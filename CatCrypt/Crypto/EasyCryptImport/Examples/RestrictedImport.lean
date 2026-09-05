/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.EasyCryptImport.FormJson
import CatCrypt.Crypto.EasyCryptImport.FormToProp
import CatCryptCore.Prob.XorBij

/-!
# Worked example: a restricted abstract module from source text to closed goals

This module takes one export — `restr.expected.json`, the output of `ec2json` on
an EasyCrypt file whose statements are quantified over an adversary carrying a
memory restriction — and carries the module, the module type and both statements
through the whole importer: JSON, AST, translation, proof.

The source the export comes from is

```
module type Adv = { proc guess(c : bool) : bool }.

module Otp = {
  var k : bool
  proc gen()  : bool = { var kk : bool; kk <$ {0,1}; k <- kk; return kk; }
  proc wipe() : bool = { k <- false; return false; }
}.

module Exp0 (A : Adv) = {
  proc main() : bool = { var kk, b, z : bool;
    kk <@ Otp.gen(); b <@ A.guess(kk ^ false); z <@ Otp.wipe(); return b; }
}.
module Exp1 (A : Adv) = { … kk ^ true … }.

section Sec.
declare module A <: Adv{-Otp}.

lemma exp_pr_eq &m :
  Pr[Exp0(A).main() @ &m : res] = Pr[Exp1(A).main() @ &m : res].
lemma exp_ll : islossless A.guess => islossless Exp0(A).main.
end section Sec.
```

`declare module` is legal only inside a section. Closing the section generalises
both lemmas over `A`, so each arrives as a formula whose outermost binder carries
the restriction, and the importer emits the restriction as a hypothesis on the
bound module: `A{-Otp}` becomes `ModuleRespectsLocs (globLocs otpModule.globals)`
and `islossless A.guess` becomes `ProcLossless (A.proc "guess")`
(`Restrictions.lean`).

## Which hypothesis carries which proof

`expPrEqGoal` is closed from the restriction. The two experiments hand the
adversary a one-time-pad encryption of `false` and of `true`, so the coupling
runs them at *different* keys in `Otp.k`; the restriction is what carries the
coupling through the adversary call, and wiping `Otp.k` afterwards turns
agreement outside the footprint back into heap equality. Both probabilities are
taken at the memory the source binds once, which is what makes the two runs start
from heaps that agree outside the footprint.

`expLosslessGoal` is closed from `ProcLossless`: sampling, heap writes and
`return` lose no mass, so the only way the experiment could is through the
adversary.

## The experiments are hand-written

`Otp` and `Adv` are decoded from the export and pinned by `#guard`. `Exp0` and
`Exp1` are functors, and the importer has no functor decoder (`AGENTS.md`), so
their bodies are written out here and supplied to the translation through
`FormEnv.functorImages`: instantiating the module binder `A` extends the
resolution environment with the two functor images the statements name.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.EasyCryptImport.RestrictedImport

open Lean (Json)
open CatCrypt.Core CatCrypt.Prob CatCrypt.Relational CatCrypt.Unary CatCrypt.Crypto
open CatCrypt.Prob.XorBij
open CatCrypt.Crypto.EasyCryptBridge
open scoped ENNReal

/-! ## The export -/

/-- The exporter's output for the restricted-adversary theory, as text. -/
private def restrExportText : String := include_str "../restr.expected.json"

/-- The exporter's output for the restricted-adversary theory. -/
private def restrExport : Json :=
  match Json.parse restrExportText with
  | .ok j => j
  | .error _ => Json.null

-- The fixture parses, it is an export of the source file it claims, and the
-- declared module the section binds is reported as section-local rather than
-- exported.
#guard (match decodeEnvelope restrExport with
        | .ok e => e.source == "tests/restr.ec" && e.root == "Top"
                     && e.sectionLocal == ["A"]
        | _ => false)

/-! ## The concrete module `Otp`

`Otp.k` is the module's one `var` declaration, so it is a heap `Location`, at the
id `decodeModule` assigns it from the base id 0. -/

/-- `Otp`'s single global `var k : bool`. -/
def kGlobal : EcGlobal := { name := "Top.Otp./k", id := 0, ty := .bool }

/-- The `Location` `Otp.k` occupies: its code is finite, so the cell its
`EcGlobal` denotes is also a finite-typed location. -/
def kLoc : Location := kGlobal.finLoc rfl

/-- The module type of `Otp`, in the order the export declares its names. -/
def otpInterface : EcInterface where
  names := ["wipe", "gen"]
  sig := fun _ => ⟨.unit, .bool⟩

/-- The imported concrete module `Otp`. `gen` samples a bit, stores it and
returns it; `wipe` writes `false` over it. -/
def otpModule : EcModule where
  name := "Otp"
  interface := otpInterface
  globals := [kGlobal]
  procs := fun p =>
    match p with
    | "gen" =>
        { params := [anonymousLocal]
          body := [.sample .bool "kk", .store kGlobal (.var .bool "kk")]
          ret := .var .bool "kk" }
    | "wipe" =>
        { params := [anonymousLocal]
          body := [.store kGlobal (.lit false)]
          ret := .lit false }
    | _ => { params := [anonymousLocal], body := [], ret := .lit default }

/-- `Otp`'s memory footprint — the image of EasyCrypt's `glob Otp`. -/
def otpLocs : LocSet := globLocs otpModule.globals

theorem otpLocs_eq : otpLocs = {kGlobal.id} := rfl

theorem kGlobal_mem_otpLocs : kLoc.id ∈ otpLocs := Finset.mem_singleton_self _

/-- Whether an expression is the `bool` literal `v`. The type index is quantified,
so this applies to the expression of an `EcStmt.store`, whose index is the stored
global's own `ty` field. -/
private def isBoolLitExpr {t : EcTy} (e : EcExpr t) (v : Bool) : Bool :=
  match t, e.litValue with
  | .bool, some w => w == v
  | _, _ => false

-- The export's module decodes to that interface and that global.
#guard (match importModule ecPrelude "Otp" restrExport with
        | .ok M =>
          M.name == "Otp" && M.interface.names == ["wipe", "gen"]
            && M.interface.sig "gen" == { arg := .unit, res := .bool }
            && M.interface.sig "wipe" == { arg := .unit, res := .bool }
            && (match M.globals with
                | [{ name := "Top.Otp./k", id := 0, ty := .bool, .. }] => true
                | _ => false)
        | _ => false)

-- `gen` decodes to the sample followed by the store of the sampled local, and
-- `wipe` to the store of `false`. The stored expressions are read back with
-- recognizers rather than matched by a pattern, because `EcStmt.store g e` types
-- `e` at `g.ty`, a projection out of its own field.
#guard (match importModule ecPrelude "Otp" restrExport with
        | .ok M =>
          (match M.procs "gen" with
           | { params := ["_"], body := [.sample .bool "kk", .store g e], ret := _ } =>
             g.name == "Top.Otp./k" && g.id == 0 && g.ty == .bool
               && e.varName == some "kk"
           | _ => false)
            && (match M.procs "wipe" with
                | { params := ["_"], body := [.store g e], ret := _ } =>
                  g.name == "Top.Otp./k" && g.id == 0 && g.ty == .bool
                    && isBoolLitExpr e false
                | _ => false)
        | _ => false)

/-- The lowered module: two `SPComp` procedures sharing the location `Otp.k`. -/
noncomputable def otpImpl : ModuleImpl otpInterface :=
  lowerModule ProcEnv.empty OpEnv.empty 0 otpModule

theorem otpImpl_gen :
    otpImpl.proc "gen" ()
      = SPComp.bind (SPComp.sample Bool)
          (fun k => SPComp.bind (SPComp.set kLoc k) (fun _ => SPComp.pure k)) := by
  show SPComp.bind
      (lowerStmts ProcEnv.empty [] 0
        [EcStmt.sample .bool "kk", EcStmt.store kGlobal (EcExpr.var .bool "kk")]
        ((emptyEnv OpEnv.empty).update anonymousLocal ⟨EcTy.unit, ()⟩))
      (fun env => SPComp.pure (evalExpr (EcExpr.var .bool "kk") env)) = _
  simp only [lowerStmts_sample, lowerStmts_store_finLoc (g := kGlobal) (hfin := rfl),
    lowerStmts_nil, sampleFin_bool, SPComp.bind_assoc, SPComp.pure_bind, evalExpr,
    Env.read_update_same]
  rfl

theorem otpImpl_wipe :
    otpImpl.proc "wipe" ()
      = SPComp.bind (SPComp.set kLoc false) (fun _ => SPComp.pure false) := by
  show SPComp.bind
      (lowerStmts ProcEnv.empty [] 0
        [EcStmt.store kGlobal (EcExpr.lit (t := .bool) false)]
        ((emptyEnv OpEnv.empty).update anonymousLocal ⟨EcTy.unit, ()⟩))
      (fun env => SPComp.pure (evalExpr (EcExpr.lit (t := .bool) false) env)) = _
  simp only [lowerStmts_store_finLoc (g := kGlobal) (hfin := rfl), lowerStmts_nil,
    SPComp.bind_assoc, SPComp.pure_bind, evalExpr]
  rfl

/-! ## The adversary interface -/

/-- The module type `Adv`: one procedure `guess : bool -> bool`. -/
def advInterface : EcInterface where
  names := ["guess"]
  sig := fun _ => ⟨.bool, .bool⟩

-- The export's module type declares that name at that signature.
#guard (match importModType ecPrelude "Adv" restrExport with
        | .ok I => I.names == ["guess"] && I.sig "guess" == { arg := .bool, res := .bool }
        | _ => false)

/-- An adversary that echoes the ciphertext it is handed and never touches the
heap, so the hypotheses of the imported statements are inhabited. -/
noncomputable def echoAdv : ModuleImpl advInterface where
  proc := fun _ c => SPComp.pure c

theorem echoAdv_respects : ModuleRespectsLocs otpLocs echoAdv :=
  fun _ => respectsLocs_of_isPure _ _ (fun c => SPComp.pure_isPure c)

theorem echoAdv_lossless : ProcLossless (echoAdv.proc "guess") :=
  fun c => lossless_pure c

/-! ## The experiments

The two functors of the source, written out: the importer has no functor decoder,
so these are the one part of the chain that does not come from the export. Each
calls `Otp` and the adversary by the cross-paths the exporter writes. -/

/-- The body of `Exp(A)` at the message bit `m`: generate the key, hand the
adversary the one-time-pad ciphertext, wipe the key, and return the adversary's
bit. -/
def expGame (m : Bool) : EcGame where
  name := "Exp"
  locals := ["kk", "b", "z"]
  body :=
    [ .callProc (xqualify "Top.Otp" "gen") ⟨.unit, .bool⟩ (.lit ()) "kk",
      .callProc (xqualify "A" "guess") ⟨.bool, .bool⟩
        (.bxor (.var .bool "kk") (.lit m)) "b",
      .callProc (xqualify "Top.Otp" "wipe") ⟨.unit, .bool⟩ (.lit ()) "z" ]
  ret := .var .bool "b"

/-- The signature of an argument-free experiment, `proc main() : bool`. -/
def mainSig : EcSig := ⟨.unit, .bool⟩

/-- The environment resolving `Otp`'s procedures. -/
noncomputable def baseEnv : ProcEnv := ProcEnv.empty.bindModuleX "Top.Otp" otpImpl

/-- The environment of the experiment: `Otp` bound concretely, the adversary bound
to the module the statement quantifies over. -/
noncomputable def expEnv (A : ModuleImpl advInterface) : ProcEnv :=
  baseEnv.bindModuleX "A" A

/-- The experiment as a family indexed by the adversary module. -/
noncomputable def expImpl (A : ModuleImpl advInterface) (m : Bool) : SPComp Bool :=
  lowerGame (expEnv A) OpEnv.empty (expGame m) 0

/-- The two functor images the statements name, keyed by the module binder they
are applied to. -/
noncomputable def expImages : String → ProcEnv → ProcEnv := fun name ρ =>
  if name = "A" then
    (ρ.bindProc "Top.Exp0(A)./main" (s := mainSig) (fun _ => lowerGame ρ OpEnv.empty (expGame false) 0)).bindProc
      "Top.Exp1(A)./main" (s := mainSig) (fun _ => lowerGame ρ OpEnv.empty (expGame true) 0)
  else ρ

/-! ## Call resolution -/

theorem expEnv_gen (A : ModuleImpl advInterface) :
    expEnv A (xqualify "Top.Otp" "gen") ⟨.unit, .bool⟩ = otpImpl.proc "gen" := rfl

theorem expEnv_wipe (A : ModuleImpl advInterface) :
    expEnv A (xqualify "Top.Otp" "wipe") ⟨.unit, .bool⟩ = otpImpl.proc "wipe" := rfl

theorem expEnv_guess (A : ModuleImpl advInterface) :
    expEnv A (xqualify "A" "guess") ⟨.bool, .bool⟩ = A.proc "guess" := rfl

/-- The lowered experiment in closed form. -/
theorem expImpl_eq (A : ModuleImpl advInterface) (m : Bool) :
    expImpl A m
      = SPComp.bind (SPComp.sample Bool) (fun k =>
          SPComp.bind (SPComp.set kLoc k) (fun _ =>
            SPComp.bind (A.proc "guess" (xor k m)) (fun b =>
              SPComp.bind (SPComp.set kLoc false) (fun _ => SPComp.pure b)))) := by
  simp only [expImpl, lowerGame, expGame, lowerStmts_callProc, lowerStmts_nil,
    expEnv_gen, expEnv_wipe, expEnv_guess, evalExpr, otpImpl_gen, otpImpl_wipe,
    EcTy.interp, SPComp.bind_assoc, SPComp.pure_bind, Env.read_update_same,
    Env.read_update_ne _ EcTy.bool "z" "b" _ (by decide)]
  rfl

/-! ## The statement tables

The signatures of `Otp`'s procedures come from the export; the two functor images
are named by the statements and supplied here, as their bodies are. The
restricting module's footprint comes from the export too, through `modGlobals`. -/

/-- The tables the two statements of the export decode against. -/
def restrTables : Except String FormTables := do
  let e ← decodeEnvelope restrExport
  let it ← findItem e "Otp"
  let S ← decodeStructure ecPrelude 0 it
  .ok (formTables (S.globals.foldl DecodeTables.withGlobal ecPrelude)
        (procSigsOfStructure S
          ++ [("Top.Exp0(A)./main", mainSig), ("Top.Exp1(A)./main", mainSig)])
        [("Top.Adv", advInterface)]
        [("Top.Otp", S.globals)])

/-- Decode the statement of the lemma `name` from the export. -/
def importedStatement (name : String) : Except String EcForm := do
  let F ← restrTables
  importAxiom F name restrExport

/-! ## The imported probability statement -/

/-- The statement of `exp_pr_eq`, as the decoder produces it. -/
def expPrEqForm : EcForm :=
  .allModRestr "A" advInterface [kGlobal]
    (.allMem "&m"
      (.probCmp .eq (EcProb.prTrueOf "Top.Exp0(A)./main" (.lit (t := .unit) ()) (.named "&m"))
        (EcProb.prTrueOf "Top.Exp1(A)./main" (.lit (t := .unit) ()) (.named "&m"))))

-- The decoder produces exactly that form: the restricted module binder, the
-- memory binder, and an equality of two `Pr[… : res]` nodes at that memory. The
-- binder's interface is matched through its declared names and the footprint
-- through the global it names, since `EcInterface` carries a function field.
#guard (match importedStatement "exp_pr_eq" with
        | .ok (.allModRestr "A" I [g]
                (.allMem "&m"
                  (.probCmp .eq
                    (.pr "Top.Exp0(A)./main" ⟨.unit, .bool⟩ (.lit ()) (.named "&m")
                       (.holds (.res .bool .cur)))
                    (.pr "Top.Exp1(A)./main" ⟨.unit, .bool⟩ (.lit ()) (.named "&m")
                       (.holds (.res .bool .cur)))))) =>
          I.names == ["guess"] && I.sig "guess" == { arg := .bool, res := .bool }
            && g.name == "Top.Otp./k" && g.id == 0 && g.ty == .bool
        | _ => false)

/-- The imported statement of `exp_pr_eq`, as a goal. -/
noncomputable def expPrEqGoal : Prop :=
  importedPropWith baseEnv expImages expPrEqForm

/-- The translated goal: for every adversary respecting `Otp`'s footprint, the two
experiments return `true` with the same probability, from every initial memory. -/
theorem expPrEqGoal_eq :
    expPrEqGoal
      = ∀ A : ModuleImpl advInterface, ModuleRespectsLocs otpLocs A →
          ∀ h : Heap, prTrue (expImpl A false) h = prTrue (expImpl A true) h := by
  show (∀ A : ModuleImpl advInterface, ModuleRespectsLocs otpLocs A →
          ∀ h : Heap, _ = _) = _
  simp only [transProb_prTrueOf]
  rfl

/-! ## The imported losslessness statement -/

/-- The statement of `exp_ll`, as the decoder produces it. -/
def expLosslessForm : EcForm :=
  .allModRestr "A" advInterface [kGlobal]
    (.imp (.lossless (xqualify "A" "guess") ⟨.bool, .bool⟩)
      (.bdHoare "Top.Exp0(A)./main" mainSig (.lit (t := .unit) ()) .tru .tru EcCmp.eq (EcRealLit.mk 1 1)))

-- The decoder produces that form: `islossless` over the abstract module's
-- procedure is the dedicated node, and over the functor image it is the bounded
-- Hoare judgement at the trivial event and the bound `1`.
#guard (match importedStatement "exp_ll" with
        | .ok (.allModRestr "A" _ [_]
                (.imp (.lossless "A./guess" ⟨.bool, .bool⟩)
                  (.bdHoare "Top.Exp0(A)./main" ⟨.unit, .bool⟩ (.lit ())
                    .tru .tru EcCmp.eq (EcRealLit.mk 1 1)))) => true
        | _ => false)

/-- The imported statement of `exp_ll`, as a goal. -/
noncomputable def expLosslessGoal : Prop :=
  importedPropWith baseEnv expImages expLosslessForm

/-- The translated goal: for every adversary respecting `Otp`'s footprint whose
`guess` is lossless, the experiment terminates with probability one from every
initial memory. -/
theorem expLosslessGoal_eq :
    expLosslessGoal
      = ∀ A : ModuleImpl advInterface, ModuleRespectsLocs otpLocs A →
          ProcLossless (A.proc "guess") →
          ∀ h : Heap, True →
            prEventComp (expImpl A false) h (fun _ _ => True) = (1 : ℕ) :=
  rfl

/-! ## The proofs -/

/-- **The coupling the restriction carries.** The fresh uniform key masks the
message, so `xor`-by-`(m₀ ^ m₁)` couples the two runs and the adversary sees the
same ciphertext on both sides. The restriction hypothesis is what carries the
coupling through the adversary call, which the two runs reach with different keys
in `Otp.k`, and wiping the key afterwards turns agreement outside the footprint
into heap equality. -/
theorem expImpl_coupling (A : ModuleImpl advInterface)
    (hA : ModuleRespectsLocs otpLocs A) (m₀ m₁ : Bool) :
    pRHL (agreeOff otpLocs) (expImpl A m₀) (expImpl A m₁) eqPost := by
  rw [expImpl_eq, expImpl_eq]
  apply rHoare_bij_step (boolXorBij (xor m₀ m₁))
  intro k
  have hc : xor ((boolXorBij (xor m₀ m₁)) k) m₁ = xor k m₀ := by
    cases k <;> cases m₀ <;> cases m₁ <;> simp [boolXorBij_apply]
  rw [hc]
  refine rHoare_set_step (Φ' := agreeOff otpLocs) kLoc k _ (fun h₁ h₂ hpre => ?_) ?_
  · exact agreeOff_set otpLocs kLoc kGlobal_mem_otpLocs hpre _ _
  · refine rHoare_bind (hA "guess" (xor k m₀)) (fun b₁ b₂ => ?_)
    refine rHoare_set_step (Φ' := fun h₁ h₂ => b₁ = b₂ ∧ h₁ = h₂) kLoc false false
      (fun h₁ h₂ hpre => ⟨hpre.1, heap_eq_of_agreeOff_singleton kLoc hpre.2 false⟩) ?_
    exact rHoare_ret (fun _ _ hh => ⟨hh.1, hh.2⟩)

/-- **The imported probability statement, closed.** Both probabilities are taken
at the same memory, which satisfies the coupling's precondition, and a coupling at
`eqPost` makes the two output distributions equal. -/
theorem expPrEqGoal_holds : expPrEqGoal := by
  rw [expPrEqGoal_eq]
  intro A hA h
  have hd : expImpl A false h = expImpl A true h :=
    liftR_eq_implies_eq
      (liftR_mono (fun _ _ hp => Prod.ext hp.1 hp.2)
        (expImpl_coupling A hA false true h h (agreeOff_refl otpLocs h)))
  simp only [prTrue, hd]

/-- **The imported losslessness statement, closed.** Sampling, heap writes and
`return` lose no mass, so the adversary's `islossless` hypothesis is what makes
the experiment lossless. -/
theorem expLosslessGoal_holds : expLosslessGoal := by
  rw [expLosslessGoal_eq]
  intro A _ hA h _
  rw [Nat.cast_one, prEventComp_true, expImpl_eq]
  refine lossless_bind (lossless_sample (α := Bool)) (fun k => ?_) h
  refine lossless_bind (lossless_set kLoc k) (fun _ => ?_)
  refine lossless_bind (hA _) (fun b => ?_)
  exact lossless_bind (lossless_set kLoc false) (fun _ => lossless_pure b)

end CatCrypt.Crypto.EasyCryptImport.RestrictedImport

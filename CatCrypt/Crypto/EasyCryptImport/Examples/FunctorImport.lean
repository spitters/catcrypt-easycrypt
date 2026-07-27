/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.EasyCryptImport.FormJson
import CatCrypt.Crypto.EasyCryptImport.FormToProp

/-!
# Worked example: two functors and their application to an abstract module

This module takes one export — `functor.expected.json`, the output of `ec2json`
on an EasyCrypt file declaring two functors over one module type — and carries
the module type, the concrete module, both functors and the statement through the
whole importer: JSON, AST, translation, proof.

The source the export comes from is

```
module type Adv = { proc guess(c : bool) : bool }.

module Otp = {
  var k : bool
  proc gen()  : bool = { var kk : bool; kk <$ {0,1}; k <- kk; return kk; }
  proc wipe() : bool = { k <- false; return false; }
}.

module Neg (P : Adv) = {
  proc guess(c : bool) : bool = { var b : bool; b <@ P.guess(c); return !b; }
}.

module Exp (Q : Adv) = {
  proc main() : bool = { var kk, b, z : bool;
    kk <@ Otp.gen(); b <@ Q.guess(kk); z <@ Otp.wipe(); return b; }
}.

section Sec.
declare module A <: Adv{-Otp}.
lemma exp_neg_ll : islossless A.guess => islossless Exp(Neg(A)).main.
end section Sec.
```

`Neg` is a functor from `Adv` to `Adv` and `Exp` is a functor from `Adv` to an
experiment, so `Exp(Neg(A))` applies one functor to the image of the other at the
module the section declares. Each functor arrives as an `EcFunctor`: the
parameter's source name is the prefix its body calls by, and the parameter's
interface comes from the module type the export carries at the parameter.

## Where the module binder goes

Closing the section generalises the lemma over `A`, so the statement arrives with
`A` as its outermost binder and the restriction `A{-Otp}` on it. Translating that
binder puts `A` into the resolution environment under its cross-paths, and the
functor image the statement names — `Top.Exp(Top.Neg(A))./main` — is supplied
through `FormEnv.functorImages`: it is the two functors applied, in order, to the
module the environment now offers under `A` (`ProcEnv.moduleX`).

## Which hypothesis carries the proof

`expNegLlGoal` is closed from `ProcLossless`: sampling, the two heap writes, the
negation and `return` lose no mass, so the only way the experiment could is
through the abstract module. The restriction `A{-Otp}` is not needed for it, and
is carried as an unused hypothesis rather than dropped. `negImpl_respects` is
what the restriction gives: the inner functor image inherits `A`'s footprint
discipline, which is the hypothesis a coupling through `Exp(Neg(A))` would
consume.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.EasyCryptImport.FunctorImport

open Lean (Json)
open CatCrypt.Core CatCrypt.Prob CatCrypt.Relational CatCrypt.Unary CatCrypt.Crypto
open CatCrypt.Crypto.EasyCryptBridge
open scoped ENNReal

/-! ## The export -/

/-- The exporter's output for the two-functor theory, as text. -/
private def functorExportText : String := include_str "../functor.expected.json"

/-- The exporter's output for the two-functor theory. -/
private def functorExport : Json :=
  match Json.parse functorExportText with
  | .ok j => j
  | .error _ => Json.null

-- The fixture parses, it is an export of the source file it claims, and the
-- declared module the section binds is reported as section-local rather than
-- exported.
#guard (match decodeEnvelope functorExport with
        | .ok e => e.source == "tests/functor.ec" && e.root == "Top"
                     && e.sectionLocal == ["A"]
        | _ => false)

/-! ## The concrete module `Otp` -/

/-- `Otp`'s single global `var k : bool`, at the id `decodeModule` assigns it from
the base id 0. -/
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
        { param := anonymousLocal
          body := [.sample .bool "kk", .store kGlobal (.var .bool "kk")]
          ret := .var .bool "kk" }
    | "wipe" =>
        { param := anonymousLocal
          body := [.store kGlobal (.lit false)]
          ret := .lit false }
    | _ => { param := anonymousLocal, body := [], ret := .lit default }

/-- `Otp`'s memory footprint — the image of EasyCrypt's `glob Otp`. -/
def otpLocs : LocSet := globLocs otpModule.globals

theorem kGlobal_mem_otpLocs : kLoc.id ∈ otpLocs := Finset.mem_singleton_self _

/-- Whether an expression is the `bool` literal `v`. The type index is quantified,
so this applies to the expression of an `EcStmt.store`, whose index is the stored
global's own `ty` field. -/
private def isBoolLitExpr {t : EcTy} (e : EcExpr t) (v : Bool) : Bool :=
  match t, e.litValue with
  | .bool, some w => w == v
  | _, _ => false

/-- Whether an expression is the negation of a read of the variable `x`. The type
index is quantified for the reason `isBoolLitExpr` gives. -/
private def isNotOfVar {t : EcTy} (e : EcExpr t) (x : String) : Bool :=
  match t, e with
  | .bool, .bnot b => b.varName == some x
  | _, _ => false

-- The export's module decodes to that interface, that global and those bodies.
#guard (match importModule ecPrelude "Otp" functorExport with
        | .ok M =>
          M.name == "Otp" && M.interface.names == ["wipe", "gen"]
            && M.interface.sig "gen" == { arg := .unit, res := .bool }
            && M.interface.sig "wipe" == { arg := .unit, res := .bool }
            && (match M.globals with
                | [{ name := "Top.Otp./k", id := 0, ty := .bool }] => true
                | _ => false)
            && (match M.procs "gen" with
                | { param := "_", body := [.sample .bool "kk", .store g e], ret := _ } =>
                  g.name == "Top.Otp./k" && g.id == 0 && g.ty == .bool
                    && e.varName == some "kk"
                | _ => false)
            && (match M.procs "wipe" with
                | { param := "_", body := [.store g e], ret := _ } =>
                  g.name == "Top.Otp./k" && isBoolLitExpr e false
                | _ => false)
        | _ => false)

/-- The lowered module: two `SPComp` procedures sharing the location `Otp.k`. -/
noncomputable def otpImpl : ModuleImpl otpInterface :=
  lowerModule ProcEnv.empty 0 otpModule

theorem otpImpl_gen :
    otpImpl.proc "gen" ()
      = SPComp.bind (SPComp.sample Bool)
          (fun k => SPComp.bind (SPComp.set kLoc k) (fun _ => SPComp.pure k)) := by
  show SPComp.bind
      (lowerStmts ProcEnv.empty [] 0
        [EcStmt.sample .bool "kk", EcStmt.store kGlobal (EcExpr.var .bool "kk")]
        (emptyEnv.update anonymousLocal ⟨EcTy.unit, ()⟩))
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
        (emptyEnv.update anonymousLocal ⟨EcTy.unit, ()⟩))
      (fun env => SPComp.pure (evalExpr (EcExpr.lit (t := .bool) false) env)) = _
  simp only [lowerStmts_store_finLoc (g := kGlobal) (hfin := rfl), lowerStmts_nil,
    SPComp.bind_assoc, SPComp.pure_bind, evalExpr]
  rfl

/-! ## The module type -/

/-- The module type `Adv`: one procedure `guess : bool -> bool`. -/
def advInterface : EcInterface where
  names := ["guess"]
  sig := fun _ => ⟨.bool, .bool⟩

-- The export's module type declares that name at that signature.
#guard (match importModType ecPrelude "Adv" functorExport with
        | .ok I => I.names == ["guess"] && I.sig "guess" == { arg := .bool, res := .bool }
        | _ => false)

/-! ## The functors

Each functor's parameter interface comes from the module type the export carries
at the parameter, so the two literals below are the decoder's output and not a
re-declaration of `Adv`. -/

/-- The body of `Neg(P)`: call the parameter's `guess` and negate its answer. -/
def negModule : EcModule where
  name := "Neg"
  interface := advInterface
  globals := []
  procs := fun _ =>
    { param := "c"
      body := [.callProc (xqualify "P" "guess") ⟨.bool, .bool⟩ (.var .bool "c") "b"]
      ret := .bnot (.var .bool "b") }

/-- The imported functor `Neg(P : Adv) : Adv`. -/
def negFunctor : EcFunctor where
  name := "Neg"
  paramName := "P"
  paramInterface := advInterface
  body := negModule

/-- The module type of `Exp`'s body: one argument-free experiment. -/
def expInterface : EcInterface where
  names := ["main"]
  sig := fun _ => ⟨.unit, .bool⟩

/-- The body of `Exp(Q)`: generate the key, hand the parameter the key, wipe the
key, and return the parameter's bit. -/
def expModule : EcModule where
  name := "Exp"
  interface := expInterface
  globals := []
  procs := fun _ =>
    { param := anonymousLocal
      body :=
        [ .callProc (xqualify "Top.Otp" "gen") ⟨.unit, .bool⟩ (.lit ()) "kk",
          .callProc (xqualify "Q" "guess") ⟨.bool, .bool⟩ (.var .bool "kk") "b",
          .callProc (xqualify "Top.Otp" "wipe") ⟨.unit, .bool⟩ (.lit ()) "z" ]
      ret := .var .bool "b" }

/-- The imported functor `Exp(Q : Adv)`. -/
def expFunctor : EcFunctor where
  name := "Exp"
  paramName := "Q"
  paramInterface := advInterface
  body := expModule

-- `Neg` decodes to that functor: the parameter is named `P` and ranges over the
-- interface `Adv` declares, and the body calls it by the cross-path the exporter
-- writes.
#guard (match importFunctor ecPrelude "Neg" functorExport with
        | .ok F =>
          F.name == "Neg" && F.paramName == "P"
            && F.paramInterface.names == ["guess"]
            && F.paramInterface.sig "guess" == { arg := .bool, res := .bool }
            && F.body.interface.names == ["guess"]
            && F.body.globals.isEmpty
            && (match F.body.procs "guess" with
                | { param := "c", body := [.callProc q s a "b"], ret := r } =>
                  q == "P./guess" && s == { arg := .bool, res := .bool }
                    && a.varName == some "c" && isNotOfVar r "b"
                | _ => false)
        | _ => false)

-- `Exp` decodes to the experiment: three calls, the middle one to the parameter
-- `Q` and the other two to `Otp`.
#guard (match importFunctor ecPrelude "Exp" functorExport with
        | .ok F =>
          F.name == "Exp" && F.paramName == "Q"
            && F.paramInterface.names == ["guess"]
            && F.body.interface.names == ["main"]
            && F.body.interface.sig "main" == { arg := .unit, res := .bool }
            && F.body.globals.isEmpty
            && (match F.body.procs "main" with
                | { param := "_",
                    body := [.callProc q₁ s₁ _ "kk", .callProc q₂ s₂ a₂ "b",
                             .callProc q₃ s₃ _ "z"], ret := r } =>
                  q₁ == "Top.Otp./gen" && s₁ == { arg := .unit, res := .bool }
                    && q₂ == "Q./guess" && s₂ == { arg := .bool, res := .bool }
                    && a₂.varName == some "kk"
                    && q₃ == "Top.Otp./wipe" && s₃ == { arg := .unit, res := .bool }
                    && r.varName == some "b"
                | _ => false)
        | _ => false)

/-! ## Functor application -/

/-- The environment resolving `Otp`'s procedures. -/
noncomputable def baseEnv : ProcEnv := ProcEnv.empty.bindModuleX "Top.Otp" otpImpl

/-- The environment the statement's module binder produces: `Otp` bound
concretely, and the abstract module bound under the binder's source name. -/
noncomputable def expEnv (A : ModuleImpl advInterface) : ProcEnv :=
  baseEnv.bindModuleX "A" A

/-- `Neg(A)`, the inner functor image: the functor applied to the module the
environment offers under the binder's name. -/
noncomputable def negImpl (A : ModuleImpl advInterface) : ModuleImpl advInterface :=
  lowerFunctorX (expEnv A) 0 negFunctor ((expEnv A).moduleX "A" advInterface)

/-- `Exp(Neg(A)).main`, the procedure the statement names. -/
noncomputable def expNegImpl (A : ModuleImpl advInterface) : SPComp Bool :=
  (lowerFunctorX (expEnv A) 0 expFunctor (negImpl A)).proc "main" ()

/-! ## Call resolution -/

theorem expEnv_guess (A : ModuleImpl advInterface) :
    ((expEnv A).moduleX "A" advInterface).proc "guess" = A.proc "guess" := rfl

theorem negEnv_guess (A : ModuleImpl advInterface) :
    ((expEnv A).bindModuleX "P" ((expEnv A).moduleX "A" advInterface))
        (xqualify "P" "guess") ⟨.bool, .bool⟩ = A.proc "guess" := rfl

theorem expEnv_gen (A : ModuleImpl advInterface) :
    ((expEnv A).bindModuleX "Q" (negImpl A)) (xqualify "Top.Otp" "gen") ⟨.unit, .bool⟩
      = otpImpl.proc "gen" := rfl

theorem expEnv_wipe (A : ModuleImpl advInterface) :
    ((expEnv A).bindModuleX "Q" (negImpl A)) (xqualify "Top.Otp" "wipe") ⟨.unit, .bool⟩
      = otpImpl.proc "wipe" := rfl

theorem expEnv_param (A : ModuleImpl advInterface) :
    ((expEnv A).bindModuleX "Q" (negImpl A)) (xqualify "Q" "guess") ⟨.bool, .bool⟩
      = (negImpl A).proc "guess" := rfl

/-! ## Closed forms of the two functor images -/

/-- The inner image in closed form: `Neg(A).guess` calls `A.guess` and negates. -/
theorem negImpl_guess (A : ModuleImpl advInterface) (c : Bool) :
    (negImpl A).proc "guess" c
      = SPComp.bind (A.proc "guess" c) (fun b => SPComp.pure (!b)) := by
  show SPComp.bind
      (lowerStmts ((expEnv A).bindModuleX "P" ((expEnv A).moduleX "A" advInterface)) [] 0
        [EcStmt.callProc (xqualify "P" "guess") ⟨.bool, .bool⟩ (EcExpr.var .bool "c") "b"]
        (emptyEnv.update "c" ⟨EcTy.bool, c⟩))
      (fun env => SPComp.pure (evalExpr (EcExpr.bnot (EcExpr.var .bool "b")) env)) = _
  simp only [lowerStmts_callProc, lowerStmts_nil, SPComp.bind_assoc, SPComp.pure_bind,
    negEnv_guess, evalExpr, Env.read_update_same]
  rfl

/-- The outer image in closed form: the key is sampled and stored, the inner image
answers on it, the key is wiped, and the negated answer is returned. -/
theorem expNegImpl_eq (A : ModuleImpl advInterface) :
    expNegImpl A
      = SPComp.bind (SPComp.sample Bool) (fun k =>
          SPComp.bind (SPComp.set kLoc k) (fun _ =>
            SPComp.bind (A.proc "guess" k) (fun b =>
              SPComp.bind (SPComp.set kLoc false)
                (fun _ => SPComp.pure (!b))))) := by
  show SPComp.bind
      (lowerStmts ((expEnv A).bindModuleX "Q" (negImpl A)) [] 0
        [ EcStmt.callProc (xqualify "Top.Otp" "gen") ⟨.unit, .bool⟩
            (EcExpr.lit (t := .unit) ()) "kk",
          EcStmt.callProc (xqualify "Q" "guess") ⟨.bool, .bool⟩
            (EcExpr.var .bool "kk") "b",
          EcStmt.callProc (xqualify "Top.Otp" "wipe") ⟨.unit, .bool⟩
            (EcExpr.lit (t := .unit) ()) "z" ]
        (emptyEnv.update anonymousLocal ⟨EcTy.unit, ()⟩))
      (fun env => SPComp.pure (evalExpr (EcExpr.var .bool "b") env)) = _
  simp only [lowerStmts_callProc, lowerStmts_nil, expEnv_gen, expEnv_wipe, expEnv_param,
    otpImpl_gen, otpImpl_wipe, negImpl_guess, evalExpr, EcTy.interp, SPComp.bind_assoc,
    SPComp.pure_bind, Env.read_update_same,
    Env.read_update_ne _ EcTy.bool "z" "b" _ (by decide)]

/-! ## What each hypothesis gives -/

/-- The inner functor image inherits the footprint discipline of the module it is
applied to: `Neg(A).guess` sequences a call to `A.guess` with a pure negation. -/
theorem negImpl_respects (A : ModuleImpl advInterface)
    (hA : ModuleRespectsLocs otpLocs A) :
    RespectsLocs otpLocs ((negImpl A).proc "guess") :=
  fun c => (negImpl_guess A c) ▸ (hA "guess").map (fun b : Bool => !b) c

/-- The experiment terminates whenever the abstract module does. -/
theorem expNegImpl_lossless (A : ModuleImpl advInterface)
    (hA : ProcLossless (A.proc "guess")) : isLossless (expNegImpl A) := by
  rw [expNegImpl_eq]
  refine lossless_bind (lossless_sample (α := Bool)) (fun k => ?_)
  refine lossless_bind (lossless_set kLoc k) (fun _ => ?_)
  refine lossless_bind (hA _) (fun b => ?_)
  exact lossless_bind (lossless_set kLoc false) (fun _ => lossless_pure (!b))

/-! ## The statement tables

The signatures of `Otp`'s procedures come from the export; the functor image the
statement names is supplied here, at the signature `Exp`'s body declares. -/

/-- The signature of an argument-free experiment, `proc main() : bool`. -/
def expMainSig : EcSig := ⟨.unit, .bool⟩

/-- The path the statement names the functor image by. -/
def expNegPath : String := "Top.Exp(Top.Neg(A))./main"

/-- The tables the statement of the export decodes against. -/
def functorTables : Except String FormTables := do
  let e ← decodeEnvelope functorExport
  let it ← findItem e "Otp"
  let S ← decodeStructure ecPrelude 0 it
  .ok (formTables (S.globals.foldl DecodeTables.withGlobal ecPrelude)
        (procSigsOfStructure S ++ [(expNegPath, expMainSig)])
        [("Top.Adv", advInterface)]
        [("Top.Otp", S.globals)])

/-- Decode the statement of the lemma `name` from the export. -/
def importedStatement (name : String) : Except String EcForm := do
  let F ← functorTables
  importAxiom F name functorExport

/-! ## The imported statement -/

/-- The statement of `exp_neg_ll`, as the decoder produces it. -/
def expNegLlForm : EcForm :=
  .allModRestr "A" advInterface [kGlobal]
    (.imp (.lossless (xqualify "A" "guess") ⟨.bool, .bool⟩)
      (.bdHoare expNegPath expMainSig (.lit (t := .unit) ()) .tru .tru .eq 1))

-- The decoder produces that form: `islossless` over the abstract module's
-- procedure is the dedicated node, and over the functor image it is the bounded
-- Hoare judgement at the trivial event. The bound is left open in the pattern
-- because `ℝ≥0∞` has no computable equality.
#guard (match importedStatement "exp_neg_ll" with
        | .ok (.allModRestr "A" I [g]
                (.imp (.lossless "A./guess" ⟨.bool, .bool⟩)
                  (.bdHoare "Top.Exp(Top.Neg(A))./main" ⟨.unit, .bool⟩ (.lit ())
                    .tru .tru .eq _))) =>
          I.names == ["guess"] && I.sig "guess" == { arg := .bool, res := .bool }
            && g.name == "Top.Otp./k" && g.id == 0 && g.ty == .bool
        | _ => false)

/-- The functor image the statement names, as an extension of the resolution
environment: instantiating the module binder `A` binds `Exp(Neg(A)).main` to the
two functors applied, in order, to the module the environment now offers under
`A`. -/
noncomputable def expImages : String → ProcEnv → ProcEnv := fun name ρ =>
  if name = "A" then
    ρ.bindProc expNegPath (s := expMainSig)
      (fun _ =>
        (lowerFunctorX ρ 0 expFunctor
            (lowerFunctorX ρ 0 negFunctor (ρ.moduleX "A" advInterface))).proc "main" ())
  else ρ

/-- The imported statement of `exp_neg_ll`, as a goal. -/
noncomputable def expNegLlGoal : Prop :=
  importedPropWith baseEnv expImages expNegLlForm

/-- The translated goal: for every abstract module respecting `Otp`'s footprint
whose `guess` is lossless, `Exp(Neg(A)).main` terminates with probability one from
every initial memory. -/
theorem expNegLlGoal_eq :
    expNegLlGoal
      = ∀ A : ModuleImpl advInterface, ModuleRespectsLocs otpLocs A →
          ProcLossless (A.proc "guess") →
          ∀ h : Heap, True → prEventComp (expNegImpl A) h (fun _ _ => True) = 1 :=
  rfl

/-- **The imported statement, closed.** -/
theorem expNegLlGoal_holds : expNegLlGoal := by
  rw [expNegLlGoal_eq]
  intro A _ hA h _
  rw [prEventComp_true]
  exact expNegImpl_lossless A hA h

end CatCrypt.Crypto.EasyCryptImport.FunctorImport

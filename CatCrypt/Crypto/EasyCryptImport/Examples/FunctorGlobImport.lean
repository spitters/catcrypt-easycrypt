/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.EasyCryptImport.Examples.AdversaryEquivImport

/-!
# Worked example: an `equiv` whose precondition is a functor image's footprint

This module takes one export — `globimg.expected.json`, the output of `ec2json`
on an EasyCrypt file whose statement is a relational judgement preconditioned on
`={glob F(A)}` — and carries that footprint comparison through JSON, AST,
translation and proof.

The source the export comes from is `tests/globimg.ec` in the exporter's tree:

```
module type Adv = { proc guess(c : bool) : bool }.

module Otp = { var k : bool }.

module Ret0 (A : Adv) = { proc main() : bool = {
  var b : bool; b <@ A.guess(Otp.k); return b; } }.
module Ret1 (A : Adv) = { proc main() : bool = {
  var b : bool; b <@ A.guess(Otp.k ^ false); return b; } }.

section Sec.
declare module A <: Adv{-Otp}.

lemma ret_equiv_img  : equiv[ Ret0(A).main ~ Ret1(A).main : ={glob Ret0(A)} ==> ={res} ].
lemma ret_equiv_pair : equiv[ Ret0(A).main ~ Ret1(A).main : ={glob A, glob Otp} ==> ={res} ].
end section Sec.
```

## The footprint of a functor image is a tuple

`glob Ret0(A)` is the footprint of the abstract parameter together with the
concrete globals the functor body reads. The parameter's part stays a `Fglob`,
whose module is a binder; the concrete part is expanded by the typechecker into
one equality operand per declared `var`. So `={glob Ret0(A)}` reaches the export
as an equality of two `Ftuple`s, `(glob A, Otp.k)` at each memory, rather than as
the equality of two `Fglob` reads that `={glob A}` is
(`Examples/AdversaryEquivImport.lean`).

The decoder compares the tuples componentwise, each component by the decoder its
own shape already has, and takes the conjunction in the tuple's order. That is
the form `={glob A, glob Otp}` produces, which is why `ret_equiv_pair` is in the
source: `isRetEquivShape` holds of both statements, so the two source spellings
of the precondition have one image.

## The two components carry different parts of the proof

`Ret1` hands the adversary `Otp.k` masked by `false`, so relating the two
experiments needs both components. `Otp.k{1} = Otp.k{2}` is what makes the two
calls receive the same argument, and `agreeOn L` — agreement on the footprint the
adversary lives on — is what `ModuleRespectsOn L A` consumes to make the two
answers agree. Dropping either leaves the postcondition `={res}` unreachable.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.EasyCryptImport.FunctorGlobImport

open Lean (Json)
open CatCrypt.Core CatCrypt.Prob CatCrypt.Relational CatCrypt.Unary CatCrypt.Crypto
open CatCrypt.Crypto.EasyCryptBridge
open CatCrypt.Crypto.EasyCryptImport.RestrictedImport
open CatCrypt.Crypto.EasyCryptImport.AdversaryEquivImport
open scoped ENNReal

/-! ## The export -/

/-- The exporter's output for the functor-image-footprint theory, as text. -/
private def globImgExportText : String := include_str "../globimg.expected.json"

/-- The exporter's output for the functor-image-footprint theory. -/
private def globImgExport : Json :=
  match Json.parse globImgExportText with
  | .ok j => j
  | .error _ => Json.null

-- The fixture parses, it is an export of the source file it claims, and the
-- declared module the section binds is reported as section-local.
#guard (match decodeEnvelope globImgExport with
        | .ok e => e.source == "tests/globimg.ec" && e.root == "Top"
                     && e.sectionLocal == ["A"]
        | _ => false)

/-! ## The statement tables

`Otp` declares one `var` and no procedure, so the export supplies the global the
expanded component of the footprint reads and the footprint the restriction is
stated against. The two functor images are named by the statements and supplied
here, as their bodies are. -/

/-- The tables the two statements of the export decode against. -/
def globImgTables : Except String FormTables := do
  let e ← decodeEnvelope globImgExport
  let it ← findItem e "Otp"
  let S ← decodeStructure ecPrelude 0 it
  .ok (formTables (S.globals.foldl DecodeTables.withGlobal ecPrelude)
        [("Top.Ret0(A)./main", mainSig), ("Top.Ret1(A)./main", mainSig)]
        [("Top.Adv", advInterface)]
        [("Top.Otp", S.globals)])

-- The export's module contributes exactly the global the footprint's expanded
-- component names.
#guard (match do
          let e ← decodeEnvelope globImgExport
          let it ← findItem e "Otp"
          decodeStructure ecPrelude 0 it with
        | .ok S =>
          (match S.globals with
           | [{ name := "Top.Otp./k", id := 0, ty := .bool, .. }] => true
           | _ => false)
            && S.procs.isEmpty
        | _ => false)

/-- Decode the statement of the lemma `name` from the export. -/
def importedStatement (name : String) : Except String EcForm := do
  let F ← globImgTables
  importAxiom F name globImgExport

/-! ## The imported relational statement -/

/-- The statement of `ret_equiv_img`, as the decoder produces it. -/
def retEquivForm : EcForm :=
  .allModRestrOn "A" advInterface [kGlobal]
    (.equiv "Top.Ret0(A)./main" mainSig (.lit (t := .unit) ())
            "Top.Ret1(A)./main" mainSig (.lit (t := .unit) ())
      (.and (.memEqOnMod "A" (.side .left) (.side .right))
        (.eqT (.glob kGlobal (.side .left)) (.glob kGlobal (.side .right))))
      (.eqT (.res .bool .left) (.res .bool .right)))

/-- Whether a decoded statement is the shape both spellings of the precondition
produce: the module binder carrying the restriction and the footprint, and a
relational judgement whose precondition is agreement on the binder's footprint
conjoined with equality of `Otp.k`, and whose postcondition is equality of
results.

The two operands of the inner equality are read back with `isGlobReadAt` rather
than matched by a pattern, because `EcTerm.glob g m` is indexed by `g.ty`
(`AGENTS.md`); the global's name, id, type and memory are all pinned by it. -/
def isRetEquivShape (f : EcForm) : Bool :=
  match f with
  | .allModRestrOn "A" I [g]
      (.equiv "Top.Ret0(A)./main" ⟨.unit, .bool⟩ _
              "Top.Ret1(A)./main" ⟨.unit, .bool⟩ _
        (.and (.memEqOnMod "A" (.side .left) (.side .right)) (.eqT a₁ a₂))
        (.eqT (.res .bool .left) (.res .bool .right))) =>
    I.names == ["guess"] && I.sig "guess" == { arg := .bool, res := .bool }
      && g.name == "Top.Otp./k" && g.id == 0 && g.ty == .bool
      && isGlobReadAt a₁ "Top.Otp./k" 0 (.side .left)
      && isGlobReadAt a₂ "Top.Otp./k" 0 (.side .right)
  | _ => false

-- The tuple of footprints decodes to that shape.
#guard (match importedStatement "ret_equiv_img" with
        | .ok f => isRetEquivShape f
        | _ => false)

-- So does the two-conjunct source form, which is what says the two spellings of
-- the precondition have one image.
#guard (match importedStatement "ret_equiv_pair" with
        | .ok f => isRetEquivShape f
        | _ => false)

-- The literal above is that shape too.
#guard isRetEquivShape retEquivForm

/-! ## The experiments

The two functors of the source, written out: the importer has no functor decoder
(`AGENTS.md`), so these are the one part of the chain that does not come from the
export. An EasyCrypt expression may read a global directly and an `EcExpr` may
not, so `A.guess(Otp.k)` is transcribed as a read of the global into a local
followed by the call. -/

/-- The body of `Ret0(A)`: read `Otp.k` and hand it to the adversary. -/
def ret0Game : EcGame where
  name := "Ret0"
  locals := ["k", "b"]
  body :=
    [ .load kGlobal "k",
      .callProc (xqualify "A" "guess") ⟨.bool, .bool⟩ (.var .bool "k") "b" ]
  ret := .var .bool "b"

/-- The body of `Ret1(A)`: read `Otp.k` and hand it to the adversary masked by
`false`. -/
def ret1Game : EcGame where
  name := "Ret1"
  locals := ["k", "b"]
  body :=
    [ .load kGlobal "k",
      .callProc (xqualify "A" "guess") ⟨.bool, .bool⟩
        (.bxor (.var .bool "k") (.lit false)) "b" ]
  ret := .var .bool "b"

/-- The environment of the experiments: `Otp` declares no procedure, so the only
binding is the adversary the statement quantifies over. -/
noncomputable def retEnv (A : ModuleImpl advInterface) : ProcEnv :=
  ProcEnv.empty.bindModuleX "A" A

theorem retEnv_guess (A : ModuleImpl advInterface) :
    retEnv A (xqualify "A" "guess") ⟨.bool, .bool⟩ = A.proc "guess" := rfl

/-- `Ret0(A)` as a family indexed by the adversary module. -/
noncomputable def ret0Impl (A : ModuleImpl advInterface) : SPComp Bool :=
  lowerGame (retEnv A) OpEnv.empty ret0Game 0

/-- `Ret1(A)` as a family indexed by the adversary module. -/
noncomputable def ret1Impl (A : ModuleImpl advInterface) : SPComp Bool :=
  lowerGame (retEnv A) OpEnv.empty ret1Game 0

/-- The two functor images the statements name, keyed by the module binder they
are applied to. -/
noncomputable def retImages : String → ProcEnv → ProcEnv := fun name ρ =>
  if name = "A" then
    (ρ.bindProc "Top.Ret0(A)./main" (s := mainSig)
        (fun _ => lowerGame ρ OpEnv.empty ret0Game 0)).bindProc
      "Top.Ret1(A)./main" (s := mainSig) (fun _ => lowerGame ρ OpEnv.empty ret1Game 0)
  else ρ

/-- The lowered `Ret0(A)` in closed form. -/
theorem ret0Impl_eq (A : ModuleImpl advInterface) :
    ret0Impl A
      = SPComp.bind (SPComp.get kLoc)
          (fun k => SPComp.bind (A.proc "guess" k) (fun b => SPComp.pure b)) := by
  simp only [ret0Impl, lowerGame, ret0Game,
    lowerStmts_load_finLoc (g := kGlobal) (hfin := rfl), lowerStmts_callProc,
    lowerStmts_nil, retEnv_guess, evalExpr, EcTy.interp, SPComp.bind_assoc,
    SPComp.pure_bind, Env.read_update_same]
  rfl

/-- The lowered `Ret1(A)` in closed form: the adversary is called at the masked
key. -/
theorem ret1Impl_eq (A : ModuleImpl advInterface) :
    ret1Impl A
      = SPComp.bind (SPComp.get kLoc)
          (fun k => SPComp.bind (A.proc "guess" (xor k false))
            (fun b => SPComp.pure b)) := by
  simp only [ret1Impl, lowerGame, ret1Game,
    lowerStmts_load_finLoc (g := kGlobal) (hfin := rfl), lowerStmts_callProc,
    lowerStmts_nil, retEnv_guess, evalExpr, EcTy.interp, SPComp.bind_assoc,
    SPComp.pure_bind, Env.read_update_same]
  rfl

/-! ## The translated goal -/

/-- The imported statement of `ret_equiv_img`, as a goal. -/
noncomputable def retEquivGoal : Prop :=
  importedPropWith ProcEnv.empty retImages retEquivForm

/-- Reading `Otp.k` at a memory, in the finite-typed vocabulary. -/
private theorem gget_kGlobal (h : Heap) : h.gget kGlobal.loc = h.get kLoc :=
  Heap.gget_ofLocation h kLoc

/-- The translated goal: for every adversary and every footprint it lives on
disjoint from `Otp`'s, the two experiments are related by the coupling whose
precondition is agreement on that footprint together with equality of `Otp.k`,
and whose postcondition is equality of results. -/
theorem retEquivGoal_eq :
    retEquivGoal
      = ∀ (A : ModuleImpl advInterface) (L : LocSet), Disjoint L otpLocs →
          ModuleRespectsOn L A → ModuleRespectsLocs otpLocs A →
            pRHL (fun h₁ h₂ => agreeOn L h₁ h₂ ∧ h₁.get kLoc = h₂.get kLoc)
              (ret0Impl A) (ret1Impl A) (fun r₁ _ r₂ _ => r₁ = r₂) := by
  show (∀ (A : ModuleImpl advInterface) (L : LocSet), Disjoint L otpLocs →
          ModuleRespectsOn L A → ModuleRespectsLocs otpLocs A →
            pRHL (fun h₁ h₂ => agreeOn L h₁ h₂
                    ∧ h₁.gget kGlobal.loc = h₂.gget kGlobal.loc)
              (ret0Impl A) (ret1Impl A) (fun r₁ _ r₂ _ => r₁ = r₂)) = _
  simp only [gget_kGlobal]
  rfl

/-! ## The hypotheses are satisfiable

The echoing adversary of `RestrictedImport.lean` touches no location, so it lives
on the empty footprint, which is disjoint from `Otp`'s
(`AdversaryEquivImport.echoAdv_respectsOn`,
`AdversaryEquivImport.echoAdv_footprint_disjoint`). -/

theorem echoAdv_hypotheses :
    Disjoint (∅ : LocSet) otpLocs ∧ ModuleRespectsOn ∅ echoAdv
      ∧ ModuleRespectsLocs otpLocs echoAdv :=
  ⟨echoAdv_footprint_disjoint, echoAdv_respectsOn ∅, echoAdv_respects⟩

/-! ## The proof -/

/-- **The coupling the two components of the footprint carry.** Equality of
`Otp.k` makes the two reads return the same bit, and masking it by `false` leaves
the adversary called at the same argument on both sides; agreement on the
adversary's own footprint is then what `ModuleRespectsOn` consumes to make its two
answers agree. Neither call writes a location, so the precondition survives to the
`return`. -/
theorem retEquivCoupling (A : ModuleImpl advInterface) (L : LocSet)
    (hA : ModuleRespectsOn L A) :
    pRHL (fun h₁ h₂ => agreeOn L h₁ h₂ ∧ h₁.get kLoc = h₂.get kLoc)
      (ret0Impl A) (ret1Impl A) (fun r₁ _ r₂ _ => r₁ = r₂) := by
  rw [ret0Impl_eq, ret1Impl_eq]
  refine rHoare_bind (rHoare_get_sync kLoc (fun _ _ hpre => hpre.2)) (fun k₁ k₂ => ?_)
  refine rHoare_bind (Ψ := fun r₁ h₁ r₂ h₂ => r₁ = r₂ ∧ agreeOn L h₁ h₂) ?_
    (fun _ _ => rHoare_ret (fun _ _ hb => hb.1))
  intro h₁ h₂ hpre
  obtain ⟨⟨hon, _⟩, hk⟩ := hpre
  have hmask : xor k₂ false = k₁ := by simp [hk.symm]
  rw [hmask]
  exact hA "guess" k₁ h₁ h₂ hon

/-- **The imported relational statement, closed.** -/
theorem retEquivGoal_holds : retEquivGoal := by
  rw [retEquivGoal_eq]
  intro A L _ hA _
  exact retEquivCoupling A L hA

end CatCrypt.Crypto.EasyCryptImport.FunctorGlobImport

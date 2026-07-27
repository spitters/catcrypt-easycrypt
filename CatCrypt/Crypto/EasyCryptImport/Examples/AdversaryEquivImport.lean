/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.EasyCryptImport.Examples.RestrictedImport

/-!
# Worked example: an `equiv` whose precondition is an adversary's footprint

This module takes one export — `advequiv.expected.json`, the output of `ec2json`
on an EasyCrypt file whose statements are relational judgements between two
adversary-using experiments — and carries the statement `={glob A}` names through
JSON, AST, translation and proof.

The source the export comes from is `tests/advequiv.ec` in the exporter's tree.
Its module `Otp`, its module type `Adv` and its two functors are those of
`RestrictedImport.lean`, and this module reuses that file's decoded module,
lowered experiments and functor images. What it adds are the three statements

```
section Sec.
declare module A <: Adv{-Otp}.

lemma exp_equiv      : equiv[ Exp0(A).main ~ Exp1(A).main : ={glob A} ==> ={res} ].
lemma exp_equiv_otp  : equiv[ Exp0(A).main ~ Exp1(A).main : ={glob Otp} ==> ={res} ].
lemma exp_equiv_both : equiv[ Exp0(A).main ~ Exp1(A).main : ={glob A, glob Otp} ==> ={res} ].
end section Sec.
```

## The two shapes a footprint comparison arrives in

EasyCrypt's `Fglob` node carries a module *identifier*, so its module is a
binder: `={glob A}` for the section-declared `A` reaches the export as an
equality of two `Fglob` reads, and decodes to `EcForm.memEqOnMod`, agreement on
the footprint the binder carries. `={glob Otp}` for the concrete module never
reaches an `Fglob`: the typechecker expands it into one equality per declared
`var`, so it decodes to an `EcForm.eqT` between two global reads.
`={glob A, glob Otp}` is the conjunction of the two.

## The footprint is a second bound variable

An abstract module declares no globals, so there is no list of globals for
`={glob A}` to range over. The set of locations `A` reads and writes is therefore
bound alongside `A` itself, and the module quantifier of a statement that names
`glob A` is `EcForm.allModRestrOn`: it quantifies a module `M` and a footprint
`L`, under the hypotheses that `L` is disjoint from `Otp`'s footprint, that `M`
lives on `L` (`ModuleRespectsOn`), and that `M` respects `Otp`'s footprint
(`ModuleRespectsLocs`, the hypothesis `A{-Otp}` already emitted). The
precondition `={glob A}` is `agreeOn L`, which two memories differing on `Otp.k`
still satisfy.

`ModuleRespectsOn L A` is what carries the coupling through the adversary call:
the two runs reach it with different keys in `Otp.k`, and `L` is disjoint from
`Otp`'s footprint, so the two memories agree on everything `A` can see.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.EasyCryptImport.AdversaryEquivImport

open Lean (Json)
open CatCrypt.Core CatCrypt.Prob CatCrypt.Relational CatCrypt.Unary CatCrypt.Crypto
open CatCrypt.Prob.XorBij
open CatCrypt.Crypto.EasyCryptBridge
open CatCrypt.Crypto.EasyCryptImport.RestrictedImport
open scoped ENNReal

/-! ## The export -/

/-- The exporter's output for the adversary-equivalence theory, as text. -/
private def advEquivExportText : String := include_str "../advequiv.expected.json"

/-- The exporter's output for the adversary-equivalence theory. -/
private def advEquivExport : Json :=
  match Json.parse advEquivExportText with
  | .ok j => j
  | .error _ => Json.null

-- The fixture parses, it is an export of the source file it claims, and the
-- declared module the section binds is reported as section-local.
#guard (match decodeEnvelope advEquivExport with
        | .ok e => e.source == "tests/advequiv.ec" && e.root == "Top"
                     && e.sectionLocal == ["A"]
        | _ => false)

/-! ## The statement tables

`Otp`'s procedure signatures and its `var` declarations come from the export; the
two functor images are named by the statements and supplied here, as they are in
`RestrictedImport.lean`. -/

/-- The tables the three statements of the export decode against. -/
def advEquivTables : Except String FormTables := do
  let e ← decodeEnvelope advEquivExport
  let it ← findItem e "Otp"
  let S ← decodeStructure ecPrelude 0 it
  .ok (formTables (S.globals.foldl DecodeTables.withGlobal ecPrelude)
        (procSigsOfStructure S
          ++ [("Top.Exp0(A)./main", mainSig), ("Top.Exp1(A)./main", mainSig)])
        [("Top.Adv", advInterface)]
        [("Top.Otp", S.globals)])

/-- Decode the statement of the lemma `name` from the export. -/
def importedStatement (name : String) : Except String EcForm := do
  let F ← advEquivTables
  importAxiom F name advEquivExport

/-! ## The imported relational statement -/

/-- The statement of `exp_equiv`, as the decoder produces it. -/
def advEquivForm : EcForm :=
  .allModRestrOn "A" advInterface [kGlobal]
    (.equiv "Top.Exp0(A)./main" mainSig (.lit (t := .unit) ())
            "Top.Exp1(A)./main" mainSig (.lit (t := .unit) ())
      (.memEqOnMod "A" (.side .left) (.side .right))
      (.eqT (.res .bool .left) (.res .bool .right)))

-- The decoder produces exactly that form: the module binder carrying both the
-- restriction and the footprint, and a relational judgement whose precondition is
-- agreement on that footprint and whose postcondition is equality of results.
#guard (match importedStatement "exp_equiv" with
        | .ok (.allModRestrOn "A" I [g]
                (.equiv "Top.Exp0(A)./main" ⟨.unit, .bool⟩ _
                        "Top.Exp1(A)./main" ⟨.unit, .bool⟩ _
                  (.memEqOnMod "A" (.side .left) (.side .right))
                  (.eqT (.res .bool .left) (.res .bool .right)))) =>
          I.names == ["guess"] && I.sig "guess" == { arg := .bool, res := .bool }
            && g.name == "Top.Otp./k" && g.id == 0 && g.ty == .bool
        | _ => false)

-- `={glob Otp}` for the concrete module is expanded before the export, so the
-- precondition is a term equality and the binder carries no footprint.
#guard (match importedStatement "exp_equiv_otp" with
        | .ok (.allModRestr "A" _ [_]
                (.equiv "Top.Exp0(A)./main" _ _ "Top.Exp1(A)./main" _ _
                  (.eqT _ _) (.eqT _ _))) => true
        | _ => false)

-- `={glob A, glob Otp}` is the conjunction of the two shapes, and the binder
-- carries the footprint because one conjunct names it.
#guard (match importedStatement "exp_equiv_both" with
        | .ok (.allModRestrOn "A" _ [_]
                (.equiv "Top.Exp0(A)./main" _ _ "Top.Exp1(A)./main" _ _
                  (.and (.memEqOnMod "A" (.side .left) (.side .right)) (.eqT _ _))
                  (.eqT _ _))) => true
        | _ => false)

/-- The imported statement of `exp_equiv`, as a goal. -/
noncomputable def advEquivGoal : Prop :=
  importedPropWith baseEnv expImages advEquivForm

/-- The translated goal: for every adversary and every footprint it lives on
disjoint from `Otp`'s, the two experiments are related by the coupling whose
precondition is agreement on that footprint and whose postcondition is equality
of results. -/
theorem advEquivGoal_eq :
    advEquivGoal
      = ∀ (A : ModuleImpl advInterface) (L : LocSet), Disjoint L otpLocs →
          ModuleRespectsOn L A → ModuleRespectsLocs otpLocs A →
            pRHL (agreeOn L) (expImpl A false) (expImpl A true)
              (fun r₁ _ r₂ _ => r₁ = r₂) := rfl

/-! ## The hypotheses are satisfiable

The echoing adversary of `RestrictedImport.lean` touches no location, so it lives
on the empty footprint, which is disjoint from `Otp`'s. -/

theorem echoAdv_respectsOn (L : LocSet) : ModuleRespectsOn L echoAdv :=
  fun _ => respectsOn_of_isPure _ _ (fun c => SPComp.pure_isPure c)

theorem echoAdv_footprint_disjoint : Disjoint (∅ : LocSet) otpLocs :=
  disjoint_bot_left

/-! ## The precondition

The imported precondition is agreement on the adversary's footprint. Agreement
outside `Otp`'s footprint implies it, so the coupling above holds under that
stronger precondition too. -/

theorem agreeOn_of_agreeOff_otpLocs {L : LocSet} (hdisj : Disjoint L otpLocs)
    {h₁ h₂ : Heap} (h : agreeOff otpLocs h₁ h₂) : agreeOn L h₁ h₂ :=
  agreeOn_of_agreeOff hdisj h

/-! ## The footprint of a module whose globals are known

`EcForm.memEqOn` is the footprint comparison stated against a list of declared
globals, the shape a module named in a `Fglob` node would take when the export
knows its `var` declarations. Its translation is agreement on the footprint those
globals occupy. -/

/-- `={glob Otp}` written against `Otp`'s declared globals. -/
def otpMemEqOnForm : EcForm := .memEqOn [kGlobal] (.side .left) (.side .right)

theorem otpMemEqOnForm_trans (ρ : FormEnv) :
    transForm otpMemEqOnForm ρ = agreeOn otpLocs ρ.memLeft ρ.memRight := rfl

/-! ## The proof -/

/-- **The coupling the footprint hypothesis carries.** The fresh uniform key masks
the message, so `xor`-by-`(m₀ ^ m₁)` couples the two runs and the adversary sees
the same ciphertext on both sides. `Otp.k` lies outside the adversary's footprint,
so writing the two different keys preserves agreement on it, and
`ModuleRespectsOn` then carries the coupling through the adversary call. -/
theorem advEquivCoupling (A : ModuleImpl advInterface) (L : LocSet)
    (hdisj : Disjoint L otpLocs) (hA : ModuleRespectsOn L A) (m₀ m₁ : Bool) :
    pRHL (agreeOn L) (expImpl A m₀) (expImpl A m₁) (fun r₁ _ r₂ _ => r₁ = r₂) := by
  have hk : kLoc.id ∉ L := fun hmem =>
    Finset.disjoint_left.mp hdisj hmem kGlobal_mem_otpLocs
  rw [expImpl_eq, expImpl_eq]
  apply rHoare_bij_step (boolXorBij (xor m₀ m₁))
  intro k
  have hc : xor ((boolXorBij (xor m₀ m₁)) k) m₁ = xor k m₀ := by
    cases k <;> cases m₀ <;> cases m₁ <;> simp [boolXorBij_apply]
  rw [hc]
  refine rHoare_set_step (Φ' := agreeOn L) kLoc k _ (fun h₁ h₂ hpre => ?_) ?_
  · exact agreeOn_set_of_not_mem L kLoc hk hpre _ _
  · refine rHoare_bind (hA "guess" (xor k m₀)) (fun b₁ b₂ => ?_)
    refine rHoare_set_step (Φ' := fun _ _ => b₁ = b₂) kLoc false false
      (fun _ _ hpre => hpre.1) ?_
    exact rHoare_ret (fun _ _ hh => hh)

/-- **The imported relational statement, closed.** -/
theorem advEquivGoal_holds : advEquivGoal := by
  rw [advEquivGoal_eq]
  intro A L hdisj hA _
  exact advEquivCoupling A L hdisj hA false true

end CatCrypt.Crypto.EasyCryptImport.AdversaryEquivImport

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.EasyCryptImport.FormToProp

/-!
# An imported statement over an abstract operator

EasyCrypt's `theories/crypto/PRF.eca` declares, in its inner theory `PseudoRF`:

```
type K.
op dK : K distr.
axiom dK_ll : is_lossless dK.
```

`K` is an abstract type, `dK` an abstract distribution, and `dK_ll` a statement
about `dK`. This module exhibits what the three become here: `K` is the code
`EcTy.opaque "Top.PseudoRF.K"` at the carrier `Ty.lean` fixes, `dK` is a value
parameter at the signature its declaration gives it, and `dK_ll` is a proposition
about that parameter.

## Two readings of one item, and which one applies

`dK_ll` carries `axiom_kind: Axiom`, so in EasyCrypt it is a hypothesis every
statement of `PseudoRF` is proved under, not a claim `PseudoRF` establishes. Both
readings are here, and they are different propositions:

* `prfDKLosslessAt D` is the hypothesis at the realization `D`, which is
  `SDistr.mass D.dK = 1` (`prfDKLosslessAt_iff`). This is the field a `Laws`
  structure carries and the premise a lemma of the theory is stated under.
* `prfDKLosslessProp` is the statement closed over its parameter, which is
  `∀ dK : SDistr Int, SDistr.mass dK = 1`
  (`prfDKLosslessProp_iff`). That is the reading an `axiom_kind: Lemma` item of a
  declaring theory gets: for every realization of the operators the statement
  reads, the statement holds. It is not what the source asserts about `dK`, and it
  is refutable — `PRFData.pointMass` and `SDistr.fail` are two realizations that
  disagree on it — which is the difference between an item the theory assumes and
  an item it proves.

## The realization is exhibited, not assumed

A statement quantified over parameters under hypotheses says nothing when the
hypotheses cannot be met together, and nothing in a build detects an unsatisfiable
imported hypothesis set. `PRFData.pointMass` and `PRFData.pointMassLaws` are the
witness for this theory: a point mass on the carrier has total mass one, so
`PRFLaws` is inhabited and the imported hypothesis set of `PseudoRF` is
satisfiable.

`Ty.lean` fixes the carrier of `EcTy.opaque "Top.PseudoRF.K"` at `Carrier` on that
path, so every
proposition here is at that carrier, and the witness is a distribution on it.

The decode of the exported items — the `Th_operator` declaration and the
`Th_axiom` statement — is checked against the exporter's node shapes in
`Json.lean` and `FormJson.lean`; the literals below are the values those decoders
produce.

## Main definitions

* `prfDKLossless`: the decoded `dK_ll` statement, an `EcForm.isLossless` of an
  `opApp` at the distribution-typed nullary operator `dK`.
* `prfDKLosslessProp`: its closed reading, quantified over every realization.
* `PRFData`, `PRFLaws`, `prfDKLosslessAt`: a realization of the theory's
  operators, its imported hypotheses, and the statement at that realization.

## Main results

* `prfDKLosslessAt_iff`, `prfDKLosslessProp_iff`: each reading is the expected
  statement about `SDistr.mass`.
* `PRFData.pointMassLaws`: a realization satisfying the imported hypotheses,
  which is what rules out their vacuity.
* `not_prfDKLosslessProp`: the closed reading is refutable, so an `Axiom` item
  and a `Lemma` item cannot share it.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.EasyCryptImport.Examples.PRFParamImport

open CatCrypt.Core CatCrypt.Prob
open CatCrypt.Crypto.EasyCryptImport

/-! ## The imported statement -/

/-- The body of `dK_ll`: the abstract operator `Top.PseudoRF.dK`, read at the
signature its declaration gives it, asserted to have total mass one. -/
def prfDKLosslessBody : EcForm :=
  .isLossless (.opApp "Top.PseudoRF.dK" ⟨.unit, .distr (.opaque "Top.PseudoRF.K")⟩
    (.lit (t := .unit) ()))

/-- The body closed over the operator it reads. `dK` is declared with no
argument, so the binder ranges over the type its declaration gives it. -/
def prfDKLossless : EcForm :=
  .allConst "Top.PseudoRF.dK" (.distr (.opaque "Top.PseudoRF.K")) prfDKLosslessBody

-- Assembling the body produces that statement, and the assembled statement reads
-- no operator it does not bind.
#guard (match prfDKLosslessBody.assembleParams with
        | .allConst "Top.PseudoRF.dK" t (.isLossless d) =>
            t == EcTy.distr (EcTy.opaque "Top.PseudoRF.K")
              && d.opAppOf == some ("Top.PseudoRF.dK",
                   { arg := EcTy.unit,
                     res := EcTy.distr (EcTy.opaque "Top.PseudoRF.K") })
        | _ => false)

#guard EcForm.opsOf prfDKLosslessBody.assembleParams == []

/-! ## The two propositions -/

/-- The imported statement as a goal: for every realization of `dK`, the
realization has total mass one. -/
noncomputable def prfDKLosslessProp : Prop :=
  importedProp ProcEnv.empty prfDKLossless

/-- The realizations of `PseudoRF`'s abstract operators: one sub-distribution on
the carrier of `Top.PseudoRF.K`. -/
structure PRFData where
  /-- The realization of `op dK : K distr.` -/
  dK : SDistr (EcTy.opaque "Top.PseudoRF.K").interp

/-- The operator environment a realization is: `Top.PseudoRF.dK` bound to `dK` at
the signature its declaration gives it. -/
noncomputable def PRFData.toOpEnv (D : PRFData) : OpEnv :=
  OpEnv.empty.bindConst "Top.PseudoRF.dK" (.distr (.opaque "Top.PseudoRF.K")) D.dK

/-- The imported statement as a hypothesis at the realization `D`. -/
noncomputable def prfDKLosslessAt (D : PRFData) : Prop :=
  importedPropWithOps ProcEnv.empty D.toOpEnv prfDKLosslessBody

/-- The imported hypotheses of `PseudoRF` at the realization `D`: the theory's one
`axiom` item. -/
structure PRFLaws (D : PRFData) : Prop where
  /-- `axiom dK_ll : is_lossless dK.` -/
  dK_ll : prfDKLosslessAt D

/-! ## What the two propositions are -/

/-- The hypothesis at a realization is that the realization has total mass one. -/
theorem prfDKLosslessAt_iff (D : PRFData) :
    prfDKLosslessAt D ↔ SDistr.mass D.dK = 1 := by
  simp only [prfDKLosslessAt, importedPropWithOps, prfDKLosslessBody,
    transForm_isLossless, evalTerm_opApp, FormEnv.withOps_ops, PRFData.toOpEnv,
    OpEnv.bindConst, OpEnv.bindOp_same]

/-- The closed statement quantifies over the realization, at the type `dK`'s
declaration gives it. -/
theorem prfDKLosslessProp_iff :
    prfDKLosslessProp ↔ ∀ dK : SDistr (Carrier "Top.PseudoRF.K"), SDistr.mass dK = 1 := by
  simp only [prfDKLosslessProp, importedProp, prfDKLossless, prfDKLosslessBody,
    transForm_allConst, transForm_isLossless, evalTerm_opApp, FormEnv.bindConst,
    FormEnv.withOps_ops, OpEnv.bindConst, OpEnv.bindOp_same]

/-! ## The committed realization -/

/-- The realization that puts all mass on one key. -/
noncomputable def PRFData.pointMass (k : Carrier "Top.PseudoRF.K") : PRFData := ⟨SDistr.pure k⟩

/-- `PseudoRF`'s imported hypotheses hold at the point mass, so the hypothesis set
is satisfiable and a statement proved under it is not vacuous. -/
theorem PRFData.pointMassLaws (k : Carrier "Top.PseudoRF.K") : PRFLaws (PRFData.pointMass k) :=
  ⟨(prfDKLosslessAt_iff _).2 (SDistr.mass_pure k)⟩

/-- The closed reading is refutable: the failed computation is a realization of
mass zero, so quantifying `dK_ll` over every realization states something
`PseudoRF` does not. -/
theorem not_prfDKLosslessProp : ¬ prfDKLosslessProp := by
  rw [prfDKLosslessProp_iff]
  intro h
  simpa using h SDistr.fail

end CatCrypt.Crypto.EasyCryptImport.Examples.PRFParamImport

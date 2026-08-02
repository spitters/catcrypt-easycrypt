/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.EasyCryptImport.FormToProp

/-!
# An imported lemma under its theory's imported axiom

EasyCrypt's `theories/crypto/DigitalSignaturesROM.eca` declares, in its theory
`StatelessROM.UUFKOAROM`:

```
op [lossless] dmsg : msg_t distr.

clone import UUFKOA with
  op dmsg <- dmsg
proof *.
realize dmsg_ll by exact: dmsg_ll.
```

`op [lossless] dmsg` declares the operator and the axiom `dmsg_ll` constraining
it. The clone carries an axiom of the same name, and realizing it exports it as
`axiom_kind: Lemma` at `Top.StatelessROM.UUFKOAROM.UUFKOA.dmsg_ll`. The clone's
own theory declares no axiom: the statement it proves is proved from the axiom of
the theory one scope out.

## What the premises are for

Closing an imported statement over the operators it reads gives "for every
realization of the declarations, `φ`". For a lemma of a theory that is the wrong
statement: the realizations the source speaks about are the ones its theory's
axioms admit. The two readings of this corpus lemma are the two propositions
below, and they differ by exactly one premise:

* `uufkoaDmsgLosslessProp` is the lemma with the axiom of its scope as a premise,
  which is `∀ dmsg : SDistr Int, SDistr.mass dmsg = 1 → SDistr.mass dmsg = 1`
  (`uufkoaDmsgLosslessProp_iff`). It is provable, by the identity —
  `uufkoaDmsgLosslessProp_holds` — which is what `realize dmsg_ll by exact:
  dmsg_ll` is.
* `uufkoaDmsgLosslessPropNoPremise` is the same statement with the premise
  dropped, which is `∀ dmsg : SDistr Int, SDistr.mass dmsg = 1`
  (`uufkoaDmsgLosslessPropNoPremise_iff`) and is refutable
  (`not_uufkoaDmsgLosslessPropNoPremise`). Dropping the premise makes the claim
  strictly stronger than the source's, and here strong enough to be false.

## The realization is exhibited, not assumed

A statement under hypotheses says nothing when the hypotheses cannot be met, and
nothing in a build detects an unsatisfiable imported hypothesis set.
`UUFKOAData.pointMass` and `UUFKOAData.pointMassLaws` are the witness for this
theory: a point mass on the carrier has total mass one, so `UUFKOALaws` is
inhabited and the premise the lemma is stated under is satisfiable.

`Ty.lean` fixes the carrier of `EcTy.opaque "Top.msg_t"` at `Int`, so every
proposition here is at that carrier, and the witness is a distribution on it.

The decode of the exported items — the operator declaration, the `Axiom` item and
the `Lemma` item, and the scope walk that pairs them — is checked against the
exporter's node shapes in `FormJson.lean`; the literals below are the values
those decoders produce.

## Main definitions

* `uufkoaDmsgLosslessBody`: the decoded `is_lossless dmsg` statement, an
  `EcForm.isLossless` of an `opApp` at the distribution-typed nullary operator
  `dmsg`.
* `uufkoaDmsgLossless`: the assembled lemma, the body under the imported axiom of
  its scope and closed over the operator both read.
* `uufkoaDmsgLosslessNoPremise`: the body closed over that operator alone.
* `UUFKOAData`, `UUFKOALaws`, `uufkoaDmsgLosslessAt`: a realization of the
  theory's abstract operator, its imported hypotheses, and the statement at that
  realization.

## Main results

* `uufkoaDmsgLosslessProp_iff`, `uufkoaDmsgLosslessProp_holds`: the assembled
  statement is the implication, and it holds.
* `not_uufkoaDmsgLosslessPropNoPremise`: the same statement without the premise
  is refutable, so the premise is what the lemma says.
* `UUFKOAData.pointMassLaws`: a realization satisfying the premise, which is what
  rules out its vacuity.
* `uufkoaDmsgLosslessAt_of_laws`: the assembled statement, at a realization
  meeting the imported hypotheses, gives the lemma's statement there.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.EasyCryptImport.Examples.UUFKOAPremiseImport

open CatCrypt.Core CatCrypt.Prob
open CatCrypt.Crypto.EasyCryptImport

/-! ## The imported statements -/

/-- The signature `dmsg`'s declaration gives it. -/
def dmsgSig : EcSig := ⟨.unit, .distr (.opaque "Top.msg_t")⟩

/-- The body of `dmsg_ll`: the abstract operator `Top.StatelessROM.UUFKOAROM.dmsg`,
read at the signature its declaration gives it, asserted to have total mass one.
The `Axiom` item of `UUFKOAROM` and the `Lemma` item of its clone are both this
statement. -/
def uufkoaDmsgLosslessBody : EcForm :=
  .isLossless
    (.opApp "Top.StatelessROM.UUFKOAROM.dmsg" dmsgSig (.lit (t := .unit) ()))

/-- The lemma of the clone: its statement under the imported axiom of the theory
declaring `dmsg`, closed over the realization both read. -/
def uufkoaDmsgLossless : EcForm :=
  .allConst "Top.StatelessROM.UUFKOAROM.dmsg" (.distr (.opaque "Top.msg_t"))
    (.imp uufkoaDmsgLosslessBody uufkoaDmsgLosslessBody)

-- Assembling the body under that one axiom produces that statement.
#guard (match EcForm.assembleStatement [uufkoaDmsgLosslessBody]
            uufkoaDmsgLosslessBody with
        | .allConst "Top.StatelessROM.UUFKOAROM.dmsg" t
            (.imp (.isLossless h) (.isLossless g)) =>
            t == EcTy.distr (EcTy.opaque "Top.msg_t")
              && h.opAppOf == some ("Top.StatelessROM.UUFKOAROM.dmsg", dmsgSig)
              && g.opAppOf == some ("Top.StatelessROM.UUFKOAROM.dmsg", dmsgSig)
        | _ => false)

-- The assembled statement reads no operator it does not bind, premise included.
#guard EcForm.opsOf
    (EcForm.assembleStatement [uufkoaDmsgLosslessBody] uufkoaDmsgLosslessBody) == []

/-- The same statement with the premise dropped: the body closed over the
operator it reads, and nothing else. -/
def uufkoaDmsgLosslessNoPremise : EcForm :=
  .allConst "Top.StatelessROM.UUFKOAROM.dmsg" (.distr (.opaque "Top.msg_t"))
    uufkoaDmsgLosslessBody

-- Assembling the parameters alone produces that statement.
#guard (match uufkoaDmsgLosslessBody.assembleParams with
        | .allConst "Top.StatelessROM.UUFKOAROM.dmsg" t (.isLossless g) =>
            t == EcTy.distr (EcTy.opaque "Top.msg_t")
              && g.opAppOf == some ("Top.StatelessROM.UUFKOAROM.dmsg", dmsgSig)
        | _ => false)

/-! ## The two readings -/

/-- The imported lemma as a goal: for every realization of `dmsg` with total mass
one, the realization has total mass one. -/
noncomputable def uufkoaDmsgLosslessProp : Prop :=
  importedProp ProcEnv.empty uufkoaDmsgLossless

/-- The same lemma with the premise dropped: for every realization of `dmsg`, the
realization has total mass one. -/
noncomputable def uufkoaDmsgLosslessPropNoPremise : Prop :=
  importedProp ProcEnv.empty uufkoaDmsgLosslessNoPremise

/-- The assembled lemma quantifies over the realization and assumes the imported
axiom of its scope. -/
theorem uufkoaDmsgLosslessProp_iff :
    uufkoaDmsgLosslessProp
      ↔ ∀ dmsg : SDistr Int, SDistr.mass dmsg = 1 → SDistr.mass dmsg = 1 := by
  simp only [uufkoaDmsgLosslessProp, importedProp, uufkoaDmsgLossless,
    uufkoaDmsgLosslessBody, transForm_allConst, transForm_imp,
    transForm_isLossless, FormEnv.bindConst, OpEnv.bindConst]
  rfl

/-- The imported lemma holds, by the identity, which is the proof the source
gives it. -/
theorem uufkoaDmsgLosslessProp_holds : uufkoaDmsgLosslessProp :=
  uufkoaDmsgLosslessProp_iff.2 (fun _ h => h)

/-- Without the premise the statement quantifies over every realization. -/
theorem uufkoaDmsgLosslessPropNoPremise_iff :
    uufkoaDmsgLosslessPropNoPremise ↔ ∀ dmsg : SDistr Int, SDistr.mass dmsg = 1 := by
  simp only [uufkoaDmsgLosslessPropNoPremise, importedProp,
    uufkoaDmsgLosslessNoPremise, uufkoaDmsgLosslessBody, transForm_allConst,
    transForm_isLossless, FormEnv.bindConst, OpEnv.bindConst]
  rfl

/-- Dropping the premise is refutable: the failed computation is a realization of
mass zero, so the premise is what the source lemma states. -/
theorem not_uufkoaDmsgLosslessPropNoPremise : ¬ uufkoaDmsgLosslessPropNoPremise := by
  rw [uufkoaDmsgLosslessPropNoPremise_iff]
  intro h
  simpa using h SDistr.fail

/-! ## The committed realization -/

/-- The realizations of `UUFKOAROM`'s abstract operator: one sub-distribution on
the carrier of `Top.msg_t`. -/
structure UUFKOAData where
  /-- The realization of `op dmsg : msg_t distr.` -/
  dmsg : SDistr (EcTy.opaque "Top.msg_t").interp

/-- The operator environment a realization is: `Top.StatelessROM.UUFKOAROM.dmsg`
bound to `dmsg` at the signature its declaration gives it. -/
noncomputable def UUFKOAData.toOpEnv (D : UUFKOAData) : OpEnv :=
  OpEnv.empty.bindConst "Top.StatelessROM.UUFKOAROM.dmsg"
    (.distr (.opaque "Top.msg_t")) D.dmsg

/-- The imported statement as a hypothesis at the realization `D`. -/
noncomputable def uufkoaDmsgLosslessAt (D : UUFKOAData) : Prop :=
  importedPropWithOps ProcEnv.empty D.toOpEnv uufkoaDmsgLosslessBody

/-- The imported hypotheses of `UUFKOAROM` at the realization `D`: the theory's
one `axiom` item, which is the premise its clone's lemma is stated under. -/
structure UUFKOALaws (D : UUFKOAData) : Prop where
  /-- `op [lossless] dmsg : msg_t distr.` -/
  dmsg_ll : uufkoaDmsgLosslessAt D

/-- The hypothesis at a realization is that the realization has total mass one. -/
theorem uufkoaDmsgLosslessAt_iff (D : UUFKOAData) :
    uufkoaDmsgLosslessAt D ↔ SDistr.mass D.dmsg = 1 := by
  simp only [uufkoaDmsgLosslessAt, importedPropWithOps, uufkoaDmsgLosslessBody,
    transForm_isLossless, UUFKOAData.toOpEnv, OpEnv.bindConst]
  rfl

/-- The realization that puts all mass on one message. -/
noncomputable def UUFKOAData.pointMass (m : Int) : UUFKOAData := ⟨SDistr.pure m⟩

/-- `UUFKOAROM`'s imported hypotheses hold at the point mass, so the premise the
lemma is stated under is satisfiable and the lemma is not vacuous. -/
theorem UUFKOAData.pointMassLaws (m : Int) : UUFKOALaws (UUFKOAData.pointMass m) :=
  ⟨(uufkoaDmsgLosslessAt_iff _).2 (SDistr.mass_pure m)⟩

/-- The assembled lemma, instantiated at a realization meeting the imported
hypotheses, is the lemma's statement at that realization. -/
theorem uufkoaDmsgLosslessAt_of_laws (D : UUFKOAData) (h : UUFKOALaws D) :
    uufkoaDmsgLosslessAt D :=
  (uufkoaDmsgLosslessAt_iff D).2
    (uufkoaDmsgLosslessProp_iff.1 uufkoaDmsgLosslessProp_holds D.dmsg
      ((uufkoaDmsgLosslessAt_iff D).1 h.dmsg_ll))

end CatCrypt.Crypto.EasyCryptImport.Examples.UUFKOAPremiseImport

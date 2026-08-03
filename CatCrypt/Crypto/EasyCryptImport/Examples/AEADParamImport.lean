/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.EasyCryptImport.FormToProp

/-!
# An imported statement over an applied abstract operator

EasyCrypt's `theories/crypto/assumptions/AEAD.ec` declares:

```
type K, AData, Msg, Cph.
op enc : K -> AData -> Msg -> Cph distr.
axiom enc_ll : forall k a m, is_lossless (enc k a m).
```

`enc` is an abstract operator of three arguments and `enc_ll` a statement about
it. This module exhibits what the two become here: `enc` is a value parameter at
the signature its declared type gives it — its three arguments as the
right-nested product `K × (AData × Msg)`, the distributions over `Cph` as the
result — and `enc_ll` is a proposition about that parameter, quantified over the
three arguments.

## The read is uncurried and the realization is curried

An operator is resolved at one uniform signature, so the statement reads `enc` at
a single argument, the right-nested pair of the three quantified variables. A
realization is written curried, and `AEADData.toOpEnv` is where the two meet: the
field is a function of three arguments and the environment binds its uncurrying
at the declared signature.

## Two readings of one item, and which one applies

`enc_ll` carries `axiom_kind: Axiom`, so in EasyCrypt it is a hypothesis every
statement of the theory is proved under, not a claim the theory establishes. Both
readings are here, and they are different propositions:

* `aeadEncLosslessAt D` is the hypothesis at the realization `D`, which is
  `∀ k a m, SDistr.mass (D.enc k a m) = 1` (`aeadEncLosslessAt_iff`). This is the
  field a `Laws` structure carries and the premise a lemma of the theory is
  stated under.
* `aeadEncLosslessProp` is the statement closed over its parameter, which is
  `∀ enc : Carrier "Top.K" × Carrier "Top.AData" × Carrier "Top.Msg" →
  SDistr (Carrier "Top.Cph"), ∀ k a m,
  SDistr.mass (enc (k, a, m)) = 1` (`aeadEncLosslessProp_iff`). That is the
  reading an `axiom_kind: Lemma` item of a declaring theory gets. It is not what
  the source asserts about `enc`, and it is refutable
  (`not_aeadEncLosslessProp`), which is the difference between an item the theory
  assumes and an item it proves.

## The realization is exhibited, not assumed

A statement quantified over parameters under hypotheses says nothing when the
hypotheses cannot be met together, and nothing in a build detects an
unsatisfiable imported hypothesis set. `AEADData.pointMass` and
`AEADData.pointMassLaws` are the witness for this theory: an encryption that
returns a point mass has total mass one, so `AEADLaws` is inhabited and the
imported hypothesis set is satisfiable.

`Ty.lean` fixes the carrier of every `EcTy.opaque` at `Int`, so each of the four
carriers of `AEAD.ec` is `Int` here and every proposition below is at those
carriers.

The decode of the exported items — the `Th_axiom` statement and the argument
nesting an application of a three-argument declaration carries — is checked
against the exporter's node shapes in `FormJson.lean`; the literals below are the
values those decoders produce.

## Main definitions

* `aeadEncSig`: the signature `enc`'s declared type gives it.
* `aeadEncLosslessBody`: the decoded `enc_ll` statement, three `EcForm.allTy`
  binders over an `EcForm.isLossless` of an `opApp` applied to the right-nested
  pair of the bound variables.
* `aeadEncLossless`: the body closed over the operator it reads, with
  `EcForm.allOp`.
* `AEADData`, `AEADLaws`, `aeadEncLosslessAt`: a realization of the theory's
  abstract operator, its imported hypotheses, and the statement at that
  realization.

## Main results

* `aeadEncLosslessAt_iff`, `aeadEncLosslessProp_iff`: each reading is the
  expected statement about `SDistr.mass`.
* `AEADData.pointMassLaws`: a realization satisfying the imported hypotheses,
  which is what rules out their vacuity.
* `not_aeadEncLosslessProp`: the closed reading is refutable, so an `Axiom` item
  and a `Lemma` item cannot share it.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.EasyCryptImport.Examples.AEADParamImport

open CatCrypt.Core CatCrypt.Prob
open CatCrypt.Crypto.EasyCryptImport

/-! ## The imported statement -/

/-- The signature `enc`'s declaration gives it: its three arguments as the
right-nested product, the distributions over the ciphertexts as the result. -/
def aeadEncSig : EcSig :=
  ⟨.prod (.opaque "Top.K") (.prod (.opaque "Top.AData") (.opaque "Top.Msg")),
   .distr (.opaque "Top.Cph")⟩

/-- The body of `enc_ll`: for every key, associated data and message, the
distribution the abstract operator `Top.enc` gives them has total mass one. The
three arguments are read as the right-nested pair the signature's argument code
carries. -/
def aeadEncLosslessBody : EcForm :=
  .allTy (.opaque "Top.K") "k"
    (.allTy (.opaque "Top.AData") "a"
      (.allTy (.opaque "Top.Msg") "m"
        (.isLossless
          (.opApp "Top.enc" aeadEncSig
            (.pair (.var (.opaque "Top.K") "k")
              (.pair (.var (.opaque "Top.AData") "a")
                (.var (.opaque "Top.Msg") "m")))))))

/-- The body closed over the operator it reads. `enc` takes three arguments, so
the binder ranges over the functions on the signature's argument code. -/
def aeadEncLossless : EcForm := .allOp "Top.enc" aeadEncSig aeadEncLosslessBody

-- Assembling the body produces that statement, and the assembled statement reads
-- no operator it does not bind.
#guard (match aeadEncLosslessBody.assembleParams with
        | .allOp "Top.enc" s
            (.allTy _ "k" (.allTy _ "a" (.allTy _ "m" (.isLossless d)))) =>
            s == aeadEncSig && d.opAppOf == some ("Top.enc", aeadEncSig)
        | _ => false)

#guard EcForm.opsOf aeadEncLosslessBody.assembleParams == []

/-! ## The two propositions -/

/-- The imported statement as a goal: for every realization of `enc` and all
three arguments, the distribution the realization gives them has total mass
one. -/
noncomputable def aeadEncLosslessProp : Prop :=
  importedProp ProcEnv.empty aeadEncLossless

/-- The realizations of `AEAD.ec`'s abstract encryption: one sub-distribution on
the ciphertexts per key, associated data and message. -/
structure AEADData where
  /-- The realization of `op enc : K -> AData -> Msg -> Cph distr.` -/
  enc : (EcTy.opaque "Top.K").interp → (EcTy.opaque "Top.AData").interp →
    (EcTy.opaque "Top.Msg").interp → SDistr (EcTy.opaque "Top.Cph").interp

/-- The operator environment a realization is: `Top.enc` bound at the declared
signature to the uncurrying of the realization, since the signature carries the
three arguments as one right-nested product. -/
noncomputable def AEADData.toOpEnv (D : AEADData) : OpEnv :=
  OpEnv.empty.bindOp "Top.enc" (s := aeadEncSig)
    (fun p => D.enc p.1 p.2.1 p.2.2)

/-- The imported statement as a hypothesis at the realization `D`. -/
noncomputable def aeadEncLosslessAt (D : AEADData) : Prop :=
  importedPropWithOps ProcEnv.empty D.toOpEnv aeadEncLosslessBody

/-- The imported hypotheses of `AEAD.ec`'s encryption at the realization `D`. -/
structure AEADLaws (D : AEADData) : Prop where
  /-- `axiom enc_ll : forall k a m, is_lossless (enc k a m).` -/
  enc_ll : aeadEncLosslessAt D

/-! ## What the two propositions are -/

/-- The hypothesis at a realization is that every ciphertext distribution it
gives has total mass one. -/
theorem aeadEncLosslessAt_iff (D : AEADData) :
    aeadEncLosslessAt D
      ↔ ∀ (k : Carrier "Top.K") (a : Carrier "Top.AData") (m : Carrier "Top.Msg"),
          SDistr.mass (D.enc k a m) = 1 :=
  Iff.rfl

/-- The closed statement quantifies over the realization, at the function type
the declared signature gives it. -/
theorem aeadEncLosslessProp_iff :
    aeadEncLosslessProp
      ↔ ∀ enc : Carrier "Top.K" × Carrier "Top.AData" × Carrier "Top.Msg"
              → SDistr (Carrier "Top.Cph"),
          ∀ (k : Carrier "Top.K") (a : Carrier "Top.AData") (m : Carrier "Top.Msg"),
            SDistr.mass (enc (k, a, m)) = 1 :=
  Iff.rfl

/-! ## The committed realization -/

/-- The realization that answers every argument with one ciphertext. -/
noncomputable def AEADData.pointMass (c : Carrier "Top.Cph") : AEADData :=
  ⟨fun _ _ _ => SDistr.pure c⟩

/-- The imported hypotheses hold at the point mass, so the hypothesis set is
satisfiable and a statement proved under it is not vacuous. -/
theorem AEADData.pointMassLaws (c : Carrier "Top.Cph") :
    AEADLaws (AEADData.pointMass c) :=
  ⟨(aeadEncLosslessAt_iff _).2 (fun _ _ _ => SDistr.mass_pure c)⟩

/-- The closed reading is refutable: the failed computation is a realization of
mass zero, so quantifying `enc_ll` over every realization states something
`AEAD.ec` does not. -/
theorem not_aeadEncLosslessProp : ¬ aeadEncLosslessProp := by
  rw [aeadEncLosslessProp_iff]
  intro h
  simpa using h (fun _ => SDistr.fail) default default default

end CatCrypt.Crypto.EasyCryptImport.Examples.AEADParamImport

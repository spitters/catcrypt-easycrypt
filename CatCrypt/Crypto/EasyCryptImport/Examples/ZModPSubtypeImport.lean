/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.EasyCryptImport.Json

/-!
# An imported subtype whose bound is a declared operator

EasyCrypt's `theories/algebra/ZModP.ec` declares, in its inner theory `ZModRing`:

```
op p : int.
axiom ge2_p : 2 <= p.
subtype zmod = {x : int | 0 <= x < p}.
```

The subtype's bound is the declared `p`, so the type it cuts out of `int` depends
on the realization of `p`: no closed `EcTy` denotes it, and the code is a function
of the theory's parameters. This module is that function, together with the
nonemptiness the declaration owes.

## Where the inhabitation comes from

`EcTy.intRange lo hi` carries `lo < hi`, and `EcTy.interp` sends it to
`{x : Int // lo ≤ x ∧ x < hi}`, whose inhabitant is `⟨lo, _⟩`. At the bound `p`
the proof needed is `0 < p`, and the theory supplies it: `ge2_p` is an
`axiom_kind: Axiom` item, hence a hypothesis of every imported statement of
`ZModRing`, and `omega` takes `2 ≤ p` to `0 < p`. So the subtype is inhabited by
the source's own axiom, and `Nonempty` is nowhere assumed — which matters, because
an assumed inhabitation of a subtype that could be empty proves every statement of
the theory.

The export's `nonempty` reference names the obligation this discharges:
`Top.ZModRing.Sub.inhabited`, the `exists x, 0 <= x && x < p` that the
declaration's `Top.Subtype` clone left in the environment.
`Json.lean`'s `decodeThTypeSubtype` reads that reference off the payload and
rejects a declaration that carries none, so the obligation the importer discharges
is the one the source states rather than one the importer invented.
`zmodSubInhabited` is that obligation at a realization, and it is proved.

## What stays out

* The obligation has no `EcForm` image: its body compares integers, and `EcTerm`
  has no integer comparison, so the statement is written here as a Lean `∃` rather
  than decoded. It is stated at the same predicate the code carries.
* `axiom_kind: Lemma` on the reference does not say the source discharged the
  obligation — the export keeps the statement and discards the proof — so the
  proof here is the evidence, and the reference is only what locates the
  statement.
* The 16 integer-carrier corpus declarations whose `nonempty` does not resolve are
  decode rejections, and 11 of the 14 that do resolve state their bound's
  positivity through `prime` rather than through a `2 <= bound` axiom, so their
  realization supplies `0 < bound` itself until the integer-divisibility operator
  has an image. The three with a direct axiom are `Top.ZModRing.zmod` (`ge2_p`),
  `Top.ZModPCyclic.ZModRing.zmod` (`ge2_order`) and `Top.PolyReduceZp.Zp.zmod`
  (`ge2_p`).
-/

/-!
## Main definitions

* `ZModRingData`, `ZModRingLaws`: the theory's parameter (the modulus) and its
  imported hypothesis (`ge2_p`).
* `zmodTy`: the subtype code at a realization, whose `lo < hi` side condition is
  discharged from that hypothesis.
* `zmodDecl`: the declaration the decoder yields, carrying the carrier, the
  range predicate and the located obligation.

## Main results

* `zmodTy_interp`, `zmodTy_defaultOf_val`, `zmodTy_hasEq`, `zmodTy_isFin`: the
  code denotes the Lean subtype, its canonical inhabitant is the lower bound,
  equality is decidable and the code is not finite.
* `zmodSubInhabited`: the nonemptiness obligation holds at a realization,
  proved rather than postulated.
* `laws7`: a concrete realization discharging the hypothesis.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.EasyCryptImport.Examples.ZModPSubtypeImport

open Lean (Json)
open CatCrypt.Crypto.EasyCryptImport

/-! ## The theory's parameters and hypotheses -/

/-- The realization of `ZModRing`'s abstract operators: the modulus. -/
structure ZModRingData where
  /-- The realization of `op p : int.` -/
  p : Int

/-- `ZModRing`'s imported hypotheses: its one `axiom_kind: Axiom` item over `p`. -/
structure ZModRingLaws (D : ZModRingData) : Prop where
  /-- `axiom ge2_p : 2 <= p.` -/
  ge2_p : 2 ≤ D.p

/-! ## The subtype's code -/

/-- The code `subtype zmod = {x : int | 0 <= x < p}` denotes at a realization
satisfying the theory's hypotheses. The range proof the code carries is `ge2_p`
through `omega`. -/
def zmodTy (D : ZModRingData) (L : ZModRingLaws D) : EcTy :=
  .intRange 0 D.p (by have h := L.ge2_p; omega)

/-- The Lean type the subtype denotes: the integers the source's predicate keeps,
carrying the predicate. -/
theorem zmodTy_interp (D : ZModRingData) (L : ZModRingLaws D) :
    (zmodTy D L).interp = {x : Int // 0 ≤ x ∧ x < D.p} := rfl

/-- The inhabitant the code carries is the least element of the range. -/
theorem zmodTy_defaultOf_val (D : ZModRingData) (L : ZModRingLaws D) :
    ((zmodTy D L).defaultOf).val = 0 := rfl

/-- A value of the subtype has decidable equality and is countable, so it can be
compared in a statement and stored in a module global. -/
theorem zmodTy_hasEq (D : ZModRingData) (L : ZModRingLaws D) :
    (zmodTy D L).hasEq = true := rfl

/-- The subtype is outside the finite codes, so no uniform sampling is available
at it. Its interpretation is finite, and `EcTy.isFin` marks the codes whose
`Fintype` instance `EcTy.fintypeOfIsFin` produces; widening it is a separate
change. -/
theorem zmodTy_isFin (D : ZModRingData) (L : ZModRingLaws D) :
    (zmodTy D L).isFin = false := rfl

/-! ## The obligation the declaration owes -/

/-- `Top.ZModRing.Sub.inhabited`, the obligation the export's `nonempty` reference
names, at a realization: the range the subtype's predicate cuts out is inhabited.
It follows from `ge2_p`. -/
theorem zmodSubInhabited (D : ZModRingData) (L : ZModRingLaws D) :
    ∃ x : Int, 0 ≤ x ∧ x < D.p :=
  ⟨0, le_refl 0, by have h := L.ge2_p; omega⟩

/-! ## A committed realization

The code is a function of the realization, so the decode of a statement that names
the subtype is too. At one realization everything is closed, which is what the
checks below run on. -/

/-- The realization at the modulus seven. -/
def data7 : ZModRingData := ⟨7⟩

/-- Its hypotheses hold. -/
theorem laws7 : ZModRingLaws data7 := ⟨by norm_num [data7]⟩

/-- The declaration `Json.lean` decodes the exported payload of
`subtype zmod = {x : int | 0 <= x < p}` to. -/
def zmodDecl : EcSubtypeDecl where
  path := "Top.ZModRing.zmod"
  carrier := .int
  pred := .intRangeOp 0 "Top.ZModRing.p"
  nonempty := "Top.ZModRing.Sub.inhabited"
  nonemptyKind := "Lemma"

/-- The type node a statement of `ZModRing` names the subtype by. -/
private def jZmodTyNode : Json :=
  Json.mkObj [("kind", Json.str "Tconstr"),
              ("path", Json.str "Top.ZModRing.zmod"), ("args", Json.arr #[])]

-- The subtype's path resolves once the realization's code is registered for it,
-- and the code is the range the source's predicate names.
#guard (match decodeTy (ecPrelude.withSubtype zmodDecl (zmodTy data7 laws7))
            jZmodTyNode with
        | .ok t => t == EcTy.intRange 0 7
        | _ => false)

-- Without that registration the path has no code, rather than defaulting to the
-- carrier: a statement at the carrier would be a statement about the integers and
-- not about the subtype.
#guard (match decodeTy ecPrelude jZmodTyNode with
        | .error _ => true
        | _ => false)

end CatCrypt.Crypto.EasyCryptImport.Examples.ZModPSubtypeImport

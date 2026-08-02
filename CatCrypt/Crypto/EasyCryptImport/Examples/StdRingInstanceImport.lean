/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.EasyCryptImport.Instances

/-!
# The imported type-class instances of `algebra/StdRing.ec`

EasyCrypt's `theories/algebra/StdRing.ec` declares the integers a ring and the
booleans a boolean ring:

```
instance ring with int
  op rzero = CoreInt.zero
  op rone  = CoreInt.one
  op add   = CoreInt.add
  op opp   = CoreInt.opp
  op mul   = CoreInt.mul
  op expr  = Ring.IntID.exp
  proof oner_neq0 by smt() … proof exprS by smt(Ring.IntID.exprS).

instance bring with bool
  op rzero = false
  op rone  = true
  op add   = Bool.( ^^ )
  op mul   = (/\)
  op opp   = bid
  proof oner_neq0 by smt() … proof oppr_id by smt().
```

This module exhibits what each becomes here. Neither is a Mathlib `Ring`
instance: each is the bundle `Instances.lean` builds — the operators as
parameters at the signatures the declaration gives them, and the axioms
EasyCrypt required of the declaration as premises about a realization of those
parameters.

## The obligations are the source's own `proof` clauses

Each declaration's `proof` clauses are exactly the laws EasyCrypt derived from
the operators it named, and `stdRingInt_obligation_names` and
`stdRingBool_obligation_names` (`Instances.lean`) are that same list computed
from the payload. The integer declaration names an exponentiation, so `expr0`
and `exprS` are on its list; the boolean one names none, so they are off its
list, and its kind puts `addrK` and `mulrK` where `addrN` sits.

## The realization is exhibited, not assumed

A bundle of premises says nothing when nothing satisfies it, and nothing in a
build detects an unsatisfiable premise set. `intRingEnv` and `boolRingEnv` are
the realizations this module commits to — the operations of `Int` and of `Bool`
at the carriers `Ty.lean` fixes for `int` and `bool` — and
`stdRingInt_satisfiedBy` and `stdRingBool_satisfiedBy` discharge every law of the
respective bundle at them.

`not_stdRingInt_satisfiedBy_empty` is the other side: the realization that
answers every operator with the canonical inhabitant of its result code fails
`oner_neq0`, so the premises are not met by everything either.

## Main definitions

* `intRingEnv`: the realization of `instance ring with int`, the operations of
  `Int`.
* `boolRingEnv`: the realization of `instance bring with bool`, the operations of
  `Bool`.
* `stdRingIntZmodule`: one of the `General` items the integer declaration binds
  beside its `Ring` item.

## Main results

* `stdRingInt_satisfiedBy`, `stdRingBool_satisfiedBy`: each declaration's
  obligations hold at its realization, so neither bundle is vacuous.
* `not_stdRingInt_satisfiedBy_empty`: the premises are not met by every
  realization.
* `zmodule_not_satisfiedBy`: the `General` item has no satisfying realization,
  because it obliges no law and bundles nothing.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.EasyCryptImport.Examples.StdRingInstanceImport

open CatCrypt.Crypto.EasyCryptImport

/-! ## The realization of `instance ring with int` -/

/-- The realization of the integer ring's operators: the operations of `Int`, at
the signatures the declaration gives them. EasyCrypt's exponentiation is at an
integer exponent and the source's `Ring.IntID.exp` is the power at its
non-negative part. -/
def intRingEnv : OpEnv :=
  ((((((OpEnv.empty.bindConst "Top.CoreInt.zero" .int (0 : Int)).bindConst
    "Top.CoreInt.one" .int (1 : Int)).bindOp
    "Top.CoreInt.add" (s := stdRingIntOps.binSig) (fun p => p.1 + p.2)).bindOp
    "Top.CoreInt.opp" (s := stdRingIntOps.unSig) (fun x => -x)).bindOp
    "Top.CoreInt.mul" (s := stdRingIntOps.binSig) (fun p => p.1 * p.2)).bindOp
    "Top.Ring.IntID.exp" (s := stdRingIntOps.expSig) (fun p => p.1 ^ p.2.toNat))

@[simp] theorem intRingEnv_zero :
    stdRingIntOps.cstV intRingEnv "Top.CoreInt.zero" = 0 := rfl

@[simp] theorem intRingEnv_one :
    stdRingIntOps.cstV intRingEnv "Top.CoreInt.one" = 1 := rfl

@[simp] theorem intRingEnv_add (x y : Int) :
    stdRingIntOps.binV intRingEnv "Top.CoreInt.add" x y = x + y := rfl

@[simp] theorem intRingEnv_mul (x y : Int) :
    stdRingIntOps.binV intRingEnv "Top.CoreInt.mul" x y = x * y := rfl

@[simp] theorem intRingEnv_opp (x : Int) :
    stdRingIntOps.unV intRingEnv "Top.CoreInt.opp" x = -x := rfl

@[simp] theorem intRingEnv_exp (x n : Int) :
    stdRingIntOps.expV intRingEnv "Top.Ring.IntID.exp" x n = x ^ n.toNat := rfl

/-- The obligations of `instance ring with int` hold at the operations of `Int`,
so the bundle is satisfiable and a statement proved under it is not vacuous. -/
theorem stdRingInt_satisfiedBy : stdRingIntInstance.satisfiedBy intRingEnv := by
  refine fun nf hnf => ?_
  fin_cases hnf
  · exact (onerNeq0_iff _ _).2 (by simp)
  · exact (addr0_iff _ _).2 (fun x => by simp)
  · exact (addrA_iff _ _).2 (fun x y z => by simp only [intRingEnv_add]; ring)
  · exact (addrC_iff _ _).2 (fun x y => by simp only [intRingEnv_add]; ring)
  · exact (addrN_iff _ _ _).2 (fun x => by simp)
  · exact (mulr1_iff _ _).2 (fun x => by simp)
  · exact (mulrA_iff _ _).2 (fun x y z => by simp only [intRingEnv_mul]; ring)
  · exact (mulrC_iff _ _).2 (fun x y => by simp only [intRingEnv_mul]; ring)
  · exact (mulrDl_iff _ _).2 (fun x y z => by
      simp only [intRingEnv_add, intRingEnv_mul]; ring)
  · exact (expr0_iff _ _ _).2 (fun x => by simp)
  · exact (exprS_iff _ _ _).2 (fun x n hn => by
      simp only [intRingEnv_exp, intRingEnv_mul]
      have h : (n + 1).toNat = n.toNat + 1 := by omega
      rw [h, pow_succ, mul_comm])

/-- The realization that answers every operator with the canonical inhabitant of
its result code fails `oner_neq0`: the premises of the bundle are not met by
every realization. -/
theorem not_stdRingInt_satisfiedBy_empty :
    ¬ stdRingIntInstance.satisfiedBy OpEnv.empty := by
  intro h
  exact (onerNeq0_iff _ _).1
    (h ("oner_neq0", stdRingIntOps.onerNeq0Form) (List.Mem.head _)) rfl

/-! ## The realization of `instance bring with bool` -/

/-- The realization of the boolean ring's operators: exclusive-or as the
addition, conjunction as the multiplication, and the identity as the opposite. -/
def boolRingEnv : OpEnv :=
  (((((OpEnv.empty.bindConst "Top.Pervasive.false" .bool false).bindConst
    "Top.Pervasive.true" .bool true).bindOp
    "Top.Bool.^^" (s := stdRingBoolOps.binSig) (fun p => xor p.1 p.2)).bindOp
    "Top.Pervasive./\\" (s := stdRingBoolOps.binSig) (fun p => p.1 && p.2)).bindOp
    "Top.bid" (s := stdRingBoolOps.unSig) (fun b => b))

/-- The obligations of `instance bring with bool` hold at the operations of
`Bool`, so the bundle is satisfiable. Every law is a statement over a finite
carrier, so each is decided. -/
theorem stdRingBool_satisfiedBy : stdRingBoolInstance.satisfiedBy boolRingEnv := by
  refine fun nf hnf => ?_
  fin_cases hnf
  · exact (onerNeq0_iff _ _).2 (by decide)
  · exact (addr0_iff _ _).2 (by decide)
  · exact (addrA_iff _ _).2 (by decide)
  · exact (addrC_iff _ _).2 (by decide)
  · exact (addrK_iff _ _).2 (by decide)
  · exact (mulrK_iff _ _).2 (by decide)
  · exact (mulr1_iff _ _).2 (by decide)
  · exact (mulrA_iff _ _).2 (by decide)
  · exact (mulrC_iff _ _).2 (by decide)
  · exact (mulrDl_iff _ _).2 (by decide)
  · exact (opprId_iff _ _ _).2 (by decide)

/-! ## The general items the same declarations bind -/

/-- One of the `General` items `StdRing.ec`'s ring declaration binds beside its
`Ring` item, at the class the algebraic hierarchy assigns the type. -/
def stdRingIntZmodule : EcInstance where
  tparams := []
  ty := .int
  locality := .global
  body := .general "Top.Ring.ZModule.zmodule"

-- The corpus item decodes to it.
#guard (match decodeThInstance ecPrelude jStdRingIntZmodule with
        | .ok i => i == stdRingIntZmodule
        | _ => false)

/-- A general instance carries no operator, so it obliges no law and no
realization satisfies it. This is the difference between a rejection and an
empty bundle: an empty bundle would be satisfied by every realization. -/
theorem zmodule_not_satisfiedBy (ρ : OpEnv) : ¬ stdRingIntZmodule.satisfiedBy ρ :=
  not_satisfiedBy_of_error _ _ _ rfl

end CatCrypt.Crypto.EasyCryptImport.Examples.StdRingInstanceImport

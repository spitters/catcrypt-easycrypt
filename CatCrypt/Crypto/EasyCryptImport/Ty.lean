/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Countable.Basic
import Mathlib.Logic.Equiv.List

/-!
# EasyCrypt import: the type universe

`EcTy` is the universe of types the importer accepts, and `EcTy.interp` sends a
code to the Lean type it denotes. Every interpreted type carries `Countable`,
`Inhabited`, `DecidableEq` and `Nonempty` instances, which are the instances a
`CatCrypt.Core.GLocation` (a heap cell holding a countable value) and equality
tests require, so a global lives at any code. Finiteness is a predicate on codes,
`EcTy.isFin`, rather than a universal instance: `EcTy.fintypeOfIsFin` produces the
`Fintype` instance from a proof that a code is finite, and that is what uniform
sampling and a `CatCrypt.Core.Location` are stated against.

## The universe

* `unit` — EasyCrypt's `unit`, the result type of a `proc` returning nothing;
* `bool` — EasyCrypt's `bool`;
* `fin n` — a finite scalar type of cardinality `n`, interpreted as `Fin n`;
  the code carries a proof of `0 < n`, which makes every interpreted type
  inhabited, matching `SPComp.sample`'s `Nonempty` requirement (EasyCrypt's
  uniform `duniform` over an empty type is the zero sub-distribution and has no
  image here). The proof is an `autoParam` discharged by `omega`, so a closed
  code is written `.fin 3` with no proof term;
* `prod a b` — pairs, EasyCrypt's `a * b`;
* `int` — EasyCrypt's `int`, interpreted as `Int`;
* `map a b` — a finite map from `a` to `b`, EasyCrypt's `(a, b) fmap`,
  interpreted as the association list `List (a.interp × b.interp)` with the
  leftmost binding for a key winning. This is the shape of a random-oracle
  query log.

## The finite subset

`EcTy.isFin` marks the codes whose interpretation is a `Fintype`: `unit`, `bool`,
`fin n`, and products of those. `int` and `map` are outside it.

Uniform sampling requires a finite code and keeps requiring it: `SPComp.sample`
is uniform over its carrier, so it is available only at a finite code.
`EcTy.sampleFin` takes the `isFin` proof, and `EcStmt.sample` carries one.

A global requires none. `EcGlobal` in `Ast.lean` lives at a
`CatCrypt.Core.GLocation`, whose value type need only be countable and
inhabited, and whose `Heap.gget`/`Heap.gset` code through `gencode`. At a finite
code the same cell is also a `CatCrypt.Core.Location`, whose `Heap.get`/`Heap.set`
code through the `Fintype` encoding: the two codecs agree there
(`Heap.gget_ofLocation`, `Heap.gset_ofLocation`), so `EcGlobal.finLoc` is a view
of the cell rather than a second cell.

## Bound on expressible types

`EcTy` is closed under products and maps of countable types, so every
`EcTy.interp` is `Countable`. EasyCrypt types with no countable interpretation —
real-valued types, function types, arbitrary HOL types — have no `EcTy` code.

## Dynamically typed values

`EcVal` is a type code paired with a value of that type. It is the payload of
the local-variable valuation used by the lowering: a read at type `t` of a
variable holding a value of type `t' ≠ t` returns `default t`. Well-typedness of
the imported program is a property of the source, not enforced by `EcVal`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.EasyCryptImport

/-- Codes for the types the importer accepts. -/
inductive EcTy where
  /-- EasyCrypt's `unit`. -/
  | unit
  /-- EasyCrypt's `bool`. -/
  | bool
  /-- A finite scalar type of cardinality `n`, interpreted as `Fin n`. -/
  | fin (n : Nat) (pos : 0 < n := by omega)
  /-- A product type, EasyCrypt's `a * b`. -/
  | prod (a b : EcTy)
  /-- EasyCrypt's `int`. -/
  | int
  /-- A finite map, EasyCrypt's `(a, b) fmap`, as an association list. -/
  | map (a b : EcTy)
  deriving DecidableEq, Repr

/-- The Lean type a code denotes. -/
def EcTy.interp : EcTy → Type
  | .unit => Unit
  | .bool => Bool
  | .fin n _ => Fin n
  | .prod a b => a.interp × b.interp
  | .int => Int
  | .map a b => List (a.interp × b.interp)

instance interpInhabited : (t : EcTy) → Inhabited t.interp
  | .unit => inferInstanceAs (Inhabited Unit)
  | .bool => inferInstanceAs (Inhabited Bool)
  | .fin _ h => ⟨⟨0, h⟩⟩
  | .prod a b =>
      letI := interpInhabited a; letI := interpInhabited b
      inferInstanceAs (Inhabited (a.interp × b.interp))
  | .int => inferInstanceAs (Inhabited Int)
  | .map a b => inferInstanceAs (Inhabited (List (a.interp × b.interp)))

instance interpDecEq : (t : EcTy) → DecidableEq t.interp
  | .unit => inferInstanceAs (DecidableEq Unit)
  | .bool => inferInstanceAs (DecidableEq Bool)
  | .fin n _ => inferInstanceAs (DecidableEq (Fin n))
  | .prod a b =>
      letI := interpDecEq a; letI := interpDecEq b
      inferInstanceAs (DecidableEq (a.interp × b.interp))
  | .int => inferInstanceAs (DecidableEq Int)
  | .map a b =>
      letI := interpDecEq a; letI := interpDecEq b
      inferInstanceAs (DecidableEq (List (a.interp × b.interp)))

instance interpCountable : (t : EcTy) → Countable t.interp
  | .unit => inferInstanceAs (Countable Unit)
  | .bool => inferInstanceAs (Countable Bool)
  | .fin n _ => inferInstanceAs (Countable (Fin n))
  | .prod a b =>
      letI := interpCountable a; letI := interpCountable b
      inferInstanceAs (Countable (a.interp × b.interp))
  | .int => inferInstanceAs (Countable Int)
  | .map a b =>
      letI := interpCountable a; letI := interpCountable b
      inferInstanceAs (Countable (List (a.interp × b.interp)))

instance interpNonempty (t : EcTy) : Nonempty t.interp := ⟨default⟩

/-! ## The finite subset -/

/-- The codes whose interpretation is a `Fintype`. -/
def EcTy.isFin : EcTy → Bool
  | .unit => true
  | .bool => true
  | .fin _ _ => true
  | .prod a b => a.isFin && b.isFin
  | .int => false
  | .map _ _ => false

@[simp] theorem EcTy.isFin_unit : EcTy.unit.isFin = true := rfl
@[simp] theorem EcTy.isFin_bool : EcTy.bool.isFin = true := rfl
@[simp] theorem EcTy.isFin_fin (n : Nat) (h : 0 < n) :
    (EcTy.fin n h).isFin = true := rfl
@[simp] theorem EcTy.isFin_prod (a b : EcTy) :
    (EcTy.prod a b).isFin = (a.isFin && b.isFin) := rfl
@[simp] theorem EcTy.isFin_int : EcTy.int.isFin = false := rfl
@[simp] theorem EcTy.isFin_map (a b : EcTy) : (EcTy.map a b).isFin = false := rfl

/-- The `Fintype` instance of a finite code's interpretation. -/
@[reducible] def EcTy.fintypeOfIsFin : (t : EcTy) → t.isFin = true → Fintype t.interp
  | .unit, _ => inferInstanceAs (Fintype Unit)
  | .bool, _ => inferInstanceAs (Fintype Bool)
  | .fin n _, _ => inferInstanceAs (Fintype (Fin n))
  | .prod a b, h =>
      letI := a.fintypeOfIsFin (by simp at h; exact h.1)
      letI := b.fintypeOfIsFin (by simp at h; exact h.2)
      inferInstanceAs (Fintype (a.interp × b.interp))
  | .int, h => absurd h (by simp)
  | .map _ _, h => absurd h (by simp)

/-! ## Dynamically typed values -/

/-- A value together with the code of its type. -/
structure EcVal where
  /-- The code of the value's type. -/
  ty : EcTy
  /-- The value. -/
  val : ty.interp

/-- Read a dynamically typed value at the code `t`, returning `default` when the
stored value has a different type. -/
def EcVal.get (v : EcVal) (t : EcTy) : t.interp :=
  if h : v.ty = t then h ▸ v.val else default

@[simp] theorem EcVal.get_mk (t : EcTy) (v : t.interp) :
    (EcVal.mk t v).get t = v := dif_pos rfl

/-- The unit value, the payload of an unassigned local variable. -/
def EcVal.nil : EcVal := ⟨.unit, ()⟩

/-! ## Finite maps as association lists

A value of `(EcTy.map a b).interp` is a list of key/value pairs, and the leftmost
pair for a key is its binding. A new binding is added at the front, so it shadows
any earlier one. -/

/-- The binding of `k`, or `none` when `k` is unbound. -/
def EcTy.mapFind {a b : EcTy} (m : (EcTy.map a b).interp) (k : a.interp) :
    Option b.interp :=
  match m with
  | [] => none
  | (k', v) :: t => if k' = k then some v else EcTy.mapFind (a := a) (b := b) t k

/-- `m` with `k` bound to `v`, shadowing any earlier binding of `k`. -/
def EcTy.mapSet {a b : EcTy} (m : (EcTy.map a b).interp) (k : a.interp)
    (v : b.interp) : (EcTy.map a b).interp := (k, v) :: m

/-- Whether `k` is bound in `m`. -/
def EcTy.mapMem {a b : EcTy} (m : (EcTy.map a b).interp) (k : a.interp) : Bool :=
  (EcTy.mapFind (a := a) (b := b) m k).isSome

/-- The binding of `k`, or `d` when `k` is unbound. -/
def EcTy.mapGetD {a b : EcTy} (m : (EcTy.map a b).interp) (k : a.interp)
    (d : b.interp) : b.interp := (EcTy.mapFind (a := a) (b := b) m k).getD d

@[simp] theorem EcTy.mapFind_nil {a b : EcTy} (k : a.interp) :
    EcTy.mapFind (a := a) (b := b) [] k = none := rfl

@[simp] theorem EcTy.mapFind_mapSet_same {a b : EcTy}
    (m : (EcTy.map a b).interp) (k : a.interp) (v : b.interp) :
    EcTy.mapFind (a := a) (b := b) (EcTy.mapSet (a := a) (b := b) m k v) k = some v := by
  simp [EcTy.mapFind, EcTy.mapSet]

theorem EcTy.mapFind_mapSet_of_ne {a b : EcTy}
    (m : (EcTy.map a b).interp) {k k' : a.interp} (h : k' ≠ k) (v : b.interp) :
    EcTy.mapFind (a := a) (b := b) (EcTy.mapSet (a := a) (b := b) m k' v) k =
      EcTy.mapFind (a := a) (b := b) m k := by
  simp [EcTy.mapFind, EcTy.mapSet, h]

@[simp] theorem EcTy.mapMem_mapSet_same {a b : EcTy}
    (m : (EcTy.map a b).interp) (k : a.interp) (v : b.interp) :
    EcTy.mapMem (a := a) (b := b) (EcTy.mapSet (a := a) (b := b) m k v) k = true := by
  simp [EcTy.mapMem]

@[simp] theorem EcTy.mapGetD_mapSet_same {a b : EcTy}
    (m : (EcTy.map a b).interp) (k : a.interp) (v d : b.interp) :
    EcTy.mapGetD (a := a) (b := b) (EcTy.mapSet (a := a) (b := b) m k v) k d = v := by
  simp [EcTy.mapGetD]

end CatCrypt.Crypto.EasyCryptImport

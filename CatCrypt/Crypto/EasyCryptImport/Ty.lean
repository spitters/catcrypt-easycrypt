/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Countable.Basic
import Mathlib.Logic.Equiv.List
import CatCryptCore.Prob.SDistr

/-!
# EasyCrypt import: the type universe

`EcTy` is the universe of types the importer accepts, and `EcTy.interp` sends a
code to the Lean type it denotes. Every interpreted type carries `Inhabited`
and `Nonempty` instances. Decidable equality and countability are predicates
on codes rather than universal instances: `EcTy.hasEq` marks the codes that
have both — everything without a distribution inside — and `decEqOfHasEq` /
`countableOfHasEq` produce the instances from a proof. Both are computable, so
evaluation stays computable: `evalExpr` branches on a code's `hasEq` where it
compares values rather than taking a classical instance, which is what the
`#guard` checks of the golden fixtures need. Countability is what a
`CatCrypt.Core.GLocation` (a heap cell holding a countable value) requires, so
a global lives at a `hasEq` code and `EcGlobal` carries the proof. At a closed
code the standard instances also resolve directly, since `EcTy.interp` is
reducible. Finiteness is the predicate `EcTy.isFin`: `EcTy.fintypeOfIsFin`
produces the `Fintype` instance from a proof that a code is finite, and that
is what uniform sampling and a `CatCrypt.Core.Location` are stated against.

## The universe

* `unit` — EasyCrypt's `unit`, the result type of a `proc` returning nothing;
* `bool` — EasyCrypt's `bool`;
* `fin n` — a finite scalar type of cardinality `n`, interpreted as `Fin n`;
  the code carries a proof of `0 < n`, which makes every interpreted type
  inhabited, matching `SPComp.sample`'s `Nonempty` requirement (EasyCrypt's
  uniform `duniform` over an empty type is the zero sub-distribution and has no
  image here). The proof is an `autoParam` discharged by `omega`, so a closed
  code is written `.fin 3` with no proof term. An EasyCrypt datatype whose
  constructors all take no argument is at this code too, at the number of them;
  see the section on datatypes below;
* `prod a b` — pairs, EasyCrypt's `a * b`;
* `int` — EasyCrypt's `int`, interpreted as `Int`;
* `map a b` — a finite map from `a` to `b`, EasyCrypt's `(a, b) fmap`,
  interpreted as the association list `List (a.interp × b.interp)` with the
  leftmost binding for a key winning. This is the shape of a random-oracle
  query log.
* `option a` — EasyCrypt's `'a option`, interpreted as `Option a.interp`.
* `list a` — EasyCrypt's `'a list`, interpreted as `List a.interp`.
* `fset a` — a finite set, EasyCrypt's `'a fset`, interpreted as
  `Finset a.interp`. The quotient is what makes the image faithful: a sequence
  image would decode set equality at the representation, which tells two
  orderings of one set apart, while `Finset` identifies them, so decoded set
  equality is set equality. Every code carries `DecidableEq`, which is what the
  `Finset` operations need.
* `distr a` — EasyCrypt's `'a distr`, interpreted as `CatCrypt.Prob.SDistr
  a.interp`: a sub-distribution as a first-class value, which is how an oracle
  receives the distribution it samples from. The code is outside `hasEq` and
  outside `isFin`, so no equality test, no module variable and no uniform
  sampling lives at it; a distribution flows through formals and locals into
  `EcStmt.sampleD`.
* `intRange lo hi` — the integer range `{x : int | lo <= x < hi}`, interpreted as
  the Lean subtype `{x : Int // lo ≤ x ∧ x < hi}`. This is the image of an
  EasyCrypt `subtype` declaration at the `int` carrier. The code carries a proof
  of `lo < hi`, which is what inhabits the interpretation; see the section on
  subtypes below.
* `opaque name` — an abstract EasyCrypt type (`type pkey.`), which declares a
  name and nothing else. See the next section for what the code denotes.

## What an abstract type denotes

An abstract EasyCrypt type has no structure, so its faithful image would be a
type parameter supplied at lowering time. `EcTy.interp` is a plain function to
`Type` — every instance and every consumer of the AST applies it with no
environment in scope — so the code fixes a carrier instead: `interp` sends every
`opaque` code to `Int`, a countable, inhabited, non-finite type. Like the `fin n`
cardinality and the `oget` default, the carrier is a decision the ingestion
records where EasyCrypt leaves the matter open: a theorem about the imported
program is a theorem at that instantiation, not a theorem for every carrier. The
code carries the abstract type's path, so two abstract types are distinct codes
and the type-directed decoder keeps them apart even though their carriers
coincide.

## What an EasyCrypt datatype denotes

A datatype declaration whose constructors all take no argument declares a type
with one value per constructor and nothing besides. Its image is `fin k` at the
number of constructors, with the constructor in position `i` of the declaration
at the value `i`. EasyCrypt's constructors are distinct and exhaust the type, so
`Fin k`'s values are its constructors and the declaration order is what says
which is which — an ingestion decision of the same kind as the `fin n`
cardinality itself. Equality, countability and finiteness all hold at `fin k`, so
such a type is compared in a statement, held in a module global and sampled
uniformly.

A constructor that takes an argument makes the declaration a sum, and `EcTy` has
no sum code. A declaration with no constructor at all denotes the empty type,
which `interpInhabited` cannot produce, and `fin 0` is not a code.

## What an EasyCrypt subtype denotes, and where its inhabitation comes from

`subtype t = {x : c | P x}` declares a type whose values are the values of `c`
satisfying `P`. Its image at the `int` carrier is `intRange lo hi`, whose
interpretation is a Lean subtype, so a value of it carries the proof that it
satisfies the range: the predicate is part of the type rather than a side
condition a statement has to repeat.

The interpretation has to be inhabited, since `interpInhabited` is total. An empty
interpretation would need either a partial `interp` or a postulated `Nonempty`, and
a postulated one at an empty type proves anything about the theory. So the code
carries `lo < hi` and `interpInhabited` builds `⟨lo, _⟩` from it; nothing is
assumed, because `lo < hi` is supplied where the code is built.

The bound of an EasyCrypt subtype is generally not a literal — it is an operator
the theory declares (`subtype zmod = {x : int | 0 <= x < p}` for `op p : int.`) —
so the code is a function of that operator's realization and `lo < hi` is
discharged from the theory's imported hypotheses (`axiom ge2_p : 2 <= p.`) at the
instantiation. `Examples/ZModPSubtypeImport.lean` is the worked case, and
`Json.lean`'s `decodeThTypeSubtype` reads such a declaration and rejects one whose
nonemptiness obligation the export could not locate. At a supplied realization of
the bound (`Json.lean`'s `SubtypeBounds`) the type table holds the range code,
whose interpretation is finite and can therefore be sampled. With none supplied
it holds the abstract type, the shape HOL gives a type definition: the relation
to the carrier travels through the theory's own `val` and `insub` operators,
under the axioms `Top.Subtype` states about them.

## The finite subset

`EcTy.isFin` marks the codes whose interpretation is a `Fintype`: `unit`, `bool`,
`fin n`, and products, options and finite sets of those. `int`, `list`, `map`
and `opaque` are outside it — an abstract type need not be finite, so no uniform
sampling is available at an `opaque` code.

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

`EcTy`'s `hasEq` fragment is closed under products and maps of countable
types, so every `hasEq` interpretation is `Countable`; the `distr` code is the
one uncountable interpretation, and it is confined to values (formals and
locals). EasyCrypt types outside both — real-valued types, function types,
arbitrary HOL types, sums, and a subtype whose carrier is one of these — have no
`EcTy` code.

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
  /-- An option type, EasyCrypt's `'a option`. -/
  | option (a : EcTy)
  /-- A list type, EasyCrypt's `'a list`. -/
  | list (a : EcTy)
  /-- A finite set, EasyCrypt's `'a fset`, interpreted as `Finset` so that set
  equality is quotient equality. -/
  | fset (a : EcTy)
  /-- A sub-distribution over a carrier, EasyCrypt's `'a distr`, interpreted as
  `SDistr`. A distribution is a first-class value — a formal parameter or a
  local can hold one, which is how an oracle receives the distribution it
  samples from — but it is outside `hasEq` (no decidable equality) and its
  carrier is uncountable, so no module variable and no equality test lives at
  this code. -/
  | distr (a : EcTy)
  /-- The integer range `{x : int | lo <= x < hi}`, the image of an EasyCrypt
  `subtype` declaration at the `int` carrier, interpreted as the Lean subtype
  `{x : Int // lo ≤ x ∧ x < hi}`. The code carries `lo < hi`, which is what
  inhabits the interpretation; it is an `autoParam` discharged by `omega`, so a
  code at two literals is written `.intRange 0 7` with no proof term, and a code
  at a bound that is a theory parameter takes the proof from that theory's
  imported hypotheses. -/
  | intRange (lo hi : Int) (ne : lo < hi := by omega)
  /-- An abstract EasyCrypt type, carried by its path and interpreted at the
  fixed carrier `Int` (see the module docstring). Distinct paths are distinct
  codes. -/
  | opaque (name : String)
  deriving DecidableEq, Repr

/-- The Lean type a code denotes. Reducible, so that instance resolution at a
closed code sees the standard instances of the interpretation — `DecidableEq
(List Int)` at `(EcTy.list EcTy.int).interp` — rather than needing a
per-universe instance chain. -/
@[reducible] def EcTy.interp : EcTy → Type
  | .unit => Unit
  | .bool => Bool
  | .fin n _ => Fin n
  | .prod a b => a.interp × b.interp
  | .int => Int
  | .map a b => List (a.interp × b.interp)
  | .option a => Option a.interp
  | .list a => List a.interp
  | .fset a => Finset a.interp
  | .distr a => CatCrypt.Prob.SDistr a.interp
  | .intRange lo hi _ => {x : Int // lo ≤ x ∧ x < hi}
  | .opaque _ => Int

/-- A computable inhabitant of `SDistr α`: the failed computation, all mass on
`none`, written as a match so the value needs no decidable equality on `α`;
the summability proof transports from `PMF.pure`. -/
def sdistrDefault (α : Type) : CatCrypt.Prob.SDistr α :=
  ⟨fun o => match o with | none => 1 | some _ => 0, by
    have h : (fun o : Option α => match o with | none => (1 : ENNReal) | some _ => 0)
        = ⇑(PMF.pure (none : Option α)) := by
      funext o
      cases o <;> simp [PMF.pure_apply]
    rw [h]
    exact (PMF.pure (none : Option α)).2⟩

instance interpInhabited : (t : EcTy) → Inhabited t.interp
  | .unit => inferInstanceAs (Inhabited Unit)
  | .bool => inferInstanceAs (Inhabited Bool)
  | .fin _ h => ⟨⟨0, h⟩⟩
  | .prod a b =>
      letI := interpInhabited a; letI := interpInhabited b
      inferInstanceAs (Inhabited (a.interp × b.interp))
  | .int => inferInstanceAs (Inhabited Int)
  | .map a b => inferInstanceAs (Inhabited (List (a.interp × b.interp)))
  | .option a => inferInstanceAs (Inhabited (Option a.interp))
  | .list a => inferInstanceAs (Inhabited (List a.interp))
  | .fset a => inferInstanceAs (Inhabited (Finset a.interp))
  | .distr a => ⟨sdistrDefault a.interp⟩
  | .intRange lo _ h => ⟨⟨lo, le_refl lo, h⟩⟩
  | .opaque _ => inferInstanceAs (Inhabited Int)

/-- The codes whose interpretation has decidable equality and is countable —
exactly the codes without a distribution inside. `decEqOfHasEq` and
`countableOfHasEq` produce the instances from a proof; the equality-expression
decode and a module variable's heap cell are gated on it. -/
def EcTy.hasEq : EcTy → Bool
  | .unit => true
  | .bool => true
  | .fin _ _ => true
  | .prod a b => a.hasEq && b.hasEq
  | .int => true
  | .map a b => a.hasEq && b.hasEq
  | .option a => a.hasEq
  | .list a => a.hasEq
  | .fset a => a.hasEq
  | .distr _ => false
  | .intRange _ _ _ => true
  | .opaque _ => true

@[simp] theorem EcTy.hasEq_unit : EcTy.unit.hasEq = true := rfl
@[simp] theorem EcTy.hasEq_bool : EcTy.bool.hasEq = true := rfl
@[simp] theorem EcTy.hasEq_fin (n : Nat) (h : 0 < n) :
    (EcTy.fin n h).hasEq = true := rfl
@[simp] theorem EcTy.hasEq_prod (a b : EcTy) :
    (EcTy.prod a b).hasEq = (a.hasEq && b.hasEq) := rfl
@[simp] theorem EcTy.hasEq_int : EcTy.int.hasEq = true := rfl
@[simp] theorem EcTy.hasEq_map (a b : EcTy) :
    (EcTy.map a b).hasEq = (a.hasEq && b.hasEq) := rfl
@[simp] theorem EcTy.hasEq_option (a : EcTy) :
    (EcTy.option a).hasEq = a.hasEq := rfl
@[simp] theorem EcTy.hasEq_list (a : EcTy) : (EcTy.list a).hasEq = a.hasEq := rfl
@[simp] theorem EcTy.hasEq_fset (a : EcTy) : (EcTy.fset a).hasEq = a.hasEq := rfl
@[simp] theorem EcTy.hasEq_distr (a : EcTy) : (EcTy.distr a).hasEq = false := rfl
@[simp] theorem EcTy.hasEq_intRange (lo hi : Int) (h : lo < hi) :
    (EcTy.intRange lo hi h).hasEq = true := rfl
@[simp] theorem EcTy.hasEq_opaque (name : String) :
    (EcTy.opaque name).hasEq = true := rfl

/-- The decidable equality of a `hasEq` code's interpretation. At a closed
code the standard instances resolve through the reducible `EcTy.interp`, so
this is for a variable code, where the proof supplies what the instance
search cannot. -/
def decEqOfHasEq : (t : EcTy) → t.hasEq = true → DecidableEq t.interp
  | .unit, _ => inferInstanceAs (DecidableEq Unit)
  | .bool, _ => inferInstanceAs (DecidableEq Bool)
  | .fin n _, _ => inferInstanceAs (DecidableEq (Fin n))
  | .prod a b, h =>
      letI := decEqOfHasEq a (by simp at h; exact h.1)
      letI := decEqOfHasEq b (by simp at h; exact h.2)
      inferInstanceAs (DecidableEq (a.interp × b.interp))
  | .int, _ => inferInstanceAs (DecidableEq Int)
  | .map a b, h =>
      letI := decEqOfHasEq a (by simp at h; exact h.1)
      letI := decEqOfHasEq b (by simp at h; exact h.2)
      inferInstanceAs (DecidableEq (List (a.interp × b.interp)))
  | .option a, h =>
      letI := decEqOfHasEq a (by simp at h; exact h)
      inferInstanceAs (DecidableEq (Option a.interp))
  | .list a, h =>
      letI := decEqOfHasEq a (by simp at h; exact h)
      inferInstanceAs (DecidableEq (List a.interp))
  | .fset a, h =>
      letI := decEqOfHasEq a (by simp at h; exact h)
      inferInstanceAs (DecidableEq (Finset a.interp))
  | .distr _, h => absurd h (by simp)
  | .intRange lo hi hne, _ =>
      inferInstanceAs (DecidableEq {x : Int // lo ≤ x ∧ x < hi})
  | .opaque _, _ => inferInstanceAs (DecidableEq Int)

/-- The countability of a `hasEq` code's interpretation, which is what a heap
cell (`CatCrypt.Core.GLocation`) requires: a distribution's carrier is
uncountable, so a module variable cannot live at a `distr` code, and
`EcGlobal` carries the proof. -/
@[reducible] def countableOfHasEq : (t : EcTy) → t.hasEq = true → Countable t.interp
  | .unit, _ => inferInstanceAs (Countable Unit)
  | .bool, _ => inferInstanceAs (Countable Bool)
  | .fin n _, _ => inferInstanceAs (Countable (Fin n))
  | .prod a b, h =>
      letI := countableOfHasEq a (by simp at h; exact h.1)
      letI := countableOfHasEq b (by simp at h; exact h.2)
      inferInstanceAs (Countable (a.interp × b.interp))
  | .int, _ => inferInstanceAs (Countable Int)
  | .map a b, h =>
      letI := countableOfHasEq a (by simp at h; exact h.1)
      letI := countableOfHasEq b (by simp at h; exact h.2)
      inferInstanceAs (Countable (List (a.interp × b.interp)))
  | .option a, h =>
      letI := countableOfHasEq a (by simp at h; exact h)
      inferInstanceAs (Countable (Option a.interp))
  | .list a, h =>
      letI := countableOfHasEq a (by simp at h; exact h)
      inferInstanceAs (Countable (List a.interp))
  | .fset a, h =>
      letI := countableOfHasEq a (by simp at h; exact h)
      inferInstanceAs (Countable (Finset a.interp))
  | .distr _, h => absurd h (by simp)
  | .intRange lo hi _, _ =>
      inferInstanceAs (Countable {x : Int // lo ≤ x ∧ x < hi})
  | .opaque _, _ => inferInstanceAs (Countable Int)

instance interpNonempty (t : EcTy) : Nonempty t.interp := ⟨default⟩

/-- The canonical inhabitant of a code's interpretation, at the instance the
code selects. `EcTy.interp` is reducible, so at a closed code instance search
sees the interpretation rather than the code and can select an instance of the
interpreting type instead of `interpInhabited`'s arm for that code — at a
`distr` code it finds `PMF`'s noncomputable `Inhabited` — which would make a
value that cannot be evaluated. Naming the instance is what pins the
computable one, so a printed literal and a `#guard` over it agree. -/
def EcTy.defaultOf (t : EcTy) : t.interp := @default _ (interpInhabited t)

/-! ## The finite subset -/

/-- The codes whose interpretation is a `Fintype`. -/
def EcTy.isFin : EcTy → Bool
  | .unit => true
  | .bool => true
  | .fin _ _ => true
  | .prod a b => a.isFin && b.isFin
  | .int => false
  | .map _ _ => false
  | .option a => a.isFin
  | .list _ => false
  | .fset a => a.isFin
  | .distr _ => false
  | .intRange _ _ _ => false
  | .opaque _ => false

@[simp] theorem EcTy.isFin_unit : EcTy.unit.isFin = true := rfl
@[simp] theorem EcTy.isFin_bool : EcTy.bool.isFin = true := rfl
@[simp] theorem EcTy.isFin_fin (n : Nat) (h : 0 < n) :
    (EcTy.fin n h).isFin = true := rfl
@[simp] theorem EcTy.isFin_prod (a b : EcTy) :
    (EcTy.prod a b).isFin = (a.isFin && b.isFin) := rfl
@[simp] theorem EcTy.isFin_int : EcTy.int.isFin = false := rfl
@[simp] theorem EcTy.isFin_map (a b : EcTy) : (EcTy.map a b).isFin = false := rfl
@[simp] theorem EcTy.isFin_option (a : EcTy) :
    (EcTy.option a).isFin = a.isFin := rfl
@[simp] theorem EcTy.isFin_list (a : EcTy) : (EcTy.list a).isFin = false := rfl
@[simp] theorem EcTy.isFin_fset (a : EcTy) : (EcTy.fset a).isFin = a.isFin := rfl
@[simp] theorem EcTy.isFin_distr (a : EcTy) : (EcTy.distr a).isFin = false := rfl
@[simp] theorem EcTy.isFin_intRange (lo hi : Int) (h : lo < hi) :
    (EcTy.intRange lo hi h).isFin = false := rfl
@[simp] theorem EcTy.isFin_opaque (name : String) :
    (EcTy.opaque name).isFin = false := rfl

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
  | .option a, h =>
      letI := a.fintypeOfIsFin (by simp at h; exact h)
      inferInstanceAs (Fintype (Option a.interp))
  | .list _, h => absurd h (by simp)
  | .fset a, h =>
      letI := a.fintypeOfIsFin (by simp at h; exact h)
      inferInstanceAs (Fintype (Finset a.interp))
  | .distr _, h => absurd h (by simp)
  | .intRange _ _ _, h => absurd h (by simp)
  | .opaque _, h => absurd h (by simp)

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

/-- The binding of `k`, or `none` when `k` is unbound. The key comparison
takes the key code's `hasEq` as a trailing proof argument, discharged by `rfl`
at a closed code, and produces the decidable equality from it with
`decEqOfHasEq`.

The argument is a **proof**, not the `DecidableEq` instance itself. A proof is a
`Prop`, so two proofs of one code's `hasEq` are interchangeable, and a statement
about `mapFind` matches the `mapFind` that `evalExpr` builds. An instance
argument would put two syntactically different instances in those two terms —
the one instance search infers at the closed code, and the one `evalExpr`
supplies — and a rewrite against such a statement does not match. -/
def EcTy.mapFind {a b : EcTy}
    (m : (EcTy.map a b).interp) (k : a.interp)
    (hEq : a.hasEq = true := by rfl) : Option b.interp :=
  letI := decEqOfHasEq a hEq
  match m with
  | [] => none
  | (k', v) :: t => if k' = k then some v else EcTy.mapFind (a := a) (b := b) t k hEq

/-- `m` with `k` bound to `v`, shadowing any earlier binding of `k`. -/
def EcTy.mapSet {a b : EcTy} (m : (EcTy.map a b).interp) (k : a.interp)
    (v : b.interp) : (EcTy.map a b).interp := (k, v) :: m

/-- Whether `k` is bound in `m`. -/
def EcTy.mapMem {a b : EcTy}
    (m : (EcTy.map a b).interp) (k : a.interp)
    (hEq : a.hasEq = true := by rfl) : Bool :=
  (EcTy.mapFind (a := a) (b := b) m k hEq).isSome

/-- The binding of `k`, or `d` when `k` is unbound. -/
def EcTy.mapGetD {a b : EcTy}
    (m : (EcTy.map a b).interp) (k : a.interp) (d : b.interp)
    (hEq : a.hasEq = true := by rfl) : b.interp :=
  (EcTy.mapFind (a := a) (b := b) m k hEq).getD d

@[simp] theorem EcTy.mapFind_nil {a b : EcTy} (k : a.interp)
    (hEq : a.hasEq = true := by rfl) :
    EcTy.mapFind (a := a) (b := b) [] k hEq = none := rfl

@[simp] theorem EcTy.mapFind_mapSet_same {a b : EcTy}
    (m : (EcTy.map a b).interp) (k : a.interp) (v : b.interp)
    (hEq : a.hasEq = true := by rfl) :
    EcTy.mapFind (a := a) (b := b) (EcTy.mapSet (a := a) (b := b) m k v) k hEq
      = some v := by
  letI := decEqOfHasEq a hEq
  simp [EcTy.mapFind, EcTy.mapSet]

theorem EcTy.mapFind_mapSet_of_ne {a b : EcTy}
    (m : (EcTy.map a b).interp) {k k' : a.interp} (h : k' ≠ k) (v : b.interp)
    (hEq : a.hasEq = true := by rfl) :
    EcTy.mapFind (a := a) (b := b) (EcTy.mapSet (a := a) (b := b) m k' v) k hEq =
      EcTy.mapFind (a := a) (b := b) m k hEq := by
  letI := decEqOfHasEq a hEq
  simp [EcTy.mapFind, EcTy.mapSet, h]

@[simp] theorem EcTy.mapMem_mapSet_same {a b : EcTy}
    (m : (EcTy.map a b).interp) (k : a.interp) (v : b.interp)
    (hEq : a.hasEq = true := by rfl) :
    EcTy.mapMem (a := a) (b := b) (EcTy.mapSet (a := a) (b := b) m k v) k hEq
      = true := by
  simp [EcTy.mapMem]

@[simp] theorem EcTy.mapGetD_mapSet_same {a b : EcTy}
    (m : (EcTy.map a b).interp) (k : a.interp) (v d : b.interp)
    (hEq : a.hasEq = true := by rfl) :
    EcTy.mapGetD (a := a) (b := b) (EcTy.mapSet (a := a) (b := b) m k v) k d hEq
      = v := by
  simp [EcTy.mapGetD]

/-! ## Lists and options

The operations below are the `List` and `Option` ones at the element code's
instances, written against the interpretation of the codes so the AST's
evaluation can apply them without unfolding `EcTy.interp`. -/

/-- The empty list at the element code `a`. -/
def EcTy.listEmpty {a : EcTy} : (EcTy.list a).interp := ([] : List a.interp)

/-- List cons at the element code `a`. -/
def EcTy.listCons {a : EcTy} (x : a.interp) (l : (EcTy.list a).interp) :
    (EcTy.list a).interp :=
  show List a.interp from x :: (show List a.interp from l)

/-- Appending one element at the end of a list, EasyCrypt's `rcons`. -/
def EcTy.listRcons {a : EcTy} (l : (EcTy.list a).interp) (x : a.interp) :
    (EcTy.list a).interp :=
  show List a.interp from (show List a.interp from l) ++ [x]

/-- The length of a list as an integer, EasyCrypt's `size`. -/
def EcTy.listSize {a : EcTy} (l : (EcTy.list a).interp) : Int :=
  ((show List a.interp from l).length : Int)

/-- Whether `x` is an element of `l`, at the element code `a`. -/
def EcTy.listMem {a : EcTy}
    (l : (EcTy.list a).interp) (x : a.interp)
    (hEq : a.hasEq = true := by rfl) : Bool :=
  letI := decEqOfHasEq a hEq
  decide (x ∈ (show List a.interp from l))

/-- The `i`-th element of `l`, or `d` when `i` is out of range — EasyCrypt's
`nth d l i`, whose value at a negative or too-large index is the default. -/
def EcTy.listNth {a : EcTy} (d : a.interp) (l : (EcTy.list a).interp)
    (i : Int) : a.interp :=
  if i < 0 then d else (show List a.interp from l).getD i.toNat d

/-- The absent option value at the element code `a`. -/
def EcTy.noneVal {a : EcTy} : (EcTy.option a).interp :=
  (none : Option a.interp)

/-- The present option value at the element code `a`. -/
def EcTy.someVal {a : EcTy} (x : a.interp) : (EcTy.option a).interp :=
  show Option a.interp from some x

/-! ## Finite sets

A value of `(EcTy.fset a).interp` is a `Finset`, so the operations below are the
`Finset` ones at the element code's decidable equality, and equality of two set
values is quotient equality: which insertions built a set does not tell two
values apart. -/

/-- The empty finite set at the element code `a`. -/
def EcTy.fsetEmpty {a : EcTy} : (EcTy.fset a).interp := (∅ : Finset a.interp)

/-- The singleton finite set at the element code `a`. -/
def EcTy.fsetSingle {a : EcTy} (x : a.interp) : (EcTy.fset a).interp :=
  ({x} : Finset a.interp)

/-- The union of two finite sets at the element code `a`. -/
def EcTy.fsetUnion {a : EcTy} (s t : (EcTy.fset a).interp)
    (hEq : a.hasEq = true := by rfl) : (EcTy.fset a).interp :=
  letI := decEqOfHasEq a hEq
  show Finset a.interp from
    (show Finset a.interp from s) ∪ (show Finset a.interp from t)

/-- Whether `x` is an element of `s`, at the element code `a`. -/
def EcTy.fsetMem {a : EcTy} (s : (EcTy.fset a).interp) (x : a.interp)
    (hEq : a.hasEq = true := by rfl) : Bool :=
  letI := decEqOfHasEq a hEq
  decide (x ∈ (show Finset a.interp from s))

/-- The finite set of the elements of a list, at the element code `a`. This is
the shape the emitter prints a set value as: a set is the same value whichever
list of its elements is written. -/
def EcTy.fsetOfList {a : EcTy} (xs : List a.interp)
    (hEq : a.hasEq = true := by rfl) : (EcTy.fset a).interp :=
  letI := decEqOfHasEq a hEq
  show Finset a.interp from xs.toFinset

/-- Union of finite sets is commutative: the image is the quotient, so the
insertion order of one set is not observable. -/
theorem EcTy.fsetUnion_comm {a : EcTy} (s t : (EcTy.fset a).interp)
    (hEq : a.hasEq = true := by rfl) :
    EcTy.fsetUnion (a := a) s t hEq = EcTy.fsetUnion (a := a) t s hEq := by
  letI := decEqOfHasEq a hEq
  simp only [EcTy.fsetUnion]
  exact Finset.union_comm _ _

end CatCrypt.Crypto.EasyCryptImport

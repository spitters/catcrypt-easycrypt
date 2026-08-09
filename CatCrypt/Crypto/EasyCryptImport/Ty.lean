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
`evalExpr` branches on a code's `hasEq` where it compares values rather than
taking a classical instance. `evalExpr` itself is `noncomputable`: `EcTy.fset`
interprets as `Finset`, a quotient, and reading its elements as a list needs an
order the element type does not carry — `hasEq` supplies `Countable`, not the
`Encodable` a computable listing would need. Countability is what a
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
* `arrow a b` — a function type, EasyCrypt's `a -> b`, interpreted as the Lean
  function type `a.interp → b.interp`. Both arrows are total, so the two agree
  on which values the type has. The code is outside `hasEq` and outside `isFin`;
  see the section on function types below.
* `opaque name` — an abstract EasyCrypt type (`type pkey.`), which declares a
  name and nothing else. See the next section for what the code denotes.

## What an abstract type denotes

An abstract EasyCrypt type has no structure, so its faithful image would be a
type parameter supplied at lowering time. `EcTy.interp` is a plain function to
`Type` — every instance and every consumer of the AST applies it with no
environment in scope — so the code fixes a carrier instead: `interp` sends the
code `opaque p` to `Carrier p`, a one-field wrapper over `Int` whose type index
is the abstract type's path.

The index is part of the type, so two abstract types denote two Lean types:
`Top.pkey` and `Top.skey` are distinct codes and `Carrier "Top.pkey"` and
`Carrier "Top.skey"` are distinct interpretations, and a statement about one is
not a statement about the other. The wrapper is not definitionally `Int`, so
arithmetic and order on `Int` are not available at the carrier without passing
through `Carrier.val`. Inhabitation, decidable equality and countability come
from the `Int` field: that is what `hasEq` at an `opaque` code and a heap cell
(`CatCrypt.Core.GLocation`) require. The carrier is infinite, so `isFin` is
false at the code and no uniform sampling lives there.

Like the `fin n` cardinality and the `oget` default, the carrier is a decision
the ingestion records where EasyCrypt leaves the matter open: a theorem about the
imported program is a theorem at that instantiation, not a theorem for every
carrier. What it does not do is make the axioms of a theory satisfiable at the
carrier. `Carrier p` is a countably infinite type carrying no operations, so a
theory that declares operators over its abstract type and states axioms about
them still needs a per-theory realization witness — the operators exhibited at
the carrier, with the axioms discharged there.

## What a function type denotes

`arrow a b` denotes `a.interp → b.interp`. EasyCrypt's `->` is total functions
and Lean's `→` is total functions, so a value of the code is a value of the
source type.

`hasEq` is false at an arrow code, following the `distr` precedent: a function
space has neither decidable equality nor countability, so no equality test and
no module variable lives at one, and `decEqOfHasEq` and `countableOfHasEq` have
vacuous arrow arms.

`isFin` is false at every arrow code, including one whose domain and codomain
are both finite. This is a restriction of the code rather than a property of the
interpretation: no uniform sampling over a function space is available, and a
later phase may lift it.

A function reaches a statement as a quantified logical variable — `EcForm.allTy`
binds at an arbitrary `EcTy` — and is consumed by `EcTerm.app`. The term layer
has no lambda, so a function value is never constructed inside a statement.

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
`fin n`, and products, options and finite sets of those. `int`, `list`, `map`,
`arrow` and `opaque` are outside it — an abstract type need not be finite, so no
uniform sampling is available at an `opaque` code.

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
types, so every `hasEq` interpretation is `Countable`; the `distr` and `arrow`
codes are the uncountable interpretations, and each is confined to values —
formals, locals and quantified logical variables. EasyCrypt types outside both —
real-valued types, arbitrary HOL types, sums, and a subtype whose carrier is one
of these — have no `EcTy` code.

## Dynamically typed values

`EcVal` is a type code paired with a value of that type. It is the payload of
the local-variable valuation used by the lowering: a read at type `t` of a
variable holding a value of type `t' ≠ t` returns `default t`. Well-typedness of
the imported program is a property of the source, not enforced by `EcVal`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.EasyCryptImport

/-- The carrier of an abstract EasyCrypt type, indexed by that type's path: a
one-field wrapper over `Int`. Distinct paths are distinct types, and the wrapper
is not definitionally `Int`. -/
structure Carrier (path : String) where
  /-- The underlying integer. -/
  val : Int
  deriving DecidableEq, Repr, Inhabited

instance carrierCountable (path : String) : Countable (Carrier path) :=
  Function.Injective.countable (f := Carrier.val)
    (fun a b h => by cases a; cases b; exact congrArg Carrier.mk h)

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
  /-- A function type, EasyCrypt's `a -> b`, interpreted as the Lean function
  type `a.interp → b.interp`. Both arrows are total. The code is outside `hasEq`
  (a function space has neither decidable equality nor countability) and outside
  `isFin`, so no equality test, no module variable and no uniform sampling lives
  at it; a function is quantified over by `EcForm.allTy` and applied by
  `EcTerm.app`. -/
  | arrow (a b : EcTy)
  /-- An abstract EasyCrypt type, carried by its path and interpreted at the
  path-indexed carrier `Carrier name` (see the module docstring). Distinct paths
  are distinct codes and distinct interpretations. -/
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
  | .arrow a b => a.interp → b.interp
  | .opaque p => Carrier p

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
  | .arrow _ b =>
      letI := interpInhabited b
      ⟨fun _ => default⟩
  | .opaque p => inferInstanceAs (Inhabited (Carrier p))

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
  | .arrow _ _ => false
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
@[simp] theorem EcTy.hasEq_arrow (a b : EcTy) :
    (EcTy.arrow a b).hasEq = false := rfl
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
  | .arrow _ _, h => absurd h (by simp)
  | .opaque p, _ => inferInstanceAs (DecidableEq (Carrier p))

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
  | .arrow _ _, h => absurd h (by simp)
  | .opaque p, _ => inferInstanceAs (Countable (Carrier p))

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
  | .arrow _ _ => false
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
@[simp] theorem EcTy.isFin_arrow (a b : EcTy) :
    (EcTy.arrow a b).isFin = false := rfl
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
  | .arrow _ _, h => absurd h (by simp)
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

/-- `m` with every binding of `k` removed, EasyCrypt's `rem`. -/
def EcTy.mapRem {a b : EcTy} (m : (EcTy.map a b).interp) (k : a.interp)
    (hEq : a.hasEq = true := by rfl) : (EcTy.map a b).interp :=
  letI := decEqOfHasEq a hEq
  (show List (a.interp × b.interp) from m).filter (fun kv => !(kv.1 = k))

/-- The reading `FMap.ec` gives `rem`, as its own lemma `remE` states it: a
lookup after removing `k` answers nothing at `k` and is unchanged elsewhere. -/
theorem EcTy.mapFind_mapRem {a b : EcTy} (m : (EcTy.map a b).interp)
    (k y : a.interp) (hEq : a.hasEq = true) :
    letI := decEqOfHasEq a hEq
    EcTy.mapFind (a := a) (b := b) (EcTy.mapRem (a := a) (b := b) m k hEq) y hEq
      = if y = k then none else EcTy.mapFind (a := a) (b := b) m y hEq := by
  letI := decEqOfHasEq a hEq
  induction (show List (a.interp × b.interp) from m) with
  | nil => simp [EcTy.mapRem, EcTy.mapFind]
  | cons kv t ih =>
      obtain ⟨k', v⟩ := kv
      by_cases hk : k' = k <;> by_cases hy : y = k <;>
        by_cases hky : k' = y <;>
        simp_all [EcTy.mapRem, EcTy.mapFind]

/-- The elements of a finite set as a list, EasyCrypt's `elems`.

`FSet.ec` declares `elems` abstractly and constrains it by `elemsK`
(`oflist (elems s) = s`), `uniq_elems`, and `oflistK`, which fixes
`elems (oflist s)` only up to permutation. The source therefore does not
determine the order, and this fixes one, as the `fin n` cardinality and `oget`'s
default fix values EasyCrypt leaves open.

It is `noncomputable` because `EcTy.fset` interprets as `Finset`, a quotient, and
no order on the element type is available: `hasEq` supplies `Countable`, not the
`Encodable` a computable listing would need. -/
noncomputable def EcTy.fsetElems {a : EcTy} (s : (EcTy.fset a).interp) :
    (EcTy.list a).interp :=
  (show Finset a.interp from s).toList

/-- A list of `n` independent samples from `d`, EasyCrypt's `dlist d n`.

`DList.ec` characterises it by two lemmas: `dlist0`, that a non-positive count
gives the point mass at the empty list, and `dlistS`, that `dlist d (n + 1)` is
the cons image of the independent product of `d` with `dlist d n`. The recursion
below is those two equations, with the product written as the bind that does not
read its first component — which is what independence is. `Int.toNat` sends every
non-positive count to zero, so `dlist0`'s guard needs no arm of its own. -/
noncomputable def EcTy.distrList {a : EcTy} (d : (EcTy.distr a).interp) (n : Int) :
    (EcTy.distr (EcTy.list a)).interp :=
  let rec go : Nat → CatCrypt.Prob.SDistr (List a.interp)
    | 0 => CatCrypt.Prob.SDistr.pure []
    | k + 1 =>
        CatCrypt.Prob.SDistr.bind (show CatCrypt.Prob.SDistr a.interp from d)
          (fun x => CatCrypt.Prob.SDistr.bind (go k)
            (fun xs => CatCrypt.Prob.SDistr.pure (x :: xs)))
  go n.toNat

/-- Two lists paired position by position, EasyCrypt's `zip`. `List.ec` defines
it by recursion on both, stopping at whichever runs out first, which is
`List.zip`. -/
def EcTy.listZip {a b : EcTy} (l₁ : (EcTy.list a).interp) (l₂ : (EcTy.list b).interp) :
    (EcTy.list (EcTy.prod a b)).interp :=
  (show List a.interp from l₁).zip (show List b.interp from l₂)

/-- The concatenation of two lists, EasyCrypt's `++`. `List.ec` defines it by
recursion on the first, returning the second at the empty list and
`x :: (s1 ++ s2)` at `x :: s1`, which is `List.append`. -/
def EcTy.listCat {a : EcTy} (l₁ l₂ : (EcTy.list a).interp) : (EcTy.list a).interp :=
  show List a.interp from (show List a.interp from l₁) ++ (show List a.interp from l₂)

/-- The first `n` elements of a list, EasyCrypt's `take`. `List.ec` returns the
empty list at a non-positive count, which `Int.toNat` gives at every such count,
so the guard the source writes needs no arm of its own. -/
def EcTy.listTake {a : EcTy} (l : (EcTy.list a).interp) (n : Int) :
    (EcTy.list a).interp :=
  (show List a.interp from l).take n.toNat

/-- The list with position `i` replaced by `x`, EasyCrypt's array update
`arr.[i <- x]`. `Array.ec` gives it as a sequence of the array's own length whose
`k`-th entry is `x` where `i = k` and the old entry elsewhere, so an index outside
the list leaves it unchanged — a negative one included, since `i = k` is false at
every position there. -/
def EcTy.listSet {a : EcTy} (l : (EcTy.list a).interp) (i : Int) (x : a.interp) :
    (EcTy.list a).interp :=
  if 0 <= i then (show List a.interp from l).set i.toNat x
  else (show List a.interp from l)

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

open Classical in
/-- EasyCrypt's `choiceb`: an element the predicate holds of when there is one,
and the given default otherwise.

`Logic.ec` defines `choiceb P x0 = if exists x, P x then choicebd P else x0`,
where `choicebd` is an abstract operator whose only law is that `P (choicebd P)`
holds once some element satisfies `P`. `Exists.choose` is that operator: it is
determined by the proposition, so the same `P` picks the same element, and
`Exists.choose_spec` is the law. -/
noncomputable def EcTy.choiceb {a : EcTy} (p : a.interp → Bool) (x0 : a.interp) :
    a.interp :=
  if h : ∃ x, p x = true then h.choose else x0

/-- `k` applications of `f`, the `i`-th of them at the index `i`. -/
def EcTy.iteriNat {a : EcTy} :
    Nat → (Int → a.interp → a.interp) → a.interp → a.interp
  | 0, _, x => x
  | k + 1, f, x => f (k : Int) (EcTy.iteriNat k f x)

/-- EasyCrypt's `iteri`, an abstract operator whose laws are `iteri n f x = x`
at `n <= 0` and `iteri (n+1) f x = f n (iteri n f x)` at `0 <= n`. Iterating
`n.toNat` times satisfies both: a non-positive `n` iterates none, and at
`0 <= n` the index the step is applied at is `n` itself. -/
def EcTy.iteri {a : EcTy} (n : Int) (f : Int → a.interp → a.interp)
    (x : a.interp) : a.interp :=
  EcTy.iteriNat n.toNat f x

/-- EasyCrypt's `iter`: `iteri` with the index dropped. -/
def EcTy.iter {a : EcTy} (n : Int) (f : a.interp → a.interp) (x : a.interp) :
    a.interp :=
  EcTy.iteri n (fun _ y => f y) x

/-- EasyCrypt's `iterop`, defined there as
`iterop n opr x z = iteri n (fun i y => if i <= 0 then x else opr x y) z`. -/
def EcTy.iterop {a : EcTy} (n : Int)
    (opr : a.interp → a.interp → a.interp) (x z : a.interp) : a.interp :=
  EcTy.iteri n (fun i y => if i ≤ 0 then x else opr x y) z

/-- The image of a list under a function, EasyCrypt's `map`. -/
def EcTy.listMap {a b : EcTy} (f : a.interp → b.interp)
    (l : (EcTy.list a).interp) : (EcTy.list b).interp :=
  show List b.interp from (show List a.interp from l).map f

/-- The right fold of a list, EasyCrypt's `foldr f z s`: `f` applied to each
element and the fold of the rest, from `z` at the empty list. -/
def EcTy.listFoldr {a b : EcTy} (f : a.interp → b.interp → b.interp)
    (z : b.interp) (l : (EcTy.list a).interp) : b.interp :=
  (show List a.interp from l).foldr f z

/-- The elements a predicate holds of, in order, EasyCrypt's `filter`. -/
def EcTy.listFilter {a : EcTy} (p : a.interp → Bool)
    (l : (EcTy.list a).interp) : (EcTy.list a).interp :=
  show List a.interp from (show List a.interp from l).filter p

/-- Whether a predicate holds of every element, EasyCrypt's `all`. -/
def EcTy.listAll {a : EcTy} (p : a.interp → Bool)
    (l : (EcTy.list a).interp) : Bool :=
  (show List a.interp from l).all p

/-- Whether a predicate holds of some element, EasyCrypt's `has`. -/
def EcTy.listHas {a : EcTy} (p : a.interp → Bool)
    (l : (EcTy.list a).interp) : Bool :=
  (show List a.interp from l).any p

/-- How many elements a predicate holds of, EasyCrypt's `count`. -/
def EcTy.listCount {a : EcTy} (p : a.interp → Bool)
    (l : (EcTy.list a).interp) : Int :=
  (((show List a.interp from l).filter p).length : Int)

/-- The concatenation of a list of lists, EasyCrypt's `flatten`. `List.ec`
defines it as `foldr (++) []`, which is `List.flatten`. -/
def EcTy.listFlatten {a : EcTy} (l : (EcTy.list (EcTy.list a)).interp) :
    (EcTy.list a).interp :=
  (show List (List a.interp) from l).flatten

/-- Whether a list repeats no element, EasyCrypt's `uniq`, at the element code
`a`. -/
def EcTy.listUniq {a : EcTy} (l : (EcTy.list a).interp)
    (hEq : a.hasEq = true := by rfl) : Bool :=
  letI := decEqOfHasEq a hEq
  decide ((show List a.interp from l).Nodup)

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

/-- The first element of `l`, or `z` when `l` is empty — EasyCrypt's
`head z l`. -/
def EcTy.listHead {a : EcTy} (z : a.interp) (l : (EcTy.list a).interp) :
    a.interp :=
  (show List a.interp from l).headD z

/-- The first of the two equations `List.ec` defines `head` by: the default at
the empty list. -/
@[simp] theorem EcTy.listHead_nil {a : EcTy} (z : a.interp) :
    EcTy.listHead (a := a) z (EcTy.listEmpty (a := a)) = z := rfl

/-- The second of the two equations `List.ec` defines `head` by: the head of a
cons, whatever the default. -/
@[simp] theorem EcTy.listHead_cons {a : EcTy} (z x : a.interp)
    (l : (EcTy.list a).interp) :
    EcTy.listHead (a := a) z (EcTy.listCons (a := a) x l) = x := rfl

/-- The absent option value at the element code `a`. -/
def EcTy.noneVal {a : EcTy} : (EcTy.option a).interp :=
  (none : Option a.interp)

/-- The present option value at the element code `a`. -/
def EcTy.someVal {a : EcTy} (x : a.interp) : (EcTy.option a).interp :=
  show Option a.interp from some x

/-- The value an option carries, or `d` where it carries none: EasyCrypt's
`odflt d o`. `oget o` is this at the code's canonical inhabitant, which is what
EasyCrypt's own `oget` answers on `None`. -/
def EcTy.optionGetD {a : EcTy} (o : (EcTy.option a).interp) (d : a.interp) :
    a.interp :=
  (show Option a.interp from o).getD d

/-- The image of an option under a function, EasyCrypt's `omap`. -/
def EcTy.optionMap {a b : EcTy} (f : a.interp → b.interp)
    (o : (EcTy.option a).interp) : (EcTy.option b).interp :=
  show Option b.interp from (show Option a.interp from o).map f

/-! ## Distributions

A value of `(EcTy.distr a).interp` is a `CatCrypt.Prob.SDistr`, so the operations
below are stated against that sub-distribution. -/

open Classical in
/-- Whether `x` has nonzero mass in `d`, EasyCrypt's `support d x`.

`Distr.ec` defines `support d x = mu1 d x <> 0`, the membership `x \in d`, which
at `SDistr` is membership in `CatCrypt.Prob.SDistr.support`. That set is carved
out by a disequality of extended reals, so the test is its classical decision. -/
noncomputable def EcTy.support {a : EcTy} (d : (EcTy.distr a).interp)
    (x : a.interp) : Bool :=
  decide (x ∈ CatCrypt.Prob.SDistr.support
    (show CatCrypt.Prob.SDistr a.interp from d))

/-- EasyCrypt's `mu d p`: the probability that a sample from `d` satisfies `p`.

A `CatCrypt.Prob.SDistr a.interp` is a `PMF (Option a.interp)` whose mass on
`none` is the failed computation, so the value is the sum of the mass on
`some x` over the `x` the predicate holds of. -/
noncomputable def EcTy.mu {a : EcTy} (d : (EcTy.distr a).interp)
    (p : a.interp → Bool) : ENNReal :=
  ∑' x : a.interp,
    if p x then (show CatCrypt.Prob.SDistr a.interp from d) (some x) else 0

/-- The bind of `d` with `f`, EasyCrypt's `dlet`.

`Distr.ec` defines `dlet d f = mk (mlet d f)` at
`mlet d f y = sum<:'a> (fun x => mu1 d x * mu1 (f x) y)`, the monadic bind on
sub-distributions, which at `SDistr` is `CatCrypt.Prob.SDistr.bind`. This is the
meaning the program layer's `EcDistr.letD` already carries. -/
noncomputable def EcTy.distrLet {a b : EcTy} (d : (EcTy.distr a).interp)
    (f : a.interp → (EcTy.distr b).interp) : (EcTy.distr b).interp :=
  CatCrypt.Prob.SDistr.bind (show CatCrypt.Prob.SDistr a.interp from d)
    (fun v => show CatCrypt.Prob.SDistr b.interp from f v)

/-- The pushforward of `d` along `f`, EasyCrypt's `dmap`.

`Distr.ec` defines `dmap d f = dlet d (MUnit.dunit \o f)`, the bind of `d` with
the point mass at the image, which at `SDistr` is `EcTy.distrLet` against
`CatCrypt.Prob.SDistr.pure`. This is the meaning the program layer's
`EcDistr.map` already carries. -/
noncomputable def EcTy.distrMap {a b : EcTy} (d : (EcTy.distr a).interp)
    (f : a.interp → b.interp) : (EcTy.distr b).interp :=
  EcTy.distrLet (a := a) (b := b) d (fun v => CatCrypt.Prob.SDistr.pure (f v))

/-! ## Finite enumeration

`Finite.ec` states finiteness of a predicate through the lists that enumerate
it: `is_finite_for p s = uniq s /\ (forall x, x \in s <=> p x)` and
`is_finite p = exists s, is_finite_for p s`. -/

open Classical in
/-- EasyCrypt's `to_seq`: a duplicate-free list of exactly the values `p` holds
of when `p` holds of finitely many, and the empty list otherwise.

`Finite.ec` defines `to_seq p = choiceb (fun s => is_finite_for p s) []`, so the
value is a choice among the lists that enumerate `p` without repetition, with
the empty list where there is none. `Exists.choose` is that choice, as it is for
`EcTy.choiceb`. -/
noncomputable def EcTy.toSeq {a : EcTy} (p : a.interp → Bool) :
    (EcTy.list a).interp :=
  show List a.interp from
    if h : ∃ s : List a.interp, s.Nodup ∧ ∀ x, x ∈ s ↔ p x = true then h.choose
    else []

open Classical in
/-- EasyCrypt's `finite_type` at the code `a`: whether some duplicate-free list
holds every value of the carrier.

`Finite.ec` defines `finite_type = is_finite predT<:'a>`, and `Logic.ec` defines
`predT x = true`, so the predicate the enumeration is asked for is the one every
value satisfies. -/
noncomputable def EcTy.finiteType (a : EcTy) : Bool :=
  decide (∃ s : List a.interp, s.Nodup ∧ ∀ x, x ∈ s)

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

/-- The number of elements of `s`, at the element code `a`, as an integer. The
source's `card` is EasyCrypt's `int`, which is `EcTy.int`, so the count is
injected rather than left a `Nat`. -/
def EcTy.fsetCard {a : EcTy} (s : (EcTy.fset a).interp) : Int :=
  ((show Finset a.interp from s).card : Int)

/-- Whether every element of `s` is an element of `t`, at the element code
`a`. -/
def EcTy.fsetSubset {a : EcTy} (s t : (EcTy.fset a).interp)
    (hEq : a.hasEq = true := by rfl) : Bool :=
  letI := decEqOfHasEq a hEq
  decide ((show Finset a.interp from s) ⊆ (show Finset a.interp from t))

/-- The finite set of the elements of a list, at the element code `a`. This is
the shape the emitter prints a set value as: a set is the same value whichever
list of its elements is written. -/
def EcTy.fsetOfList {a : EcTy} (xs : List a.interp)
    (hEq : a.hasEq = true := by rfl) : (EcTy.fset a).interp :=
  letI := decEqOfHasEq a hEq
  show Finset a.interp from xs.toFinset

/-- A key the association list carries is bound, and a key it does not carry is
unbound: the keys of `m` are exactly the first components of its pairs. -/
theorem EcTy.mapFind_isSome_iff {a b : EcTy} (m : (EcTy.map a b).interp)
    (x : a.interp) (hEq : a.hasEq = true) :
    (EcTy.mapFind (a := a) (b := b) m x hEq).isSome = true
      ↔ x ∈ (show List (a.interp × b.interp) from m).map Prod.fst := by
  letI := decEqOfHasEq a hEq
  induction (show List (a.interp × b.interp) from m) with
  | nil => simp [EcTy.mapFind]
  | cons kv t ih =>
      obtain ⟨k, v⟩ := kv
      by_cases hk : k = x
      · simp_all [EcTy.mapFind]
      · simp_all [EcTy.mapFind]
        exact fun h => absurd h.symm hk

/-- The finite set of the keys `m` binds, EasyCrypt's `fdom`. -/
def EcTy.mapFdom {a b : EcTy} (m : (EcTy.map a b).interp)
    (hEq : a.hasEq = true := by rfl) : (EcTy.fset a).interp :=
  EcTy.fsetOfList (a := a)
    ((show List (a.interp × b.interp) from m).map Prod.fst) hEq

/-- The reading `FMap.ec` gives `fdom`, as its own lemma `mem_fdom` states it:
the elements of the domain are the keys the map binds. -/
theorem EcTy.fsetMem_mapFdom {a b : EcTy} (m : (EcTy.map a b).interp)
    (x : a.interp) (hEq : a.hasEq = true) :
    EcTy.fsetMem (a := a) (EcTy.mapFdom (a := a) (b := b) m hEq) x hEq
      = EcTy.mapMem (a := a) (b := b) m x hEq := by
  letI := decEqOfHasEq a hEq
  have h := EcTy.mapFind_isSome_iff (a := a) (b := b) m x hEq
  simp only [EcTy.fsetMem, EcTy.mapFdom, EcTy.fsetOfList, EcTy.mapMem,
    List.mem_toFinset]
  rw [Bool.eq_iff_iff, decide_eq_true_eq]
  exact h.symm

/-- Whether `y` is the binding of some key of `m`, EasyCrypt's `rng`. -/
def EcTy.mapRng {a b : EcTy} (m : (EcTy.map a b).interp) (y : b.interp)
    (hEqA : a.hasEq = true := by rfl) (hEqB : b.hasEq = true := by rfl) : Bool :=
  letI := decEqOfHasEq a hEqA
  letI := decEqOfHasEq b hEqB
  ((show List (a.interp × b.interp) from m).map Prod.fst).any
    (fun k => EcTy.mapFind (a := a) (b := b) m k hEqA = some y)

/-- The reading `FMap.ec` gives `rng`, which is its definition: `y` is in the
range exactly when some key is bound to it. A key the association list does not
carry is unbound, so quantifying over the keys it carries quantifies over every
key that could witness the range. -/
theorem EcTy.mapRng_iff {a b : EcTy} (m : (EcTy.map a b).interp) (y : b.interp)
    (hEqA : a.hasEq = true) (hEqB : b.hasEq = true) :
    EcTy.mapRng (a := a) (b := b) m y hEqA hEqB = true
      ↔ ∃ k, EcTy.mapFind (a := a) (b := b) m k hEqA = some y := by
  letI := decEqOfHasEq a hEqA
  letI := decEqOfHasEq b hEqB
  simp only [EcTy.mapRng, List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨k, _, hk⟩; exact ⟨k, hk⟩
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_, hk⟩
    exact (EcTy.mapFind_isSome_iff (a := a) (b := b) m k hEqA).mp (by simp [hk])

/-- Union of finite sets is commutative: the image is the quotient, so the
insertion order of one set is not observable. -/
theorem EcTy.fsetUnion_comm {a : EcTy} (s t : (EcTy.fset a).interp)
    (hEq : a.hasEq = true := by rfl) :
    EcTy.fsetUnion (a := a) s t hEq = EcTy.fsetUnion (a := a) t s hEq := by
  letI := decEqOfHasEq a hEq
  simp only [EcTy.fsetUnion]
  exact Finset.union_comm _ _

end CatCrypt.Crypto.EasyCryptImport

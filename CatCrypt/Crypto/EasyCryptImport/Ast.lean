/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.EasyCryptImport.Ty
import CatCryptCore.Core.Location
import CatCrypt.Core.GenHeap

/-!
# EasyCrypt import: abstract syntax

This module defines the Lean inductive types for the EasyCrypt subset the
importer accepts: typed expressions and statements, module-scoped global
variables, procedures, concrete modules, parameterised modules (functors), and
closed games.

## Supported fragment

* **Types** (`EcTy`, `Ty.lean`): `unit`, `bool`, `fin n`, products, `int`, and
  finite maps.
* **Expressions** (`EcExpr t`): intrinsically typed by an `EcTy` code —
  variables, literals, the boolean operators, decidable equality at any code,
  pair construction and projection, addition on `fin n`, integer addition and
  comparison, the finite-map operations, the finite-set operations (singleton,
  union, membership), the list operations (cons, `rcons`, `size`, `mem`,
  `nth`), and the some-constructor. Expression evaluation is pure: it reads a
  local valuation and returns a value.
* **Distributions** (`EcDistr t`): intrinsically typed by the code they are a
  distribution over — the uniform distribution on a finite code, a point mass at
  an expression, a pushforward along an expression under a binder, a distribution
  conditioned on a boolean expression under a binder, a bind whose second
  argument is a distribution under a binder, the independent product of two
  distributions, a rescaling to mass one, and a restriction to a boolean
  expression under a binder. A distribution expression reads the same local
  valuation an expression does.
* **Statements** (`EcStmt`):
  - `assign t x e` — the local assignment `x <- e`;
  - `assignTuple t xs e` — the destructuring assignment `(x₁, …, xₙ) <- e`,
    binding each name to its component of the right-nested product;
  - `sample t x` — uniform sampling `x <$ t`, at a finite code;
  - `sampleD t x d` — sampling `x <$ d` from a distribution expression;
  - `load g x` — the global read `x <- M.g`;
  - `store g e` — the global write `M.g <- e`;
  - `ite c thn els` — the conditional;
  - `forN n body` — the bounded loop that runs `body` `n` times, threading the
    local valuation and the heap through the iterations. It binds no counter: a
    source loop's counter is a program variable the body assigns;
  - `call p` — an argument-free call to a procedure of the enclosing game's
    procedure table, expanded by bounded inlining;
  - `callProc q s arg x` — the call `x <@ q(arg)` to the procedure registered
    under the qualified name `q` at signature `s`. This is the image of both a
    concrete module call `x <@ M.f(a)` and an abstract/adversary call
    `x <@ A.o(a)`; which one it is depends on what the resolution environment
    binds to `q` (`Modules.lean`). A call whose source discards the result
    binds it to the anonymous local, which no source variable can name;
  - `callProcTuple q s arg xs` — the call `(x₁, …, xₙ) <@ q(arg)`, whose
    result destructures the way `assignTuple`'s value does.
* **Globals** (`EcGlobal`): a module-scoped `var` with a stable location id and
  an `EcTy` code, at any code. It denotes a `GLocation`, the heap cell whose
  value type need only be countable and inhabited, which every `EcTy.interp` is.
  At a finite code the same cell is also a CatCrypt `Location`, `EcGlobal.finLoc`,
  and `EcGlobal.loc_finLoc` says the two views are the same cell.
* **Procedures** (`EcProcAt s`): the formal parameter names in declaration
  order, a statement body, and a return expression, at a fixed signature `s`
  whose argument type is the formals' types as a right-nested product.
* **Interfaces** (`EcInterface`): the declared procedure names of a module type
  together with each name's signature.
* **Modules** (`EcModule`): a name, a declared interface, the module's globals,
  and one procedure body per name of the interface.
* **Functors** (`EcFunctor`): a module body plus the interface of the module
  parameter and the prefix under which the parameter's procedures are called.
* **Games** (`EcGame`): declared locals, an argument-free procedure table, a
  statement body, and the bit that `main` returns.

## Out of scope

The following EasyCrypt features have no constructor here, and the importer
does not accept them:

* the distribution operators outside `EcDistr`: `dnull`, `dbiased`, `dbin`,
  `duniform` over a list, `dlist`, `dfun`, `dopt`, `dfold` and `dinter`;
* a loop with a runtime guard — `forN` carries an iteration count, and the
  EasyCrypt `while` shapes that determine one are listed in `Json.lean`;
* types outside `EcTy`, in particular real-valued types and sums; see `Ty.lean`
  for what the universe covers and where finiteness is still required;
* complexity and cost annotations (`[A : `#queries, …`]`), which have no
  representation in CatCrypt;
* module restrictions (`A{-M}`) and `islossless`, which are not part of the
  syntax: they are emitted as side hypotheses on the generated statement
  (`Restrictions.lean`).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.EasyCryptImport

open CatCrypt.Core

/-- The identity of a local variable: its source name together with the
uniqueness stamp EasyCrypt gives a bound identifier. A program variable — a
procedure's formal parameter, one of its declared locals — is a `PVloc` and
carries no stamp, so its stamp is `none`; an `EcIdent`, which is what a lambda
binder under a distribution operator is, carries the stamp the exporter writes.
Two identifiers of one source name and different stamps are different variables,
and the local valuation is keyed by the whole identity so that a binder cannot
capture an occurrence of another identifier of its name. -/
structure EcVarId where
  /-- The source name. -/
  name : String
  /-- The uniqueness stamp of a bound identifier; `none` for a program variable. -/
  stamp : Option Nat := none
  deriving DecidableEq, Repr, Inhabited

/-- The identity of the program variable of a given source name. -/
@[reducible] def EcVarId.ofName (x : String) : EcVarId := { name := x }

instance : Coe String EcVarId := ⟨EcVarId.ofName⟩

/-- Two program variables are the same variable exactly when their source names
agree: the program variables of a procedure are keyed by name, and it is the
stamped identifiers that a name alone does not determine. -/
@[simp] theorem EcVarId.ofName_inj {x y : String} :
    EcVarId.ofName x = EcVarId.ofName y ↔ x = y :=
  ⟨fun h => congrArg EcVarId.name h, fun h => h ▸ rfl⟩

/-- A procedure signature: the argument type and the result type. -/
structure EcSig where
  /-- The argument type. -/
  arg : EcTy
  /-- The result type. -/
  res : EcTy
  deriving DecidableEq, Repr

/-- A module type: the declared procedure names and their signatures. `sig` is
total; a name outside `names` is undeclared and its signature is irrelevant. -/
structure EcInterface where
  /-- The declared procedure names. -/
  names : List String
  /-- The signature of each name. -/
  sig : String → EcSig

/-- A module-scoped global variable: the source name (for provenance), the
location id it is assigned in the heap, and its type code. The code is
unrestricted, since every `EcTy.interp` is countable and inhabited, which is what
a `GLocation` requires. -/
structure EcGlobal where
  /-- The source name, `M.g`. -/
  name : String
  /-- The heap location id. -/
  id : Nat
  /-- The type code of the stored value. -/
  ty : EcTy
  /-- The stored code is countable: a heap cell holds a countable value, and a
  distribution's carrier is not one, so a module variable cannot live at a
  `distr` code — the decoder rejects one rather than construct this proof. At
  a closed code the default discharges the field. -/
  hasEq : ty.hasEq = true := by rfl

/-- The CatCrypt `GLocation` a global denotes. -/
def EcGlobal.loc (g : EcGlobal) : GLocation :=
  letI := countableOfHasEq g.ty g.hasEq
  { id := g.id, ty := g.ty.interp }

@[simp] theorem EcGlobal.loc_id (g : EcGlobal) : g.loc.id = g.id := rfl

/-- The CatCrypt `Location` a global at a finite code occupies. `Heap.get` and
`Heap.set` code a value through its `Fintype` encoding, so this view of the cell
needs the finiteness proof that `EcGlobal.loc` does not. -/
def EcGlobal.finLoc (g : EcGlobal) (h : g.ty.isFin = true) : Location :=
  letI := g.ty.fintypeOfIsFin h
  { id := g.id, ty := g.ty.interp }

@[simp] theorem EcGlobal.finLoc_id (g : EcGlobal) (h : g.ty.isFin = true) :
    (g.finLoc h).id = g.id := rfl

/-- The two views of a finite-typed global's cell agree: its `GLocation` is the
image of its `Location` under `GLocation.ofLocation`, along which `Heap.gget` and
`Heap.gset` restrict to `Heap.get` and `Heap.set`. -/
theorem EcGlobal.loc_finLoc (g : EcGlobal) (h : g.ty.isFin = true) :
    g.loc = GLocation.ofLocation (g.finLoc h) := rfl

/-- The set of location ids a list of globals occupies — the image of
EasyCrypt's `glob M` footprint. -/
def globLocs (gs : List EcGlobal) : LocSet := (gs.map EcGlobal.id).toFinset

/-- Intrinsically typed EasyCrypt expressions. -/
inductive EcExpr : EcTy → Type where
  /-- A local variable read `x`, at the type code `t`. The variable is named by
  its whole identity, so a program variable and a bound identifier of one source
  name are different reads. -/
  | var (t : EcTy) (x : EcVarId) : EcExpr t
  /-- A literal of the interpreted type. -/
  | lit {t : EcTy} (v : t.interp) : EcExpr t
  /-- An abstract operator of the enclosing theory, applied to an argument. The
  operator has no definition the source fixes, so the expression denotes a value
  only against a realization of the declaration: a program that reads one is
  parametric in it, exactly as a statement that reads one is (`EcForm.allOp`). A
  declaration of several arguments is read at the signature whose argument code is
  those arguments' codes as a right-nested product, the nesting a procedure's
  formals carry, and a declaration of none at `⟨unit, t⟩` applied to `.lit ()`.
  A declaration whose result is a distribution code is how an abstract
  distribution reaches sampling, through `EcDistr.ofExpr`. -/
  | opApp (path : String) (s : EcSig) (arg : EcExpr s.arg) : EcExpr s.res
  /-- A one-binder lambda, EasyCrypt's `fun x => e`. The binder is a local of
  the valuation the body reads, so the value is the function sending each
  argument to the body under the extended valuation. -/
  | lam (a : EcTy) {b : EcTy} (x : EcVarId) (body : EcExpr b) :
      EcExpr (.arrow a b)
  /-- The image of a list under a function, EasyCrypt's `map`. -/
  | listMap {a b : EcTy} (f : EcExpr (.arrow a b)) (l : EcExpr (.list a)) :
      EcExpr (.list b)
  /-- A function value applied to an argument. The function is any expression at
  an arrow code — a formal parameter or a local holding one, which is how a
  higher-order procedure receives it. Application is curried, so a source
  application of several arguments is this constructor once per argument. -/
  | app {a b : EcTy} (f : EcExpr (.arrow a b)) (x : EcExpr a) : EcExpr b
  /-- Boolean negation. -/
  | bnot (e : EcExpr .bool) : EcExpr .bool
  /-- Boolean conjunction. -/
  | band (a b : EcExpr .bool) : EcExpr .bool
  /-- Boolean exclusive-or. -/
  | bxor (a b : EcExpr .bool) : EcExpr .bool
  /-- Decidable equality at any type code. -/
  | beq {t : EcTy} (a b : EcExpr t) : EcExpr .bool
  /-- Pair construction. -/
  | pair {a b : EcTy} (x : EcExpr a) (y : EcExpr b) : EcExpr (.prod a b)
  /-- First projection. -/
  | fst {a b : EcTy} (p : EcExpr (.prod a b)) : EcExpr a
  /-- Second projection. -/
  | snd {a b : EcTy} (p : EcExpr (.prod a b)) : EcExpr b
  /-- Addition on `fin n`, wrapping. -/
  | finAdd {n : Nat} {pos : 0 < n} (a b : EcExpr (.fin n pos)) : EcExpr (.fin n pos)
  /-- Integer addition. -/
  | intAdd (a b : EcExpr .int) : EcExpr .int
  /-- Integer multiplication. -/
  | intMul (a b : EcExpr .int) : EcExpr .int
  /-- Integer negation. -/
  | intOpp (a : EcExpr .int) : EcExpr .int
  /-- Euclidean division, EasyCrypt's `edivz`: the quotient and the remainder as
  a pair, the remainder taken in `[0, |d|)`, and `(0, m)` at divisor zero. `%/`
  and `%%` are its projections. -/
  | intEdivz (a b : EcExpr .int) : EcExpr (.prod .int .int)
  /-- The absolute value, EasyCrypt's `absz`: the argument when it is
  non-negative and its negation otherwise. -/
  | intAbsz (a : EcExpr .int) : EcExpr .int
  /-- The greatest common divisor, EasyCrypt's `gcd`: the non-negative common
  divisor that every common divisor is bounded by, and `0` at `(0, 0)`. -/
  | intGcd (a b : EcExpr .int) : EcExpr .int
  /-- Integer order comparison. -/
  | intLe (a b : EcExpr .int) : EcExpr .bool
  /-- Bind a key in a finite map, shadowing any earlier binding. -/
  | mapSet {a b : EcTy} (m : EcExpr (.map a b)) (k : EcExpr a) (v : EcExpr b) :
      EcExpr (.map a b)
  /-- Whether a key is bound in a finite map. -/
  | mapMem {a b : EcTy} (m : EcExpr (.map a b)) (k : EcExpr a) : EcExpr .bool
  /-- The map with every binding of a key removed, EasyCrypt's `rem`. -/
  | mapRem {a b : EcTy} (m : EcExpr (.map a b)) (k : EcExpr a) :
      EcExpr (.map a b)
  /-- The binding of a key in a finite map, or a default when it is unbound. -/
  | mapGetD {a b : EcTy} (m : EcExpr (.map a b)) (k : EcExpr a) (d : EcExpr b) :
      EcExpr b
  /-- The finite set of the keys a finite map binds, EasyCrypt's `fdom`. -/
  | mapFdom {a b : EcTy} (m : EcExpr (.map a b)) : EcExpr (.fset a)
  /-- Whether a value is the binding of some key of a finite map, EasyCrypt's
  `rng` applied to a map and a value. -/
  | mapRng {a b : EcTy} (m : EcExpr (.map a b)) (y : EcExpr b) : EcExpr .bool
  /-- A conditional expression, EasyCrypt's `e ? a : b`. Both branches are
  expressions, so neither samples nor calls and the reading is a `Bool` test.
  A branch that is a statement is `EcStmt.ite` instead. -/
  | ite {t : EcTy} (c : EcExpr .bool) (thn els : EcExpr t) : EcExpr t
  /-- The present option value, EasyCrypt's `Some`. -/
  | someE {a : EcTy} (x : EcExpr a) : EcExpr (.option a)
  /-- The value an option carries, or a default, EasyCrypt's `odflt`. `oget` is
  this at the code's canonical inhabitant. The option is any expression, not
  only a map lookup. -/
  | optionGetD {a : EcTy} (o : EcExpr (.option a)) (d : EcExpr a) : EcExpr a
  /-- List cons, EasyCrypt's `::`. -/
  | listCons {a : EcTy} (x : EcExpr a) (l : EcExpr (.list a)) : EcExpr (.list a)
  /-- Appending one element at the end of a list, EasyCrypt's `rcons`. -/
  | listRcons {a : EcTy} (l : EcExpr (.list a)) (x : EcExpr a) : EcExpr (.list a)
  /-- The length of a list as an integer, EasyCrypt's `size`. -/
  | listSize {a : EcTy} (l : EcExpr (.list a)) : EcExpr .int
  /-- Membership in a list, EasyCrypt's `mem`. -/
  | listMem {a : EcTy} (l : EcExpr (.list a)) (x : EcExpr a) : EcExpr .bool
  /-- The `i`-th element of a list, or the default `d` when the index is out of
  range — EasyCrypt's `nth d l i`. -/
  | listNth {a : EcTy} (d : EcExpr a) (l : EcExpr (.list a)) (i : EcExpr .int) :
      EcExpr a
  /-- The first element of a list, or the default `z` when the list is empty —
  EasyCrypt's `head z l`. -/
  | listHead {a : EcTy} (z : EcExpr a) (l : EcExpr (.list a)) : EcExpr a
  /-- The list with a position replaced, EasyCrypt's array update
  `arr.[i <- x]`. -/
  | listSet {a : EcTy} (l : EcExpr (.list a)) (i : EcExpr .int) (x : EcExpr a) :
      EcExpr (.list a)
  /-- The first `n` elements of a list, EasyCrypt's `take`. -/
  | listTake {a : EcTy} (l : EcExpr (.list a)) (n : EcExpr .int) :
      EcExpr (.list a)
  /-- The elements of a finite set as a list, EasyCrypt's `elems`. -/
  | fsetElems {a : EcTy} (s : EcExpr (.fset a)) : EcExpr (.list a)
  /-- The concatenation of two lists, EasyCrypt's `++`. -/
  | listCat {a : EcTy} (l₁ l₂ : EcExpr (.list a)) : EcExpr (.list a)
  /-- Two lists paired position by position, EasyCrypt's `zip`. -/
  | listZip {a b : EcTy} (l₁ : EcExpr (.list a)) (l₂ : EcExpr (.list b)) :
      EcExpr (.list (.prod a b))
  /-- Whether a list repeats no element, EasyCrypt's `uniq`. -/
  | listUniq {a : EcTy} (l : EcExpr (.list a)) : EcExpr .bool
  /-- Whether a predicate holds of some element, EasyCrypt's `has`. -/
  | listHas {a : EcTy} (p : EcExpr (.arrow a .bool)) (l : EcExpr (.list a)) :
      EcExpr .bool
  /-- A universally quantified expression at the `bool` code, EasyCrypt's
  `forall x, e`. The binder is a local of the valuation the body reads, and the
  value is the classical decision of the proposition the body states — the
  reading `EcTerm.forallB` already has at the term layer. -/
  | forallB (a : EcTy) (x : EcVarId) (body : EcExpr .bool) : EcExpr .bool
  /-- An existentially quantified expression at the `bool` code. -/
  | existsB (a : EcTy) (x : EcVarId) (body : EcExpr .bool) : EcExpr .bool
  /-- The concatenation of a list of lists, EasyCrypt's `flatten`. -/
  | listFlatten {a : EcTy} (l : EcExpr (.list (.list a))) : EcExpr (.list a)
  /-- The singleton finite set, EasyCrypt's `fset1`. -/
  | fsetSingle {a : EcTy} (x : EcExpr a) : EcExpr (.fset a)
  /-- The union of two finite sets, EasyCrypt's `` (`|`) ``. -/
  | fsetUnion {a : EcTy} (s t : EcExpr (.fset a)) : EcExpr (.fset a)
  /-- Membership in a finite set, EasyCrypt's `mem`. -/
  | fsetMem {a : EcTy} (s : EcExpr (.fset a)) (x : EcExpr a) : EcExpr .bool
  /-- The number of elements of a finite set, EasyCrypt's `card`. -/
  | fsetCard {a : EcTy} (s : EcExpr (.fset a)) : EcExpr .int
  /-- Finite-set inclusion, EasyCrypt's `\subset`. -/
  | fsetSubset {a : EcTy} (s t : EcExpr (.fset a)) : EcExpr .bool

/-- The value an expression is, when the expression is a literal. The type index
is quantified, which is what lets a caller read the leaf out of an expression
whose index the context has already fixed: `EcStmt.store g e` types `e` at `g.ty`,
a projection out of a field, and a pattern for a literal there would make the
dependent pattern matcher solve an equation between two non-variable terms. -/
def EcExpr.litValue : {t : EcTy} → EcExpr t → Option t.interp
  | _, .lit v => some v
  | _, _ => none

/-- The variable an expression reads, when the expression is a variable read. The
type index is quantified for the reason `EcExpr.litValue` gives. -/
def EcExpr.varName : {t : EcTy} → EcExpr t → Option EcVarId
  | _, .var _ x => some x
  | _, _ => none

/-- The variable an expression increments, when the expression is `x + 1` or
`1 + x` at the integer code. The type index is quantified for the reason
`EcExpr.litValue` gives. -/
def EcExpr.incrOf : {t : EcTy} → EcExpr t → Option EcVarId
  | _, .intAdd a b =>
      match a.varName, b.litValue with
      | some x, some (1 : Int) => some x
      | _, _ =>
        match b.varName, a.litValue with
        | some x, some (1 : Int) => some x
        | _, _ => none
  | _, _ => none

/-- The counter and the bound of a guard of the shape `x < n`, at a variable `x`
and an integer literal `n`. EasyCrypt's strict integer order has no `EcExpr`
constructor of its own and decodes as the negation of the reversed `≤`, which is
the shape read here. -/
def EcExpr.ltGuard : {t : EcTy} → EcExpr t → Option (EcVarId × Int)
  | _, .bnot (.intLe a b) =>
      match a.litValue, b.varName with
      | some (n : Int), some x => some (x, n)
      | _, _ => none
  | _, _ => none

/-- Intrinsically typed EasyCrypt distribution expressions: `EcDistr t` is a
distribution over `t.interp`. A binder is an `EcVarId`, bound in the local
valuation the sub-expression under it reads, which is how a distribution operator
whose argument is a function reaches the AST. -/
inductive EcDistr : EcTy → Type where
  /-- The uniform distribution on a finite code, EasyCrypt's `dunifin`. The
  finiteness argument defaults to `rfl`, which discharges it for every closed
  finite code. -/
  | uniform (t : EcTy) (fin : t.isFin = true := by rfl) : EcDistr t
  /-- The point mass at an expression, EasyCrypt's `dunit`. -/
  | point {t : EcTy} (e : EcExpr t) : EcDistr t
  /-- The pushforward of `d` along `fun x => e`, EasyCrypt's `dmap`. -/
  | map {a b : EcTy} (d : EcDistr a) (x : EcVarId) (e : EcExpr b) : EcDistr b
  /-- `d` conditioned on `fun x => p`, EasyCrypt's `dcond`. EasyCrypt's
  `d \ X` — `dexcepted`, sampling `d` conditioned on avoiding `X` — is this
  constructor at the negated predicate, which is `dexcepted`'s own definition
  `dscale (drestrict d (predC X))`. -/
  | cond {t : EcTy} (d : EcDistr t) (x : EcVarId) (p : EcExpr .bool) : EcDistr t
  /-- The bind `dlet d (fun x => body)`, EasyCrypt's `dlet`: draw from `d`, bind
  the draw to `x`, and draw from the distribution `body` denotes under that
  binding. This is the constructor with a second recursive position under a
  binder. -/
  | letD {a b : EcTy} (d : EcDistr a) (x : EcVarId) (body : EcDistr b) : EcDistr b
  /-- The independent product `d₁ `*` d₂`, EasyCrypt's ``(`*`)``. -/
  | prod {a b : EcTy} (d₁ : EcDistr a) (d₂ : EcDistr b) : EcDistr (.prod a b)
  /-- A list of independent samples, EasyCrypt's `dlist d n`. `DList.ec`
  characterises it by `dlist0` (the point mass at the empty list at a
  non-positive count) and `dlistS` (a cons over the independent product of `d`
  with the shorter list), which is what the recursion below is. -/
  | dlist {a : EcTy} (d : EcDistr a) (n : EcExpr .int) : EcDistr (.list a)
  /-- `d` rescaled to mass one, EasyCrypt's `dscale`. -/
  | scale {t : EcTy} (d : EcDistr t) : EcDistr t
  /-- `d` with the mass outside `fun x => p` sent to failure, EasyCrypt's
  `drestrict`. -/
  | restrict {t : EcTy} (d : EcDistr t) (x : EcVarId) (p : EcExpr .bool) : EcDistr t
  /-- A distribution read out of an expression at a `distr` code — a formal
  parameter or a local holding a first-class distribution value, which is how
  an oracle samples from the distribution it was handed. -/
  | ofExpr {t : EcTy} (e : EcExpr (.distr t)) : EcDistr t

/-- The finiteness proof a distribution expression carries, when the expression is
the uniform distribution on its carrier. The type index is quantified, which is
what lets a caller read the proof out of a distribution whose index the context
has already fixed. -/
def EcDistr.uniformFin : {t : EcTy} → EcDistr t → Option (PLift (t.isFin = true))
  | _, .uniform _ h => some ⟨h⟩
  | _, _ => none

/-- EasyCrypt statements. -/
inductive EcStmt where
  /-- Local assignment `x <- e`. -/
  | assign (t : EcTy) (x : String) (e : EcExpr t)
  /-- Destructuring assignment `(x₁, …, xₙ) <- e`: `e` is typed at the
  components' types as a right-nested product, and each name binds its
  component in declaration order, exactly as a procedure's formals bind the
  argument (`bindParams`, `Lower.lean`). The names are carried as a list,
  mirroring `EcProcAt.params`; the rejected alternative — a fresh temporary
  plus binary projections — would manufacture a binder the source does not
  have and turn one instruction into a statement sequence. -/
  | assignTuple (t : EcTy) (xs : List String) (e : EcExpr t)
  /-- Uniform sampling `x <$ t` at a finite code. The finiteness argument
  defaults to `rfl`, which discharges it for every closed finite code. -/
  | sample (t : EcTy) (x : String) (fin : t.isFin = true := by rfl)
  /-- Sampling `x <$ d` from a distribution expression. -/
  | sampleD (t : EcTy) (x : String) (d : EcDistr t)
  /-- Global read `x <- g`. -/
  | load (g : EcGlobal) (x : String)
  /-- Global write `g <- e`. -/
  | store (g : EcGlobal) (e : EcExpr g.ty)
  /-- Conditional `if c then thn else els` over statement blocks. -/
  | ite (c : EcExpr .bool) (thn els : List EcStmt)
  /-- Bounded loop `for i = 0 to n-1 do body`. -/
  | forN (n : Nat) (body : List EcStmt)
  /-- Unbounded loop `while c do body`. The guard is an expression over the local
  valuation: a source guard reading a module global is decoded with that read
  hoisted into a load placed both before the loop and at the end of the body, so
  each iteration tests a value read in that iteration. The lowering is the limit
  of the bounded approximants (`CatCryptCore.NonUniform.whileLoopS`), so a run
  that never leaves the loop carries failure mass rather than an outcome. -/
  | whileS (c : EcExpr .bool) (body : List EcStmt)
  /-- Argument-free call `p()` to a procedure of the enclosing game's table. -/
  | call (p : String)
  /-- The call `x <@ q(arg)` at signature `s`, resolved against the ambient
  procedure environment. -/
  | callProc (q : String) (s : EcSig) (arg : EcExpr s.arg) (x : String)
  /-- The call `(x₁, …, xₙ) <@ q(arg)` at signature `s`, resolved against the
  ambient procedure environment: the result destructures into the names the
  way `EcStmt.assignTuple`'s value does. -/
  | callProcTuple (q : String) (s : EcSig) (arg : EcExpr s.arg) (xs : List String)

/-- The counter a statement initialises and the value it gives it, when the
statement assigns an integer literal to a local variable. -/
def EcStmt.initOf : EcStmt → Option (String × Int)
  | .assign t x e =>
      match t, e.litValue with
      | .int, some v => some (x, v)
      | _, _ => none
  | _ => none

/-- The counter a statement increments by one, when the statement is
`x <- x + 1`. -/
def EcStmt.incrOf : EcStmt → Option String
  | .assign _ x e => if e.incrOf == some (EcVarId.ofName x) then some x else none
  | _ => none

mutual

/-- The local variables a statement can write, or `none` when the statement does
not determine them. An argument-free `call` runs a procedure of the enclosing
game's table in the caller's own valuation, and the call site names neither the
table nor the body, so its write set is not determined here. -/
def EcStmt.assignedLocals : EcStmt → Option (List String)
  | .assign _ x _ => some [x]
  | .assignTuple _ xs _ => some xs
  | .sample _ x _ => some [x]
  | .sampleD _ x _ => some [x]
  | .load _ x => some [x]
  | .store _ _ => some []
  | .ite _ thn els =>
      match EcStmt.assignedLocalsList thn, EcStmt.assignedLocalsList els with
      | some a, some b => some (a ++ b)
      | _, _ => none
  | .forN _ body => EcStmt.assignedLocalsList body
  | .whileS _ body => EcStmt.assignedLocalsList body
  | .call _ => none
  | .callProc _ _ _ x => some [x]
  | .callProcTuple _ _ _ xs => some xs

/-- The local variables a statement block can write, or `none` when one of its
statements does not determine them. -/
def EcStmt.assignedLocalsList : List EcStmt → Option (List String)
  | [] => some []
  | s :: rest =>
      match s.assignedLocals, EcStmt.assignedLocalsList rest with
      | some a, some b => some (a ++ b)
      | _, _ => none

end

/-- Whether a statement block is known to leave the local variable `x`
untouched. A block whose write set is not determined is not known to. -/
def EcStmt.avoids (x : String) (body : List EcStmt) : Bool :=
  match EcStmt.assignedLocalsList body with
  | some ws => !ws.contains x
  | none => false

/-- A procedure body at a fixed signature: the formal parameter names in
declaration order, the statement body, and the return expression. The
signature's argument type is the formals' types as a right-nested product —
`unit` for no formals, the formal's own type for one — and a call site passes
its arguments in the same nesting, so the `k`-th formal binds the `k`-th
component at call entry (`bindParams`, `Lower.lean`). -/
structure EcProcAt (s : EcSig) where
  /-- The formal parameters in declaration order, each bound as a local
  variable. -/
  params : List String
  /-- The statement body. -/
  body : List EcStmt
  /-- The return expression. -/
  ret : EcExpr s.res

/-- A concrete EasyCrypt module: a declared interface, module-scoped globals,
and one procedure body per name of the interface. -/
structure EcModule where
  /-- The source module name (provenance, and the prefix used to qualify calls). -/
  name : String
  /-- The module type. -/
  interface : EcInterface
  /-- The module's `var` declarations. -/
  globals : List EcGlobal
  /-- The body of each declared procedure, at the interface's signature. -/
  procs : (p : String) → EcProcAt (interface.sig p)

/-- A parameterised module `F(X : paramInterface)`: the body is a module whose
procedures may call `X`'s procedures under the qualified prefix `paramName`. -/
structure EcFunctor where
  /-- The functor name (provenance). -/
  name : String
  /-- The prefix under which the parameter's procedures are called. -/
  paramName : String
  /-- The interface the parameter module must implement. -/
  paramInterface : EcInterface
  /-- The functor body. -/
  body : EcModule

/-- An EasyCrypt experiment: declared locals, an argument-free procedure table
for intra-game `call`s, the body of `main`, and the bit `main` returns. -/
structure EcGame where
  /-- The source game name (provenance). -/
  name : String
  /-- The declared local variables (provenance; an unassigned local reads as the
  default of its type). -/
  locals : List String
  /-- The argument-free procedures `call` refers to. -/
  procs : List (String × List EcStmt) := []
  /-- The statement body of `main`. -/
  body : List EcStmt
  /-- The bit `main` returns. -/
  ret : EcExpr .bool

/-- The qualified name of procedure `p` of the module bound at `pfx`. -/
def qualify (pfx p : String) : String := pfx ++ "." ++ p

/-- The name the exporter gives the procedure or global `p` of the module whose
path is `pfx`: EasyCrypt's cross-path, written with a slash between the module
path and the component. This is the key a call site, an assignment to a global
and a judgement name their target by. -/
def xqualify (pfx p : String) : String := pfx ++ "./" ++ p

end CatCrypt.Crypto.EasyCryptImport

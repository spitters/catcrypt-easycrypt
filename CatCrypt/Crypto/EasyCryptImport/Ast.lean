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
  comparison, and the finite-map operations. Expression evaluation is pure: it
  reads a local valuation and returns a value.
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
  - `sample t x` — uniform sampling `x <$ t`, at a finite code;
  - `sampleD t x d` — sampling `x <$ d` from a distribution expression;
  - `load g x` — the global read `x <- M.g`;
  - `store g e` — the global write `M.g <- e`;
  - `ite c thn els` — the conditional;
  - `forN n body` — the bounded loop `for i = 0 to n-1 do body`;
  - `call p` — an argument-free call to a procedure of the enclosing game's
    procedure table, expanded by bounded inlining;
  - `callProc q s arg x` — the call `x <@ q(arg)` to the procedure registered
    under the qualified name `q` at signature `s`. This is the image of both a
    concrete module call `x <@ M.f(a)` and an abstract/adversary call
    `x <@ A.o(a)`; which one it is depends on what the resolution environment
    binds to `q` (`Modules.lean`).
* **Globals** (`EcGlobal`): a module-scoped `var` with a stable location id and
  an `EcTy` code, at any code. It denotes a `GLocation`, the heap cell whose
  value type need only be countable and inhabited, which every `EcTy.interp` is.
  At a finite code the same cell is also a CatCrypt `Location`, `EcGlobal.finLoc`,
  and `EcGlobal.loc_finLoc` says the two views are the same cell.
* **Procedures** (`EcProcAt s`): a formal parameter name, a statement body, and
  a return expression, at a fixed signature `s`.
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
* unbounded `while` loops with a runtime guard — only the bounded `forN`;
* types outside `EcTy`, in particular real-valued and function types; see
  `Ty.lean` for what the universe covers and where finiteness is still required;
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

/-- The CatCrypt `GLocation` a global denotes. -/
def EcGlobal.loc (g : EcGlobal) : GLocation := { id := g.id, ty := g.ty.interp }

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
  /-- Integer order comparison. -/
  | intLe (a b : EcExpr .int) : EcExpr .bool
  /-- Bind a key in a finite map, shadowing any earlier binding. -/
  | mapSet {a b : EcTy} (m : EcExpr (.map a b)) (k : EcExpr a) (v : EcExpr b) :
      EcExpr (.map a b)
  /-- Whether a key is bound in a finite map. -/
  | mapMem {a b : EcTy} (m : EcExpr (.map a b)) (k : EcExpr a) : EcExpr .bool
  /-- The binding of a key in a finite map, or a default when it is unbound. -/
  | mapGetD {a b : EcTy} (m : EcExpr (.map a b)) (k : EcExpr a) (d : EcExpr b) :
      EcExpr b

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
  /-- `d` rescaled to mass one, EasyCrypt's `dscale`. -/
  | scale {t : EcTy} (d : EcDistr t) : EcDistr t
  /-- `d` with the mass outside `fun x => p` sent to failure, EasyCrypt's
  `drestrict`. -/
  | restrict {t : EcTy} (d : EcDistr t) (x : EcVarId) (p : EcExpr .bool) : EcDistr t

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
  /-- Argument-free call `p()` to a procedure of the enclosing game's table. -/
  | call (p : String)
  /-- The call `x <@ q(arg)` at signature `s`, resolved against the ambient
  procedure environment. -/
  | callProc (q : String) (s : EcSig) (arg : EcExpr s.arg) (x : String)

/-- A procedure body at a fixed signature: the formal parameter name, the
statement body, and the return expression. -/
structure EcProcAt (s : EcSig) where
  /-- The formal parameter, bound as a local variable. -/
  param : String
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

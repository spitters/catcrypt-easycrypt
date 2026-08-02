/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.EasyCryptImport.Ast
import Mathlib.Data.ENNReal.Basic

/-!
# EasyCrypt import: the syntax of imported statements

`Ast.lean` gives the syntax of imported *programs*. This module gives the syntax
of imported *statements*: the shape a lemma taken from an EasyCrypt development
has when it arrives in Lean, before it is translated to a CatCrypt proposition
(`FormToProp.lean`).

The syntax is three layers, mirroring EasyCrypt's `form`:

* `EcTerm t` — the value layer, intrinsically typed by an `EcTy` code. Logical
  variables, literals, a module global read at a memory (`g{&m}`), the result of
  the enclosing judgement (`res`), the operators of `Ast.lean`'s expression
  fragment, an application of an abstract operator (`opApp`), `if`, and `let`.
  An `EcExpr` embeds directly (`ofExpr`).
* `EcProb` — the probability layer: `Pr[q(arg) @ &m : ev]`, constants, a
  probability-valued parameter, sum, product, and absolute difference.
* `EcForm` — the formula layer: the first-order skeleton (the connectives,
  quantifiers over an `EcTy`, over a memory, over a probability parameter, over
  a module type — restricted or not, and carrying the bound module's footprint
  or not — and over the realizations of an abstract operator or constant, term
  equality,
  memory equality, footprint agreement, `if`, `let`) together with the six modal
  nodes: a probability comparison, a Hoare judgement, a bounded Hoare judgement,
  a relational (equiv) judgement, a procedure's losslessness assertion, and a
  distribution's losslessness assertion.

## Abstract items are parameters of the statement

An EasyCrypt theory declares operators without definitions, and a statement of
that theory reads them. `EcForm.allOp` quantifies over the realization of one
such declaration at the signature the declaration gives it, and `EcForm.allConst`
over the value of a declaration that takes no argument, so an imported statement
of a declaring theory reads "for every realization of the operators it names,
`φ`". `Params.lean` defines the realization environment `OpEnv`, and
`EcForm.opsOf` collects the operators a statement reads but does not bind:
`EcForm.assembleParams` wraps a statement in one binder per collected operator,
and `opsOf` of the result is empty.

A theory also constrains its declarations by axioms, and a lemma of that theory
holds under them. `EcForm.assembleStatement` puts those axioms to the left of
`EcForm.imp` and closes the whole implication over the operators the axioms and
the goal read, so an imported lemma reads "for every realization of the
declarations, the theory's imported axioms imply `φ`".

## Type parameters are binders over the type codes

An EasyCrypt statement written `lemma foo ['a] : φ` is polymorphic in `'a`, and
every type position of `φ` may name it. `EcTy` is a closed universe of codes with
a fixed interpretation, so a type parameter is not an `EcTy` node — it names no
code. What it is here is a binder over the codes: `EcPolyForm n` is a statement
awaiting the `n` codes its parameters are read at, in the order the source
declares them, and `FormToProp.importedPropPoly` quantifies over them. An
imported polymorphic lemma reads "for every `n` type codes, for every realization
of the operators the statement reads, the axioms in scope imply the statement":
the type binders are outermost, since a code fixes the signatures the operator
binders range at.

The binder ranges over `EcTy`, and not over `Type`. The two differ, and the
difference is a weakening: a Lean type outside the image of `EcTy.interp` is not
reached, while the source ranges over every EasyCrypt type. A binder over `Type`
needs `EcTy.interp` indexed by a carrier assignment, which makes the heap model
realization-dependent — `EcGlobal.loc` builds a location out of the
interpretation of a code, so which cell a global is would depend on the
assignment — and re-indexes every value, expression, statement and procedure of
the AST by it.

The type binders sit outside `EcForm` rather than inside it. An `EcForm` node
binding a code carries its body as a function `EcTy → EcForm`, because `EcTerm`
is indexed by the code of its value and so the body's own syntax is fixed only
once the code is. The first-order recursions over `EcForm` — `opsOf`,
`namesGlobOf`, and the emitter's printer — would then each have to choose a code
to recurse at, and a printer cannot apply such a body at a code it is printing as
a variable. `EcPolyForm` keeps `EcForm` first-order and puts the quantifier where
the printer can name it.

An operator is resolved at one uniform signature: a declaration of `n` arguments
is read at the signature whose argument code is those arguments' codes as a
right-nested product, the nesting a procedure's formals carry, and
`EcTerm.nestArgs` builds the argument of such a read from the arguments in source
order.

The two binders differ in what they range over and not in what they bind. A
declaration of no arguments is read at `⟨unit, t⟩` and its realization is a
function on `Unit`. The binder of
a statement is what a reader of that statement sees, and the source declares a
value of `t`, so `allConst` binds `v : t.interp` and answers the read through
`OpEnv.bindConst`. The read itself stays `EcTerm.opApp` at `⟨unit, t⟩`: one
source read has one AST shape, the decoder chooses nothing, and the unit
application disappears in the translation, where `bindConst` sends it to `v`.

`EcForm` and `EcProb` are mutually recursive because the event of a `Pr[…]` node
is itself a formula and a formula compares probabilities.

## Typing discipline: intrinsic at the term layer, annotated at the formula layer

`EcTerm` is intrinsically typed, like `EcExpr`: a term carries the `EcTy` code of
its value. The payoff is that term evaluation and formula translation are
**total** functions — there is no `Option`, no failure case, and hence no partial
translation whose failure could turn into a vacuously provable goal.

`EcForm` is not intrinsically typed. It has no type index because the sorts its
nodes range over — `Prop`, a probability in `ℝ≥0∞`, a memory (`Heap`), a module
value (`ModuleImpl I` at a varying interface) — are not codes in any single
universe that `EcTy` could be extended to. Instead the sorts are separated
syntactically: memories are named by `EcMemRef`, probabilities live in `EcProb`,
module binders name their interface, and `EcForm` itself is the `Prop` layer.
Stratifying this way keeps the translation total without a dependently typed
formula index and without transport lemmas at every node.

## Memories and sides

An `EcMemRef` is either a memory named by a quantifier (`&m`) or one of the three
memories a judgement binds: the two sides of an equiv judgement (EasyCrypt's
`{1}` and `{2}`) and the ambient memory of a unary judgement or a `Pr[…]` event
(EasyCrypt's `&hr`). `res` carries the same side tag, so `res{1}`, `res{2}` and
`res` are `EcTerm.res _ .left`, `EcTerm.res _ .right` and `EcTerm.res _ .cur`.

## Out of scope

The following EasyCrypt form nodes have no constructor here. Each is absent
because CatCrypt has no target for it; the reason is given with the node.

* **Statement judgements** (`hoare{ s }`, `equiv{ s₁ ~ s₂ }`, EasyCrypt's
  `FhoareS`/`FbdHoareS`/`FequivS`): their assertions range over the local
  variables in scope, and locals are meta-level in the lowering (a valuation
  `Env`, not heap state), so there is nothing for such an assertion to denote.
  Only the procedure-level judgements are present.
* **Local program variables** `x{&m}` for a procedure-local `x`, for the same
  reason. `EcTerm.glob` reads a module global, which is a heap cell; `res` is
  available because a judgement binds it.
* **`glob M` as a value** (`Fglob`): a memory restricted to a module's footprint
  is not a value of an `EcTy`. Footprint-level *comparison* is available, as
  `EcForm.memEqOn` against a list of declared globals and as
  `EcForm.memEqOnMod` against the footprint of a module binder in scope.
* **Eager/lazy judgements** (`Feager`): CatCrypt has no eager-sampling judgement.
* **Pattern matching** (`Fmatch`): `EcTy` has no sum or inductive codes, so there
  is nothing to match on beyond `bool`, which `EcTerm.ite` covers.
* **General real terms**: reals appear only as probabilities, in `EcProb`. A
  bound of the form `q / 2 ^ n` with `q` a quantified integer is outside the
  fragment; a bound that is a closed constant is `EcProb.const`.
* **Signed subtraction of probabilities**: `EcProb` has `absDiff` but no `sub`.
  Probabilities translate into `ℝ≥0∞`, where subtraction is truncated, so a
  signed difference `Pr[A] - Pr[B]` — which EasyCrypt allows to be negative — has
  no faithful image. The bound shapes EasyCrypt statements actually use,
  `|Pr[A] - Pr[B]| ≤ ε` and `Pr[A] ≤ Pr[B] + ε`, are `absDiff` and `add`.
* **Cost and complexity forms**: no representation, as for the restrictions
  (`Restrictions.lean`).
* **Quantification over a function variable of the source**: the value
  quantifiers range over an `EcTy`, a memory or a probability. `EcForm.allOp`
  ranges over the realizations of an operator the source *declares*, at the
  signature its declaration gives it, which is a parameter of the statement
  rather than a bound variable of the formula.
* **Polymorphic operator declarations** (`tparams ≠ []`): `EcTy` has no type
  variables, so an operator declaration that binds one has no `EcSig`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.EasyCryptImport

open CatCrypt.Core
open scoped ENNReal

/-! ## Memories, sides, comparisons -/

/-- Which memory of a judgement a reference denotes: the left or right side of a
relational judgement (EasyCrypt's `{1}` and `{2}`), or the ambient memory of a
unary judgement or a probability event (EasyCrypt's `&hr`). -/
inductive EcSide where
  /-- The left side of a relational judgement, EasyCrypt's `{1}`. -/
  | left
  /-- The right side of a relational judgement, EasyCrypt's `{2}`. -/
  | right
  /-- The ambient memory of a unary judgement or a probability event. -/
  | cur
  deriving DecidableEq, Repr

/-- A memory reference: a memory bound by a quantifier, or one bound by the
enclosing judgement. -/
inductive EcMemRef where
  /-- A memory bound by a quantifier, EasyCrypt's `&m`. -/
  | named (m : String)
  /-- A memory bound by the enclosing judgement. -/
  | side (s : EcSide)
  deriving DecidableEq, Repr

/-- The comparisons a probability statement uses. EasyCrypt's `hoarecmp` covers
`le`, `eq` and `ge`; `lt` and `gt` are the strict comparisons a general form may
write between reals. -/
inductive EcCmp where
  /-- `≤`. -/
  | le
  /-- `<`. -/
  | lt
  /-- `=`. -/
  | eq
  /-- `≥`. -/
  | ge
  /-- `>`. -/
  | gt
  deriving DecidableEq, Repr

/-! ## Real literals -/

/-- A real literal of the fragment: the natural number the decoder read, and the
bound it denotes. EasyCrypt writes such a bound as `from_int n`, so the numeral is
the whole of what the export carries and `EcRealLit.value` is its reading.

The value is a function of the numeral rather than a second field beside it, so
the numeral is the denotation of the value by construction: `EcRealLit.value ⟨n⟩`
is `(n : ℝ≥0∞)` by `rfl`, the semantics still goes through `ℝ≥0∞` since nothing
matches on `num`, and a printer reading `num` reads a presentation of the same
bound. A pair of fields with a proof obligation joining them is the weaker form,
because the obligation can be omitted at a construction site.

The cost is that a bound which is not a natural number has no `EcRealLit`, by
hand or otherwise. Nothing decodable is lost: `decodeRealLit` accepts the
injection of a non-negative integer literal and rejects every other real
operator. A fragment admitting `q / 2 ^ n` gives `EcRealLit` a second constructor
and `EcRealLit.value` a second arm, and the invariant survives that. -/
structure EcRealLit where
  /-- The numeral the decoder read from the export. -/
  num : Nat
  deriving DecidableEq, Repr

/-- The bound a real literal denotes. -/
def EcRealLit.value (r : EcRealLit) : ℝ≥0∞ := (r.num : ℝ≥0∞)

/-! ## The term layer -/

/-- Intrinsically typed terms of an imported statement. Beyond the expression
fragment of `Ast.lean` these have the two leaves a statement needs: a module
global read at a memory, and the result of the enclosing judgement. -/
inductive EcTerm : EcTy → Type where
  /-- A logical variable bound by a quantifier or a `let`. -/
  | var (t : EcTy) (x : String) : EcTerm t
  /-- A literal of the interpreted type. -/
  | lit {t : EcTy} (v : t.interp) : EcTerm t
  /-- A program expression of the imported-program fragment, read against the
  ambient valuation of logical variables. -/
  | ofExpr {t : EcTy} (e : EcExpr t) : EcTerm t
  /-- The module global `g` read at the memory `m`, EasyCrypt's `g{m}`. -/
  | glob (g : EcGlobal) (m : EcMemRef) : EcTerm g.ty
  /-- The result of the enclosing judgement at the side `s`, EasyCrypt's `res`. -/
  | res (t : EcTy) (s : EcSide) : EcTerm t
  /-- The abstract operator declared at `path` with signature `s`, applied to
  `arg`. The argument type of `s` is the declaration's arguments as a
  right-nested product, so a nullary operator has `s.arg = EcTy.unit` and is
  applied at the unit literal. The realization is read from the ambient `OpEnv`
  (`Params.lean`), which `EcForm.allOp` binds. -/
  | opApp (path : String) (s : EcSig) (arg : EcTerm s.arg) : EcTerm s.res
  /-- Boolean negation. -/
  | bnot (e : EcTerm .bool) : EcTerm .bool
  /-- Boolean conjunction. -/
  | band (a b : EcTerm .bool) : EcTerm .bool
  /-- Boolean exclusive-or. -/
  | bxor (a b : EcTerm .bool) : EcTerm .bool
  /-- Decidable equality at any type code, as a `bool`-valued term. -/
  | beq {t : EcTy} (a b : EcTerm t) : EcTerm .bool
  /-- Pair construction. -/
  | pair {a b : EcTy} (x : EcTerm a) (y : EcTerm b) : EcTerm (.prod a b)
  /-- First projection. -/
  | fst {a b : EcTy} (p : EcTerm (.prod a b)) : EcTerm a
  /-- Second projection. -/
  | snd {a b : EcTy} (p : EcTerm (.prod a b)) : EcTerm b
  /-- Addition on `fin n`, wrapping. -/
  | finAdd {n : Nat} {pos : 0 < n} (a b : EcTerm (.fin n pos)) : EcTerm (.fin n pos)
  /-- Integer addition. -/
  | intAdd (a b : EcTerm .int) : EcTerm .int
  /-- Integer multiplication. -/
  | intMul (a b : EcTerm .int) : EcTerm .int
  /-- Integer negation. -/
  | intOpp (a : EcTerm .int) : EcTerm .int
  /-- Euclidean division, EasyCrypt's `edivz`: the quotient and the remainder as
  a pair, the remainder taken in `[0, |d|)`, and `(0, m)` at divisor zero. `%/`
  and `%%` are its projections. -/
  | intEdivz (a b : EcTerm .int) : EcTerm (.prod .int .int)
  /-- Integer order comparison. The strict order has no constructor of its own:
  `x < y` is the negation of the reversed comparison, the shape `EcExpr` reads it
  at too. -/
  | intLe (a b : EcTerm .int) : EcTerm .bool
  /-- Whether a key is bound in a finite map, EasyCrypt's `dom`. -/
  | mapMem {a b : EcTy} (m : EcTerm (.map a b)) (k : EcTerm a) : EcTerm .bool
  /-- List cons, EasyCrypt's `::`. -/
  | listCons {a : EcTy} (x : EcTerm a) (l : EcTerm (.list a)) : EcTerm (.list a)
  /-- The length of a list as an integer, EasyCrypt's `size`. -/
  | listSize {a : EcTy} (l : EcTerm (.list a)) : EcTerm .int
  /-- Membership in a list, EasyCrypt's `mem`. -/
  | listMem {a : EcTy} (l : EcTerm (.list a)) (x : EcTerm a) : EcTerm .bool
  /-- Membership in a finite set, EasyCrypt's `mem`. -/
  | fsetMem {a : EcTy} (s : EcTerm (.fset a)) (x : EcTerm a) : EcTerm .bool
  /-- A conditional term. -/
  | ite {t : EcTy} (c : EcTerm .bool) (thn els : EcTerm t) : EcTerm t
  /-- A `let` binding of a logical variable. -/
  | letIn {t' t : EcTy} (x : String) (v : EcTerm t') (body : EcTerm t) : EcTerm t

/-! ### Leaf recognizers

Two queries on a term, each a `match` at a **quantified** type index. `EcTerm.glob`
is indexed by `g.ty`, a projection out of its own field, so a `match` at a fixed
index — as a pattern under `EcForm.holds`, or a function on `EcTerm .bool` — makes
the dependent pattern matcher solve `EcTy.bool = g.ty` with `g` a fresh variable,
which it cannot. Quantifying the index makes the same equation an assignment.
These are how a caller reads a leaf back out of a term: the golden `#guard`s of
`FormJson.lean` use them to pin a decoded global read and a decoded literal. -/

/-- The global a term reads and the memory it reads it at, when the term is a
global read. -/
def EcTerm.globRead : {t : EcTy} → EcTerm t → Option (EcGlobal × EcMemRef)
  | _, .glob g m => some (g, m)
  | _, _ => none

/-- The value a term is, when the term is a literal. -/
def EcTerm.litValue : {t : EcTy} → EcTerm t → Option t.interp
  | _, .lit v => some v
  | _, _ => none

/-- The operator path and signature a term applies, when the term is an
application of an abstract operator. `EcTerm.opApp` is indexed by `s.res`, a
projection out of its own field, so this is the query a caller reads the leaf
back with, for the reason `EcTerm.globRead` gives. -/
def EcTerm.opAppOf : {t : EcTy} → EcTerm t → Option (String × EcSig)
  | _, .opApp path s _ => some (path, s)
  | _, _ => none

/-! ### The arguments of an applied operator

An operator of `n` arguments is read at a signature whose argument code is the
arguments' codes as a right-nested product, the nesting `EcProcAt.params` and
`bindParams` fix for a procedure's formals. `EcTerm.nestArgs` is the term side of
that nesting, so an operator of `n` arguments and a procedure of `n` formals
carry their arguments the same way and a declaration's `EcSig` is read exactly as
a procedure's is. -/

/-- The arguments of an applied operator, in source order, as one term: a single
argument at its own type code, and two or more as the right-nested pair
`(a₁, (a₂, …))`. The code of the result is the right-nested product of the
arguments' codes, which is the argument code of the signature an `n`-argument
declaration has. -/
def EcTerm.nestArgs : ((t : EcTy) × EcTerm t) → List ((t : EcTy) × EcTerm t) →
    (t : EcTy) × EcTerm t
  | a, [] => a
  | a, b :: rest =>
      let r := EcTerm.nestArgs b rest
      Sigma.mk (EcTy.prod a.1 r.1) (EcTerm.pair a.2 r.2)

-- One argument keeps its own code, and three nest to the right.
#guard (EcTerm.nestArgs ⟨.bool, .lit (t := .bool) true⟩ []).1 == EcTy.bool

#guard (EcTerm.nestArgs ⟨.bool, .lit (t := .bool) true⟩
          [⟨.int, .lit (t := .int) 0⟩, ⟨.unit, .lit (t := .unit) ()⟩]).1
        == EcTy.prod .bool (.prod .int .unit)

/-! ### Operator occurrences

The abstract operators a term reads, each with the signature it is read at. This
is what `EcForm.opsOf` collects through a formula, and what
`EcForm.assembleParams` binds. -/

/-- The abstract operators a term applies, in occurrence order, with
repetitions. -/
def EcTerm.opsOf : {t : EcTy} → EcTerm t → List (String × EcSig)
  | _, .var _ _ => []
  | _, .lit _ => []
  | _, .ofExpr _ => []
  | _, .glob _ _ => []
  | _, .res _ _ => []
  | _, .opApp path s arg => (path, s) :: EcTerm.opsOf arg
  | _, .bnot e => EcTerm.opsOf e
  | _, .band a b => EcTerm.opsOf a ++ EcTerm.opsOf b
  | _, .bxor a b => EcTerm.opsOf a ++ EcTerm.opsOf b
  | _, .beq a b => EcTerm.opsOf a ++ EcTerm.opsOf b
  | _, .pair x y => EcTerm.opsOf x ++ EcTerm.opsOf y
  | _, .fst p => EcTerm.opsOf p
  | _, .snd p => EcTerm.opsOf p
  | _, .finAdd a b => EcTerm.opsOf a ++ EcTerm.opsOf b
  | _, .intAdd a b => EcTerm.opsOf a ++ EcTerm.opsOf b
  | _, .intMul a b => EcTerm.opsOf a ++ EcTerm.opsOf b
  | _, .intOpp a => EcTerm.opsOf a
  | _, .intEdivz a b => EcTerm.opsOf a ++ EcTerm.opsOf b
  | _, .intLe a b => EcTerm.opsOf a ++ EcTerm.opsOf b
  | _, .mapMem m k => EcTerm.opsOf m ++ EcTerm.opsOf k
  | _, .listCons x l => EcTerm.opsOf x ++ EcTerm.opsOf l
  | _, .listSize l => EcTerm.opsOf l
  | _, .listMem l x => EcTerm.opsOf l ++ EcTerm.opsOf x
  | _, .fsetMem s x => EcTerm.opsOf s ++ EcTerm.opsOf x
  | _, .ite c thn els => EcTerm.opsOf c ++ EcTerm.opsOf thn ++ EcTerm.opsOf els
  | _, .letIn _ v body => EcTerm.opsOf v ++ EcTerm.opsOf body

/-! ## The formula and probability layers -/

mutual

/-- Formulas of an imported statement: the first-order skeleton together with the
probability comparison and the three judgement nodes. -/
inductive EcForm where
  /-- `true`. -/
  | tru
  /-- `false`. -/
  | fls
  /-- A `bool`-valued term asserted to hold. -/
  | holds (b : EcTerm .bool)
  /-- Equality of two terms at the same type code. -/
  | eqT {t : EcTy} (a b : EcTerm t)
  /-- Equality of two memories: the two heaps are equal. No decoder produces this
  node — EasyCrypt has no whole-memory equality, `={glob}` is not surface syntax,
  and `={glob M}` is expanded by the typechecker into one `eqT` per declared
  global. It is reached from a hand-written form, where it is the precondition and
  postcondition a relational judgement about heap-carrying programs needs. -/
  | memEq (m₁ m₂ : EcMemRef)
  /-- Agreement of two memories on the footprint of the globals `gs`,
  EasyCrypt's `={glob M}` for the module whose `var` declarations are `gs`. -/
  | memEqOn (gs : List EcGlobal) (m₁ m₂ : EcMemRef)
  /-- Agreement of two memories on the footprint of the module binder `name`,
  EasyCrypt's `={glob A}` for an abstract `A`. The footprint is the one the
  binder carries, since an abstract module declares no globals. -/
  | memEqOnMod (name : String) (m₁ m₂ : EcMemRef)
  /-- Negation. -/
  | not (f : EcForm)
  /-- Conjunction. -/
  | and (a b : EcForm)
  /-- Disjunction. -/
  | or (a b : EcForm)
  /-- Implication. -/
  | imp (a b : EcForm)
  /-- Logical equivalence. -/
  | iff (a b : EcForm)
  /-- A conditional formula, branching on a `bool`-valued term. -/
  | ifF (c : EcTerm .bool) (thn els : EcForm)
  /-- A `let` binding of a logical variable in a formula. -/
  | letF {t : EcTy} (x : String) (v : EcTerm t) (body : EcForm)
  /-- Universal quantification over the values of a type code. -/
  | allTy (t : EcTy) (x : String) (body : EcForm)
  /-- Existential quantification over the values of a type code. -/
  | exTy (t : EcTy) (x : String) (body : EcForm)
  /-- Universal quantification over memories, EasyCrypt's `forall &m`. -/
  | allMem (m : String) (body : EcForm)
  /-- Existential quantification over memories. -/
  | exMem (m : String) (body : EcForm)
  /-- Universal quantification over a probability parameter, the `ε` of a
  concrete-security statement. -/
  | allProb (x : String) (body : EcForm)
  /-- Universal quantification over the modules of a module type, EasyCrypt's
  `forall (A <: I)`. The procedures of the bound module answer calls made under
  the qualified prefix `name`. -/
  | allMod (name : String) (I : EcInterface) (body : EcForm)
  /-- Universal quantification over the modules of a module type restricted away
  from the footprint of the globals `gs`, EasyCrypt's `forall (A <: I{-M})` with
  `gs` the `var` declarations of `M`. The restriction is a side hypothesis on the
  bound module, not a constraint on the interface. -/
  | allModRestr (name : String) (I : EcInterface) (gs : List EcGlobal) (body : EcForm)
  /-- Universal quantification over the modules of a module type together with
  the footprint the bound module lives on, for a body that names `glob name`. An
  abstract module declares no globals, so the set of locations its procedures
  read and write is a second bound variable, and living on it is a hypothesis on
  the pair. -/
  | allModOn (name : String) (I : EcInterface) (body : EcForm)
  /-- Universal quantification over the modules of a module type restricted away
  from the footprint of the globals `gs`, together with the footprint the bound
  module lives on, for a body that names `glob name`. The restriction is both the
  disjointness of the two footprints and the hypothesis on the bound module that
  `allModRestr` carries. -/
  | allModRestrOn (name : String) (I : EcInterface) (gs : List EcGlobal) (body : EcForm)
  /-- Universal quantification over the realizations of the abstract operator
  declared at `path` with signature `s`, EasyCrypt's theory-level `op f : T.`
  read from a statement of the declaring theory. The body reads the bound
  realization through `EcTerm.opApp` at the same path and signature. -/
  | allOp (path : String) (s : EcSig) (body : EcForm)
  /-- Universal quantification over the values of the abstract constant declared
  at `path` with type `t`, EasyCrypt's theory-level `op c : t.` for a declaration
  that takes no argument. The binder ranges over `t.interp` rather than over
  `Unit → t.interp`, which is the type the source gives the declaration; the body
  reads it through `EcTerm.opApp` at the signature `⟨unit, t⟩`, which
  `FormEnv.bindConst` answers with the bound value. -/
  | allConst (path : String) (t : EcTy) (body : EcForm)
  /-- Termination of the procedure `q` at signature `s`, EasyCrypt's
  `islossless q`: the procedure's output sub-distribution has total mass one, at
  every argument and from every initial memory. -/
  | lossless (q : String) (s : EcSig)
  /-- Total mass one of the sub-distribution a term denotes, EasyCrypt's
  `is_lossless d`. -/
  | isLossless {t : EcTy} (d : EcTerm (.distr t))
  /-- A comparison between two probability expressions. -/
  | probCmp (cmp : EcCmp) (a b : EcProb)
  /-- The Hoare judgement `hoare[q(arg) : pre ==> post]`. `pre` reads the initial
  memory and `post` the final memory as the `cur` side; `post` also binds
  `res`. -/
  | hoare (q : String) (s : EcSig) (arg : EcTerm s.arg) (pre post : EcForm)
  /-- The bounded Hoare judgement `bd_hoare[q(arg) : pre ==> post] cmp bd`. -/
  | bdHoare (q : String) (s : EcSig) (arg : EcTerm s.arg) (pre post : EcForm)
      (cmp : EcCmp) (bd : EcRealLit)
  /-- The relational judgement `equiv[q₁(arg₁) ~ q₂(arg₂) : pre ==> post]`.
  `pre` and `post` read the two memories as the `left` and `right` sides, and
  `post` binds `res{1}` and `res{2}`. -/
  | equiv (q₁ : String) (s₁ : EcSig) (arg₁ : EcTerm s₁.arg)
      (q₂ : String) (s₂ : EcSig) (arg₂ : EcTerm s₂.arg) (pre post : EcForm)

/-- Probability expressions of an imported statement. -/
inductive EcProb where
  /-- `Pr[q(arg) @ m : ev]`. The event `ev` reads the final memory as the `cur`
  side and binds `res`. -/
  | pr (q : String) (s : EcSig) (arg : EcTerm s.arg) (m : EcMemRef) (ev : EcForm)
  /-- A constant probability. -/
  | const (r : EcRealLit)
  /-- A probability parameter bound by `EcForm.allProb`. -/
  | pvar (x : String)
  /-- Sum of two probability expressions. -/
  | add (a b : EcProb)
  /-- Product of two probability expressions. -/
  | mul (a b : EcProb)
  /-- Absolute difference of two probability expressions. -/
  | absDiff (a b : EcProb)

end

/-! ### Footprint occurrences

Whether a statement compares the footprint of a named module binder. This is what
decides which of the two module quantifiers a binder becomes: the footprint is a
second bound variable exactly when the body names it. A nested binder of the same
name shadows the outer one, so the search stops there. -/

mutual

/-- Whether the formula compares the footprint of the module binder `name`. -/
def EcForm.namesGlobOf (name : String) : EcForm → Bool
  | .tru => false
  | .fls => false
  | .holds _ => false
  | .eqT _ _ => false
  | .memEq _ _ => false
  | .memEqOn _ _ _ => false
  | .memEqOnMod nm _ _ => nm == name
  | .not f => EcForm.namesGlobOf name f
  | .and a b => EcForm.namesGlobOf name a || EcForm.namesGlobOf name b
  | .or a b => EcForm.namesGlobOf name a || EcForm.namesGlobOf name b
  | .imp a b => EcForm.namesGlobOf name a || EcForm.namesGlobOf name b
  | .iff a b => EcForm.namesGlobOf name a || EcForm.namesGlobOf name b
  | .ifF _ thn els => EcForm.namesGlobOf name thn || EcForm.namesGlobOf name els
  | .letF _ _ body => EcForm.namesGlobOf name body
  | .allTy _ _ body => EcForm.namesGlobOf name body
  | .exTy _ _ body => EcForm.namesGlobOf name body
  | .allMem _ body => EcForm.namesGlobOf name body
  | .exMem _ body => EcForm.namesGlobOf name body
  | .allProb _ body => EcForm.namesGlobOf name body
  | .allMod nm _ body => nm != name && EcForm.namesGlobOf name body
  | .allModRestr nm _ _ body => nm != name && EcForm.namesGlobOf name body
  | .allModOn nm _ body => nm != name && EcForm.namesGlobOf name body
  | .allModRestrOn nm _ _ body => nm != name && EcForm.namesGlobOf name body
  | .allOp _ _ body => EcForm.namesGlobOf name body
  | .allConst _ _ body => EcForm.namesGlobOf name body
  | .lossless _ _ => false
  | .isLossless _ => false
  | .probCmp _ a b => EcProb.namesGlobOf name a || EcProb.namesGlobOf name b
  | .hoare _ _ _ pre post => EcForm.namesGlobOf name pre || EcForm.namesGlobOf name post
  | .bdHoare _ _ _ pre post _ _ =>
      EcForm.namesGlobOf name pre || EcForm.namesGlobOf name post
  | .equiv _ _ _ _ _ _ pre post =>
      EcForm.namesGlobOf name pre || EcForm.namesGlobOf name post

/-- Whether the probability expression's events compare the footprint of the
module binder `name`. -/
def EcProb.namesGlobOf (name : String) : EcProb → Bool
  | .pr _ _ _ _ ev => EcForm.namesGlobOf name ev
  | .const _ => false
  | .pvar _ => false
  | .add a b => EcProb.namesGlobOf name a || EcProb.namesGlobOf name b
  | .mul a b => EcProb.namesGlobOf name a || EcProb.namesGlobOf name b
  | .absDiff a b => EcProb.namesGlobOf name a || EcProb.namesGlobOf name b

end

/-! ### The operators a statement leaves free

`EcForm.opsOf` collects the abstract operators a formula reads and does not bind.
An `allOp` binder discharges every occurrence of its own path at its own
signature, so `opsOf` of an assembled statement is empty and no operator the
statement reads reaches the ambient `OpEnv`. This is the coverage check
`assembleParams` is written against: an operator missing a binder would resolve
to the canonical inhabitant of its result code (`Params.lean`), which is not the
operator's meaning. -/

mutual

/-- The abstract operators a formula reads without binding them, in occurrence
order, with repetitions. -/
def EcForm.opsOf : EcForm → List (String × EcSig)
  | .tru => []
  | .fls => []
  | .holds b => b.opsOf
  | .eqT a b => a.opsOf ++ b.opsOf
  | .memEq _ _ => []
  | .memEqOn _ _ _ => []
  | .memEqOnMod _ _ _ => []
  | .not f => EcForm.opsOf f
  | .and a b => EcForm.opsOf a ++ EcForm.opsOf b
  | .or a b => EcForm.opsOf a ++ EcForm.opsOf b
  | .imp a b => EcForm.opsOf a ++ EcForm.opsOf b
  | .iff a b => EcForm.opsOf a ++ EcForm.opsOf b
  | .ifF c thn els => c.opsOf ++ EcForm.opsOf thn ++ EcForm.opsOf els
  | .letF _ v body => v.opsOf ++ EcForm.opsOf body
  | .allTy _ _ body => EcForm.opsOf body
  | .exTy _ _ body => EcForm.opsOf body
  | .allMem _ body => EcForm.opsOf body
  | .exMem _ body => EcForm.opsOf body
  | .allProb _ body => EcForm.opsOf body
  | .allMod _ _ body => EcForm.opsOf body
  | .allModRestr _ _ _ body => EcForm.opsOf body
  | .allModOn _ _ body => EcForm.opsOf body
  | .allModRestrOn _ _ _ body => EcForm.opsOf body
  | .allOp path s body => (EcForm.opsOf body).filter (fun e => e != (path, s))
  | .allConst path t body =>
      (EcForm.opsOf body).filter (fun e => e != (path, ⟨EcTy.unit, t⟩))
  | .lossless _ _ => []
  | .isLossless d => d.opsOf
  | .probCmp _ a b => EcProb.opsOf a ++ EcProb.opsOf b
  | .hoare _ _ arg pre post =>
      arg.opsOf ++ EcForm.opsOf pre ++ EcForm.opsOf post
  | .bdHoare _ _ arg pre post _ _ =>
      arg.opsOf ++ EcForm.opsOf pre ++ EcForm.opsOf post
  | .equiv _ _ arg₁ _ _ arg₂ pre post =>
      arg₁.opsOf ++ arg₂.opsOf ++ EcForm.opsOf pre ++ EcForm.opsOf post

/-- The abstract operators a probability expression reads without binding
them. -/
def EcProb.opsOf : EcProb → List (String × EcSig)
  | .pr _ _ arg _ ev => arg.opsOf ++ EcForm.opsOf ev
  | .const _ => []
  | .pvar _ => []
  | .add a b => EcProb.opsOf a ++ EcProb.opsOf b
  | .mul a b => EcProb.opsOf a ++ EcProb.opsOf b
  | .absDiff a b => EcProb.opsOf a ++ EcProb.opsOf b

end

/-- The list with the repetitions dropped, keeping each entry's first
occurrence. -/
def opsUnique (l : List (String × EcSig)) : List (String × EcSig) :=
  l.foldl (fun acc e => if acc.contains e then acc else acc ++ [e]) []

/-- The statement quantified over the realizations of the abstract operators it
reads: one binder per operator, in the order the statement reads them, the first
read outermost. `EcForm.opsOf` of the result is empty.

A declaration that takes no argument binds at its own type, through
`EcForm.allConst`, and not at `Unit → t.interp`: the source declares a value, and
the unit argument is an artifact of the uniform signature an operator is resolved
at. An arrow-typed declaration binds through `EcForm.allOp`. -/
def EcForm.assembleParams (f : EcForm) : EcForm :=
  (opsUnique f.opsOf).foldr
    (fun e body =>
      match e.2 with
      | ⟨.unit, t⟩ => .allConst e.1 t body
      | s => .allOp e.1 s body) f

/-- The statement of a theory's lemma: `goal` under the theory's imported
axioms, closed over the abstract operators the goal and those axioms read. The
premises nest in list order, the first outermost.

The parameter binders sit outside the premises. An imported axiom constrains the
same declarations the goal reads, so its operator reads are discharged by the
binders the goal's reads are discharged by; a premise outside the binders would
resolve its reads in the ambient environment instead (`Params.lean`).
`EcForm.opsOf` of the result is empty, which is that property. -/
def EcForm.assembleStatement (hyps : List EcForm) (goal : EcForm) : EcForm :=
  (hyps.foldr EcForm.imp goal).assembleParams

/-! ## Polymorphic statements

A statement whose source declares type parameters is a family of statements, one
per assignment of a type code to each parameter. `EcPolyForm n` is that family at
`n` parameters, and the two assembly functions are the pointwise readings of
`EcForm.assembleParams` and `EcForm.assembleStatement`: the operator binders and
the premises sit inside the type binders, because an operator's signature can
name a type parameter. -/

/-- A statement polymorphic in `n` type parameters: an `EcForm` once each
parameter is given a type code, the parameters taken in the order the source
declares them. -/
def EcPolyForm : Nat → Type
  | 0 => EcForm
  | n + 1 => EcTy → EcPolyForm n

/-- The statement at each instantiation quantified over the abstract operators it
reads. The operator binders are inside the type binders: an operator's signature
can name a type parameter, so the signature its binder ranges at is fixed only
once the parameter is. -/
def EcPolyForm.assembleParams : {n : Nat} → EcPolyForm n → EcPolyForm n
  | 0, f => EcForm.assembleParams f
  | _ + 1, f => fun a => EcPolyForm.assembleParams (f a)

/-- The statement of a theory's polymorphic lemma: at each instantiation, the
goal under the theory's imported axioms, closed over the abstract operators the
goal and those axioms read. A premise is an `EcForm` of its own, so it names no
type parameter of the goal. -/
def EcPolyForm.assembleStatement (hyps : List EcForm) :
    {n : Nat} → EcPolyForm n → EcPolyForm n
  | 0, goal => EcForm.assembleStatement hyps goal
  | _ + 1, f => fun a => EcPolyForm.assembleStatement hyps (f a)

/-- `Pr[q(arg) @ m : res]` for a `bool`-returning procedure: the probability that
the procedure returns `true`. -/
def EcProb.prTrueOf (q : String) (arg : EcTerm .unit) (m : EcMemRef) : EcProb :=
  .pr q ⟨.unit, .bool⟩ arg m (.holds (.res .bool .cur))

/-- `|Pr[q₁(arg₁) @ m : res] - Pr[q₂(arg₂) @ m : res]| cmp bd`, the shape of an
imported distinguishing bound between two `bool`-returning experiments. -/
def EcForm.prDiffCmp (cmp : EcCmp) (q₁ : String) (arg₁ : EcTerm .unit)
    (q₂ : String) (arg₂ : EcTerm .unit) (m : EcMemRef) (bd : EcProb) : EcForm :=
  .probCmp cmp (.absDiff (EcProb.prTrueOf q₁ arg₁ m) (EcProb.prTrueOf q₂ arg₂ m)) bd

/-! ## Coverage checks

The checks below are the property `assembleParams` exists for: the assembled
statement reads no operator that it does not itself bind. They are `#guard`
commands over hand-written literals; `opsOf` and `assembleParams` are ordinary
structural recursions, so a `decide` would serve equally, and `#guard` matches
how the rest of the importer's checks are written (`AGENTS.md`). -/

section CoverageGuard

/-- `is_lossless d` for an abstract nullary distribution operator: one operator
occurrence, at a signature whose argument is `unit`. -/
private def guardLosslessForm : EcForm :=
  .isLossless (.opApp "Top.T.d" ⟨.unit, .distr (.opaque "Top.T.t")⟩ (.lit (t := .unit) ()))

-- The operator occurrence is collected at the signature it is read at.
#guard EcForm.opsOf guardLosslessForm
  == [("Top.T.d", ⟨EcTy.unit, EcTy.distr (EcTy.opaque "Top.T.t")⟩)]

-- Assembling binds it, and the assembled statement reads no free operator.
#guard EcForm.opsOf (EcForm.assembleParams guardLosslessForm) == []

-- The assembled shape is one binder at the collected path, and the declaration
-- takes no argument, so the binder ranges over the declared type itself.
#guard (match EcForm.assembleParams guardLosslessForm with
        | .allConst "Top.T.d" (.distr (.opaque "Top.T.t")) (.isLossless d) =>
            d.opAppOf == some ("Top.T.d", ⟨EcTy.unit, EcTy.distr (EcTy.opaque "Top.T.t")⟩)
        | _ => false)

-- Two occurrences of one operator get one binder, and it discharges both.
#guard (match EcForm.assembleParams (.and guardLosslessForm guardLosslessForm) with
        | .allConst "Top.T.d" _ (.and (.isLossless _) (.isLossless _)) => true
        | _ => false)

#guard EcForm.opsOf
    (EcForm.assembleParams (.and guardLosslessForm guardLosslessForm)) == []

/-- A read of an arrow-typed declaration, at the signature its declaration gives
it: one argument at the `bool` code. -/
private def guardArrowForm : EcForm :=
  .holds (.opApp "Top.T.g" ⟨.bool, .bool⟩ (.lit (t := .bool) true))

-- An arrow-typed declaration keeps the signature binder, since its realization is
-- a function and no single value stands for it.
#guard (match EcForm.assembleParams guardArrowForm with
        | .allOp "Top.T.g" ⟨.bool, .bool⟩ (.holds _) => true
        | _ => false)

#guard EcForm.opsOf (EcForm.assembleParams guardArrowForm) == []

-- The two binders are told apart by the declaration's argument type, so a
-- statement reading both gets one of each and reads no free operator.
#guard EcForm.opsOf
    (EcForm.assembleParams (.and guardLosslessForm guardArrowForm)) == []

#guard (match EcForm.assembleParams (.and guardLosslessForm guardArrowForm) with
        | .allConst "Top.T.d" _ (.allOp "Top.T.g" _ (.and _ _)) => true
        | _ => false)

-- A goal stated under one imported axiom binds the operator both read once, and
-- the premise is inside that binder.
#guard (match EcForm.assembleStatement [guardLosslessForm] guardLosslessForm with
        | .allConst "Top.T.d" (.distr (.opaque "Top.T.t"))
            (.imp (.isLossless _) (.isLossless _)) => true
        | _ => false)

#guard EcForm.opsOf
    (EcForm.assembleStatement [guardLosslessForm] guardLosslessForm) == []

-- An axiom reading a declaration the goal does not read is bound too, so no read
-- of a premise reaches the ambient environment.
#guard (match EcForm.assembleStatement [guardArrowForm] guardLosslessForm with
        | .allOp "Top.T.g" _
            (.allConst "Top.T.d" _ (.imp (.holds _) (.isLossless _))) => true
        | _ => false)

#guard EcForm.opsOf
    (EcForm.assembleStatement [guardArrowForm] guardLosslessForm) == []

-- The premises nest in list order, the first outermost.
#guard (match EcForm.assembleStatement [guardArrowForm, guardLosslessForm] .tru with
        | .allOp "Top.T.g" _ (.allConst "Top.T.d" _
            (.imp (.holds _) (.imp (.isLossless _) .tru))) => true
        | _ => false)

-- An empty axiom list is the parameter-only assembly.
#guard (match EcForm.assembleStatement [] guardLosslessForm with
        | .allConst "Top.T.d" _ (.isLossless _) => true
        | _ => false)

/-- A statement polymorphic in one type parameter: an abstract nullary
distribution operator at the parameter's code, asserted lossless. -/
private def guardPolyForm : EcPolyForm 1 := fun a =>
  .isLossless (.opApp "Top.T.d" ⟨.unit, .distr a⟩ (.lit (t := .unit) ()))

-- The operator's signature names the type parameter, so the binder assembling
-- fixes ranges at the signature the instantiation gives it.
#guard (match EcPolyForm.assembleParams guardPolyForm EcTy.bool with
        | .allConst "Top.T.d" (.distr .bool) (.isLossless _) => true
        | _ => false)

#guard (match EcPolyForm.assembleParams guardPolyForm EcTy.int with
        | .allConst "Top.T.d" (.distr .int) (.isLossless _) => true
        | _ => false)

-- The coverage property holds at each instantiation.
#guard EcForm.opsOf (EcPolyForm.assembleParams guardPolyForm EcTy.bool) == []

#guard EcForm.opsOf (EcPolyForm.assembleParams guardPolyForm EcTy.int) == []

-- A premise sits inside the type binder and keeps the codes its own statement
-- reads, while the goal takes the bound code.
#guard (match EcPolyForm.assembleStatement [guardLosslessForm] guardPolyForm EcTy.bool with
        | .allConst "Top.T.d" (.distr (.opaque "Top.T.t"))
            (.allConst "Top.T.d" (.distr .bool)
              (.imp (.isLossless _) (.isLossless _))) => true
        | _ => false)

#guard EcForm.opsOf
    (EcPolyForm.assembleStatement [guardLosslessForm] guardPolyForm EcTy.bool) == []

end CoverageGuard

end CatCrypt.Crypto.EasyCryptImport

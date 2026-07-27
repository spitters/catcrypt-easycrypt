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
  fragment, `if`, and `let`. An `EcExpr` embeds directly (`ofExpr`).
* `EcProb` — the probability layer: `Pr[q(arg) @ &m : ev]`, constants, a
  probability-valued parameter, sum, product, and absolute difference.
* `EcForm` — the formula layer: the first-order skeleton (the connectives,
  quantifiers over an `EcTy`, over a memory, over a probability parameter and
  over a module type — restricted or not, and carrying the bound module's
  footprint or not — term equality, memory equality, footprint agreement, `if`,
  `let`) together with the five modal nodes: a probability comparison, a Hoare
  judgement, a bounded Hoare judgement, a relational (equiv) judgement, and a
  losslessness assertion.

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
* **Higher-order quantification** over operators or distributions: the quantifier
  nodes range over an `EcTy`, a memory, a probability, or a module type only.
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
  | finAdd {n : Nat} (a b : EcTerm (.fin n)) : EcTerm (.fin n)
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
  /-- Termination of the procedure `q` at signature `s`, EasyCrypt's
  `islossless q`: the procedure's output sub-distribution has total mass one, at
  every argument and from every initial memory. -/
  | lossless (q : String) (s : EcSig)
  /-- A comparison between two probability expressions. -/
  | probCmp (cmp : EcCmp) (a b : EcProb)
  /-- The Hoare judgement `hoare[q(arg) : pre ==> post]`. `pre` reads the initial
  memory and `post` the final memory as the `cur` side; `post` also binds
  `res`. -/
  | hoare (q : String) (s : EcSig) (arg : EcTerm s.arg) (pre post : EcForm)
  /-- The bounded Hoare judgement `bd_hoare[q(arg) : pre ==> post] cmp bd`. -/
  | bdHoare (q : String) (s : EcSig) (arg : EcTerm s.arg) (pre post : EcForm)
      (cmp : EcCmp) (bd : ℝ≥0∞)
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
  | const (r : ℝ≥0∞)
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
  | .lossless _ _ => false
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

/-- `Pr[q(arg) @ m : res]` for a `bool`-returning procedure: the probability that
the procedure returns `true`. -/
def EcProb.prTrueOf (q : String) (arg : EcTerm .unit) (m : EcMemRef) : EcProb :=
  .pr q ⟨.unit, .bool⟩ arg m (.holds (.res .bool .cur))

/-- `|Pr[q₁(arg₁) @ m : res] - Pr[q₂(arg₂) @ m : res]| cmp bd`, the shape of an
imported distinguishing bound between two `bool`-returning experiments. -/
def EcForm.prDiffCmp (cmp : EcCmp) (q₁ : String) (arg₁ : EcTerm .unit)
    (q₂ : String) (arg₂ : EcTerm .unit) (m : EcMemRef) (bd : EcProb) : EcForm :=
  .probCmp cmp (.absDiff (EcProb.prTrueOf q₁ arg₁ m) (EcProb.prTrueOf q₂ arg₂ m)) bd

end CatCrypt.Crypto.EasyCryptImport

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.EasyCryptImport.Form
import CatCrypt.Crypto.EasyCryptImport.Lower
import CatCrypt.Crypto.EasyCryptImport.Params
import CatCrypt.Crypto.EasyCryptImport.Restrictions
import CatCryptCore.Unary.Event
import CatCryptCore.Crypto.SDist
import CatCryptCore.Crypto.EasyCryptBridge

/-!
# EasyCrypt import: imported statements as CatCrypt propositions

This module translates the statement syntax of `Form.lean` into CatCrypt
propositions. An imported EasyCrypt lemma therefore arrives as a **Lean goal**:
`importedProp ρ f` is a `Prop`, and closing it is an ordinary CatCrypt proof
obligation, discharged with the pRHL rules, the advantage lemmas and the tactics
the rest of the library provides.

## Imported statements are goals, never assertions

A generated file states an imported lemma as

```lean
def someImportedLemma : Prop := importedProp ρ form
```

and nothing more. It never states `theorem someImportedLemma : … := proof`, and
it never introduces an axiom: an EasyCrypt proof is not a Lean proof, so
asserting the statement would import the *claim* while pretending to import the
*evidence*. The proof is left to a human, working against the generated `Prop`.

The translation is total — every `EcForm` denotes a proposition — and it is total
because the fragment was cut to what CatCrypt can state: a form EasyCrypt can
write but CatCrypt cannot express has no `EcForm` constructor at all, rather than
a constructor mapped to something weaker that merely typechecks (`Form.lean` lists
the omissions and their reasons). `EcForm.tru` translates to `True` because
EasyCrypt's `true` is the source's own trivial formula, used for example as the
precondition of a Hoare judgement; no other node has a trivial image.

## The translation is unverified and in the trust base

No theorem here relates EasyCrypt's semantics to CatCrypt's. `transForm` is a
*definition of intent*: it says which CatCrypt proposition the importer takes an
EasyCrypt judgement to mean. A mistranslation would produce a well-formed Lean
goal about the wrong thing, and no proof in this repository would detect it.
Anything proved through this route depends on the translation being right, in
addition to the usual dependence on the lowering (`Lower.lean`) and on the
exporter. The worked examples are the available evidence:
`Examples/FormImport.lean` exhibits imported forms whose translation is
definitionally the statement of a theorem CatCrypt proves independently, and
`Examples/OTPEquivImport.lean` does the same for a form decoded from an
exporter fixture rather than written by hand.

## Targets

| form | CatCrypt target | notes |
| --- | --- | --- |
| `Pr[q(arg) @ m : ev]` | `prEventComp` | `prTrue` when `ev` is `res`, by `prEventComp_res_eq_prTrue` |
| `hoare[q(arg) : pre ==> post]` | `pHoare` (`Unary/Judgment.lean`) | |
| `bd_hoare[q(arg) : pre ==> post] cmp bd` | `prEventComp … cmp bd` under `pre` | all three EasyCrypt comparisons are expressible |
| `equiv[q₁ ~ q₂ : pre ==> post]` | `pRHL` = `rHoare` | |
| `\|Pr[…] - Pr[…]\| ≤ ε` | `absDiff` of two `prEventComp` | see below |
| `forall (A <: I{-M})` | `∀ M, ModuleRespectsLocs (globLocs gs) M → …` | `gs` the `var` declarations of `M` |
| `forall (A <: I{-M})`, body naming `glob A` | `∀ M L, Disjoint L (globLocs gs) → ModuleRespectsOn L M → ModuleRespectsLocs (globLocs gs) M → …` | see below |
| `={glob M}` for a concrete `M` | `agreeOn (globLocs gs)` | |
| `={glob A}` for a bound `A` | `agreeOn L` with `L` the binder's footprint | |
| `islossless q` | `ProcLossless` | |
| `is_lossless d` | `SDistr.mass … = 1` | the term's sub-distribution |
| `op f : A -> B.` read by the statement | `∀ f : s.arg.interp → s.res.interp, …` | see below |
| `op c : t.` read by the statement | `∀ v : t.interp, …` | see below |
| `lemma l ['a] : φ.` | `∀ a : EcTy, …` | one binder per type parameter, outermost |

An abstract operator of the theory a statement comes from is a parameter of the
statement: `allOp` binds one realization per declared operator, at the signature
the declaration gives it, and `EcTerm.opApp` at that path and signature reads the
bound realization back. A declaration of no arguments binds at its own type
instead (`allConst`), since that is the type the source gives it; the read stays
at the uniform signature `⟨unit, t⟩` and `FormEnv.bindConst` answers it with the
bound value (`evalTerm_opApp_bindConst`). An imported statement of a declaring theory therefore
reads "for every realization of the operators it names, `φ`". The environment the
realizations live in is `OpEnv` (`Params.lean`), and the statement binds every
path it reads (`EcForm.opsOf`, `EcForm.assembleParams`), so no read resolves
against `OpEnv.empty`, whose answer is the canonical inhabitant of the result code
rather than the operator's meaning.

A statement the source declares type parameters for is a family of statements,
one per assignment of a type code to each parameter (`EcPolyForm`), and
`importedPropPoly` binds the codes outside everything else: an operator's
signature can name a type parameter, so the signature an operator binder ranges
at is fixed only once the parameter is.

The realizations a theory's lemma speaks about are the ones its axioms admit, so
the goal of a lemma carries those axioms as premises inside the binders
(`EcForm.assembleStatement`). The premise reading needs no translation function of
its own: the premises are `EcForm.imp` nodes of the assembled statement, and
`importedProp` translates them where they stand.

An abstract module has no declared globals, so the set of locations its
procedures read and write is a second bound variable of the module quantifier:
`allModOn` and `allModRestrOn` bind a module `M` and a footprint `L` together,
under the hypothesis `ModuleRespectsOn L M` that `M` lives on `L`. This is what
`glob A` names in EasyCrypt — a fixed but unknown set of variables — and the
restriction `A{-M}` becomes the disjointness of `L` from `M`'s footprint
alongside the `ModuleRespectsLocs` hypothesis the unrestricted form carries. A
`ModuleImpl` is an arbitrary family of computations, so the three hypotheses are
what cut the quantifier down to the modules an EasyCrypt binder ranges over; each
sits to the left of the implication, and `={glob A}` itself stays where the
source puts it, as the precondition of the judgement.

A module restriction is a hypothesis on the bound module and not a constraint on
its interface (`Restrictions.lean`): `A{-M}` becomes `ModuleRespectsLocs` on the
quantified `ModuleImpl` and `islossless A.f` becomes `ProcLossless` on the
procedure it names.

An imported distinguishing bound translates **structurally**, to an `absDiff` of
two probabilities at the memory the form names, and not directly to `Advantage`,
`AdvantageA` or `sdist`. Each of those three would silently change the statement:
`Advantage` fixes the initial heap to `Heap.empty`, `AdvantageA` additionally
post-composes a distinguisher that the imported form does not mention, and
`sdist` takes a supremum over all distinguishers and all initial heaps. The
structural translation says exactly what the source says, and the two named
bridges below say what extra quantification is needed to reach the other forms:
`advantage_eq_absDiff_prTrue` at the empty heap, and `sdist_le_of_forall_absDiff`
once the form is quantified over both a memory and a post-composed distinguisher.

## Memory ↔ heap

An EasyCrypt memory is the whole program state: the global variables of every
module in scope, plus the locals of the procedures in scope. A CatCrypt `Heap`
holds only globals, keyed by location id, each stored through a chosen injection
of its type into `Nat`. The correspondence the translation uses is therefore
**globals-only**: a memory is a `Heap`, and `g{&m}` is `Heap.gget` at
`EcGlobal.loc g`, the same cell the program lowering reads (`Lower.lean`). Its
limits:

* a procedure-local program variable is not in the heap at all, so it has no term
  (`Form.lean`); the result of a judgement is available because the judgement
  binds it;
* a global whose type has no `EcTy` code has no `EcGlobal` (`Ty.lean`);
* `EcForm.memEq` is heap equality and `EcForm.memEqOn` / `EcForm.memEqOnMod` are
  agreement on a footprint (`agreeOn`); none of the three is a value-level
  `glob M`;
* the argument of a `hoare`, `bd_hoare` or `equiv` node is evaluated in the
  ambient environment, because `pHoare` and `rHoare` fix the computation before
  quantifying over the initial heap. A judgement whose argument reads its own
  initial memory is outside the fragment; the EasyCrypt idiom
  `forall a, hoare[f(a) : …]` is `allTy` around the judgement and is in the
  fragment. A `Pr[…]` node names its memory explicitly, so its argument does read
  that memory.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.EasyCryptImport

open CatCrypt.Core CatCrypt.Prob CatCrypt.Relational CatCrypt.Unary CatCrypt.Crypto
open CatCrypt.Crypto.EasyCryptBridge
open scoped ENNReal

/-! ## The translation environment -/

/-- The environment a form is translated against. It carries the four kinds of
binding a form can make — logical variables, memories, probability parameters and
modules — together with the memories and results the enclosing judgement binds.

`locals` is the same valuation the program lowering threads (`Lower.lean`), so an
`EcTerm.ofExpr` reads exactly what the corresponding program expression reads.
`procs` is the resolution environment the judgement and probability nodes look
their procedures up in, so a form and the program it talks about resolve calls the
same way. -/
structure FormEnv where
  /-- The logical variables in scope. -/
  locals : Env
  /-- The memories bound by `allMem` / `exMem`. -/
  mems : String → Heap
  /-- The probability parameters bound by `allProb`. -/
  probs : String → ℝ≥0∞
  /-- The left memory of the enclosing relational judgement. -/
  memLeft : Heap
  /-- The right memory of the enclosing relational judgement. -/
  memRight : Heap
  /-- The ambient memory of the enclosing unary judgement or probability event. -/
  memCur : Heap
  /-- The result of the enclosing relational judgement on the left. -/
  resLeft : EcVal
  /-- The result of the enclosing relational judgement on the right. -/
  resRight : EcVal
  /-- The result of the enclosing unary judgement or probability event. -/
  resCur : EcVal
  /-- The environment qualified procedure calls resolve against. -/
  procs : ProcEnv
  /-- The realization of the abstract operators the statement reads, bound by
  `EcForm.allOp` and read by `EcTerm.opApp`. -/
  ops : OpEnv
  /-- The procedures a module binder brings into scope beyond the bound module
  itself. A statement that applies a functor to the module it binds names the
  image `F(A)` by a path of its own, and the importer has no functor decoder
  (`AGENTS.md`), so the image is supplied here: `bindMod` binds the module and
  then applies `functorImages name` to the resulting environment. -/
  functorImages : String → ProcEnv → ProcEnv
  /-- The footprint each module binder in scope lives on, keyed by the binder's
  name. It is bound by `allModOn` and `allModRestrOn`, and read by the footprint
  comparison `memEqOnMod`. -/
  modFootprints : String → LocSet

/-- The environment an imported statement is translated in: nothing bound, calls
resolved against `ρ`. Every binding a form uses is made by the form's own
quantifiers and judgement nodes. -/
noncomputable def initialFormEnv (ρ : ProcEnv) : FormEnv where
  locals := emptyEnv
  mems := fun _ => Heap.empty
  probs := fun _ => 0
  memLeft := Heap.empty
  memRight := Heap.empty
  memCur := Heap.empty
  resLeft := EcVal.nil
  resRight := EcVal.nil
  resCur := EcVal.nil
  procs := ρ
  ops := OpEnv.empty
  functorImages := fun _ e => e
  modFootprints := fun _ => ∅

/-- The heap a memory reference denotes. -/
def FormEnv.mem (ρ : FormEnv) : EcMemRef → Heap
  | .named m => ρ.mems m
  | .side .left => ρ.memLeft
  | .side .right => ρ.memRight
  | .side .cur => ρ.memCur

/-- The result value a side tag denotes. -/
def FormEnv.resOf (ρ : FormEnv) : EcSide → EcVal
  | .left => ρ.resLeft
  | .right => ρ.resRight
  | .cur => ρ.resCur

/-- Bind a logical variable. -/
def FormEnv.bindVar (ρ : FormEnv) (x : String) (v : EcVal) : FormEnv :=
  { ρ with locals := ρ.locals.update x v }

/-- Bind a memory name. -/
def FormEnv.bindMem (ρ : FormEnv) (m : String) (h : Heap) : FormEnv :=
  { ρ with mems := fun y => if y = m then h else ρ.mems y }

/-- Bind a probability parameter. -/
def FormEnv.bindProb (ρ : FormEnv) (x : String) (r : ℝ≥0∞) : FormEnv :=
  { ρ with probs := fun y => if y = x then r else ρ.probs y }

/-- Bind the realization `f` of the abstract operator declared at `path` with
signature `s`, so that `EcTerm.opApp path s` reads `f`. -/
def FormEnv.bindOp (ρ : FormEnv) (path : String) {s : EcSig}
    (f : s.arg.interp → s.res.interp) : FormEnv :=
  { ρ with ops := ρ.ops.bindOp path f }

/-- Bind the value `v` of the abstract constant declared at `path` with type `t`,
so that `EcTerm.opApp path ⟨unit, t⟩` reads `v`. -/
def FormEnv.bindConst (ρ : FormEnv) (path : String) (t : EcTy) (v : t.interp) :
    FormEnv :=
  { ρ with ops := ρ.ops.bindConst path t v }

/-- Bind a module under the prefix `name`, so that a call to the cross-path
`name./p` — the name the exporter writes for a procedure of the bound module —
resolves to the module's implementation of `p`, and then extend the environment
with the functor images the statement names. -/
noncomputable def FormEnv.bindMod (ρ : FormEnv) (name : String) {I : EcInterface}
    (M : ModuleImpl I) : FormEnv :=
  { ρ with procs := ρ.functorImages name (ρ.procs.bindModuleX name M) }

/-- Bind a module under the prefix `name`, together with the footprint `L` it
lives on, which the footprint comparison `memEqOnMod name` reads back. -/
noncomputable def FormEnv.bindModOn (ρ : FormEnv) (name : String) {I : EcInterface}
    (M : ModuleImpl I) (L : LocSet) : FormEnv :=
  { ρ.bindMod name M with
    modFootprints := fun y => if y = name then L else ρ.modFootprints y }

/-! ## Terms -/

/-- Evaluation of a term. Total: a term carries the code of its type, so every
node has a value. -/
noncomputable def evalTerm : {t : EcTy} → EcTerm t → FormEnv → t.interp
  | _, .var t x, ρ => ρ.locals.read t x
  | _, .lit v, _ => v
  | _, .ofExpr e, ρ => evalExpr e ρ.locals
  | _, .glob g m, ρ => (ρ.mem m).gget g.loc
  | _, .res t s, ρ => (ρ.resOf s).get t
  | _, .opApp path s arg, ρ => ρ.ops path s (evalTerm arg ρ)
  | _, .app (a := a) (b := b) f x, ρ =>
      (show a.interp → b.interp from evalTerm f ρ) (evalTerm x ρ)
  | _, .bnot e, ρ => !(evalTerm e ρ)
  | _, .band a b, ρ => (evalTerm a ρ) && (evalTerm b ρ)
  | _, .bxor a b, ρ => xor (evalTerm a ρ) (evalTerm b ρ)
  | _, .beq (t := u) a b, ρ =>
      -- The form layer is proof-only and this evaluation is already
      -- noncomputable, so equality at a code outside `hasEq` is decided
      -- classically here rather than gated as in `evalExpr`.
      letI := Classical.decEq u.interp
      decide (evalTerm a ρ = evalTerm b ρ)
  | _, .pair x y, ρ => (evalTerm x ρ, evalTerm y ρ)
  | _, .fst p, ρ => (evalTerm p ρ).1
  | _, .snd p, ρ => (evalTerm p ρ).2
  | _, .finAdd (n := n) a b, ρ =>
      (show Fin n from evalTerm a ρ) + (show Fin n from evalTerm b ρ)
  | _, .intAdd a b, ρ =>
      (show Int from evalTerm a ρ) + (show Int from evalTerm b ρ)
  | _, .intMul a b, ρ =>
      (show Int from evalTerm a ρ) * (show Int from evalTerm b ρ)
  | _, .intOpp a, ρ => -(show Int from evalTerm a ρ)
  | _, .intEdivz a b, ρ =>
      (Int.ediv (show Int from evalTerm a ρ) (show Int from evalTerm b ρ),
       Int.emod (show Int from evalTerm a ρ) (show Int from evalTerm b ρ))
  | _, .intAbsz a, ρ => (Int.natAbs (show Int from evalTerm a ρ) : Int)
  | _, .intGcd a b, ρ =>
      (Int.gcd (show Int from evalTerm a ρ) (show Int from evalTerm b ρ) : Int)
  | _, .intLe a b, ρ =>
      decide ((show Int from evalTerm a ρ) ≤ (show Int from evalTerm b ρ))
  -- The three membership tests answer `false` at an element code without
  -- decidable equality, the value `evalExpr` answers with there.
  | _, .mapMem (a := a) (b := b) m k, ρ =>
      if h : a.hasEq = true then
        EcTy.mapMem (a := a) (b := b) (evalTerm m ρ) (evalTerm k ρ) h
      else false
  | _, .listCons (a := a) x l, ρ =>
      EcTy.listCons (a := a) (evalTerm x ρ) (evalTerm l ρ)
  | _, .listSize (a := a) l, ρ => EcTy.listSize (a := a) (evalTerm l ρ)
  | _, .listMem (a := a) l x, ρ =>
      if h : a.hasEq = true then
        EcTy.listMem (a := a) (evalTerm l ρ) (evalTerm x ρ) h
      else false
  | _, .fsetMem (a := a) s x, ρ =>
      if h : a.hasEq = true then
        EcTy.fsetMem (a := a) (evalTerm s ρ) (evalTerm x ρ) h
      else false
  | _, .ite c thn els, ρ =>
      if (show Bool from evalTerm c ρ) then evalTerm thn ρ else evalTerm els ρ
  | _, .letIn (t' := t') x v body, ρ => evalTerm body (ρ.bindVar x ⟨t', evalTerm v ρ⟩)

@[simp] theorem evalTerm_var (t : EcTy) (x : String) (ρ : FormEnv) :
    evalTerm (.var t x) ρ = ρ.locals.read t x := rfl

@[simp] theorem evalTerm_app {a b : EcTy} (f : EcTerm (.arrow a b)) (x : EcTerm a)
    (ρ : FormEnv) :
    evalTerm (.app f x) ρ
      = (show a.interp → b.interp from evalTerm f ρ) (evalTerm x ρ) := rfl

@[simp] theorem evalTerm_pair {a b : EcTy} (x : EcTerm a) (y : EcTerm b) (ρ : FormEnv) :
    evalTerm (.pair x y) ρ = (evalTerm x ρ, evalTerm y ρ) := rfl

@[simp] theorem evalTerm_fst {a b : EcTy} (p : EcTerm (.prod a b)) (ρ : FormEnv) :
    evalTerm (.fst p) ρ = (evalTerm p ρ).1 := rfl

@[simp] theorem evalTerm_snd {a b : EcTy} (p : EcTerm (.prod a b)) (ρ : FormEnv) :
    evalTerm (.snd p) ρ = (evalTerm p ρ).2 := rfl

@[simp] theorem evalTerm_ofExpr {t : EcTy} (e : EcExpr t) (ρ : FormEnv) :
    evalTerm (.ofExpr e) ρ = evalExpr e ρ.locals := rfl

@[simp] theorem evalTerm_glob (g : EcGlobal) (m : EcMemRef) (ρ : FormEnv) :
    evalTerm (.glob g m) ρ = (ρ.mem m).gget g.loc := rfl

/-- A global read at a finite code, in the finite-typed vocabulary: `Heap.gget`
at the global's cell is `Heap.get` at the `Location` that cell also is. -/
theorem evalTerm_glob_finLoc (g : EcGlobal) (hfin : g.ty.isFin = true) (m : EcMemRef)
    (ρ : FormEnv) :
    evalTerm (.glob g m) ρ = (ρ.mem m).get (g.finLoc hfin) :=
  Heap.gget_ofLocation (ρ.mem m) (g.finLoc hfin)

@[simp] theorem evalTerm_intAdd (a b : EcTerm .int) (ρ : FormEnv) :
    evalTerm (.intAdd a b) ρ
      = (show Int from evalTerm a ρ) + (show Int from evalTerm b ρ) := rfl

@[simp] theorem evalTerm_intMul (a b : EcTerm .int) (ρ : FormEnv) :
    evalTerm (.intMul a b) ρ
      = (show Int from evalTerm a ρ) * (show Int from evalTerm b ρ) := rfl

@[simp] theorem evalTerm_intOpp (a : EcTerm .int) (ρ : FormEnv) :
    evalTerm (.intOpp a) ρ = -(show Int from evalTerm a ρ) := rfl

/-- `edivz` at a realization: the Euclidean quotient and remainder. -/
@[simp] theorem evalTerm_intEdivz (a b : EcTerm .int) (ρ : FormEnv) :
    evalTerm (.intEdivz a b) ρ
      = (Int.ediv (show Int from evalTerm a ρ) (show Int from evalTerm b ρ),
         Int.emod (show Int from evalTerm a ρ) (show Int from evalTerm b ρ)) := rfl

/-- `absz` at a realization: the absolute value, as a non-negative integer. -/
@[simp] theorem evalTerm_intAbsz (a : EcTerm .int) (ρ : FormEnv) :
    evalTerm (.intAbsz a) ρ = (Int.natAbs (show Int from evalTerm a ρ) : Int) := rfl

/-- `gcd` at a realization: the greatest common divisor, as a non-negative
integer. -/
@[simp] theorem evalTerm_intGcd (a b : EcTerm .int) (ρ : FormEnv) :
    evalTerm (.intGcd a b) ρ
      = (Int.gcd (show Int from evalTerm a ρ) (show Int from evalTerm b ρ) : Int) :=
  rfl

@[simp] theorem evalTerm_intLe (a b : EcTerm .int) (ρ : FormEnv) :
    evalTerm (.intLe a b) ρ
      = decide ((show Int from evalTerm a ρ) ≤ (show Int from evalTerm b ρ)) := rfl

@[simp] theorem evalTerm_listCons {a : EcTy} (x : EcTerm a) (l : EcTerm (.list a))
    (ρ : FormEnv) :
    evalTerm (.listCons x l) ρ = EcTy.listCons (a := a) (evalTerm x ρ) (evalTerm l ρ) :=
  rfl

@[simp] theorem evalTerm_listSize {a : EcTy} (l : EcTerm (.list a)) (ρ : FormEnv) :
    evalTerm (.listSize l) ρ = EcTy.listSize (a := a) (evalTerm l ρ) := rfl

/-- Map membership at an element code with decidable equality, the codes a
decoded term carries. -/
@[simp] theorem evalTerm_mapMem {a b : EcTy} (m : EcTerm (.map a b)) (k : EcTerm a)
    (ρ : FormEnv) (hEq : a.hasEq = true := by rfl) :
    evalTerm (.mapMem m k) ρ
      = EcTy.mapMem (a := a) (b := b) (evalTerm m ρ) (evalTerm k ρ) hEq :=
  dif_pos hEq

/-- List membership at an element code with decidable equality, the codes a
decoded term carries. -/
@[simp] theorem evalTerm_listMem {a : EcTy} (l : EcTerm (.list a)) (x : EcTerm a)
    (ρ : FormEnv) (hEq : a.hasEq = true := by rfl) :
    evalTerm (.listMem l x) ρ
      = EcTy.listMem (a := a) (evalTerm l ρ) (evalTerm x ρ) hEq :=
  dif_pos hEq

/-- Finite-set membership at an element code with decidable equality, the codes a
decoded term carries. -/
@[simp] theorem evalTerm_fsetMem {a : EcTy} (s : EcTerm (.fset a)) (x : EcTerm a)
    (ρ : FormEnv) (hEq : a.hasEq = true := by rfl) :
    evalTerm (.fsetMem s x) ρ
      = EcTy.fsetMem (a := a) (evalTerm s ρ) (evalTerm x ρ) hEq :=
  dif_pos hEq

@[simp] theorem evalTerm_res (t : EcTy) (s : EcSide) (ρ : FormEnv) :
    evalTerm (.res t s) ρ = (ρ.resOf s).get t := rfl

@[simp] theorem evalTerm_opApp (path : String) (s : EcSig) (arg : EcTerm s.arg)
    (ρ : FormEnv) : evalTerm (.opApp path s arg) ρ = ρ.ops path s (evalTerm arg ρ) := rfl

/-- The realization a bound operator reads: `allOp` extends the environment at
the operator's own path and signature, and `opApp` there is the bound
function. -/
theorem evalTerm_opApp_bindOp (path : String) (s : EcSig) (arg : EcTerm s.arg)
    (f : s.arg.interp → s.res.interp) (ρ : FormEnv) :
    evalTerm (.opApp path s arg) (ρ.bindOp path f)
      = f (evalTerm arg (ρ.bindOp path f)) := by
  have h : (ρ.bindOp path f).ops path s = f := OpEnv.bindOp_same ρ.ops path f
  rw [evalTerm_opApp, h]

/-- The value a bound constant reads: `allConst` extends the environment at the
constant's path and nullary signature, and the read there is the bound value,
whatever the unit argument evaluates to. This is what makes the two layers agree:
the read keeps the uniform signature and the binder ranges over the declared
type. -/
theorem evalTerm_opApp_bindConst (path : String) (t : EcTy) (v : t.interp)
    (arg : EcTerm .unit) (ρ : FormEnv) :
    evalTerm (.opApp path ⟨.unit, t⟩ arg) (ρ.bindConst path t v) = v :=
  OpEnv.bindConst_same ρ.ops path t v _

/-! ## Comparisons -/

/-- The relation an `EcCmp` denotes on probabilities. -/
def cmpRel : EcCmp → ℝ≥0∞ → ℝ≥0∞ → Prop
  | .le, a, b => a ≤ b
  | .lt, a, b => a < b
  | .eq, a, b => a = b
  | .ge, a, b => b ≤ a
  | .gt, a, b => b < a

/-! ## Formulas and probabilities -/

mutual

/-- The CatCrypt proposition a formula denotes. -/
noncomputable def transForm : EcForm → FormEnv → Prop
  | .tru, _ => True
  | .fls, _ => False
  | .holds b, ρ => evalTerm b ρ = true
  | .eqT a b, ρ => evalTerm a ρ = evalTerm b ρ
  | .memEq m₁ m₂, ρ => ρ.mem m₁ = ρ.mem m₂
  | .memEqOn gs m₁ m₂, ρ => agreeOn (globLocs gs) (ρ.mem m₁) (ρ.mem m₂)
  | .memEqOnMod name m₁ m₂, ρ =>
      agreeOn (ρ.modFootprints name) (ρ.mem m₁) (ρ.mem m₂)
  | .not f, ρ => ¬ transForm f ρ
  | .and a b, ρ => transForm a ρ ∧ transForm b ρ
  | .or a b, ρ => transForm a ρ ∨ transForm b ρ
  | .imp a b, ρ => transForm a ρ → transForm b ρ
  | .iff a b, ρ => transForm a ρ ↔ transForm b ρ
  | .ifF c thn els, ρ =>
      if (show Bool from evalTerm c ρ) then transForm thn ρ else transForm els ρ
  | .letF (t := t) x v body, ρ => transForm body (ρ.bindVar x ⟨t, evalTerm v ρ⟩)
  | .allTy t x body, ρ => ∀ v : t.interp, transForm body (ρ.bindVar x ⟨t, v⟩)
  | .exTy t x body, ρ => ∃ v : t.interp, transForm body (ρ.bindVar x ⟨t, v⟩)
  | .allMem m body, ρ => ∀ h : Heap, transForm body (ρ.bindMem m h)
  | .exMem m body, ρ => ∃ h : Heap, transForm body (ρ.bindMem m h)
  | .allProb x body, ρ => ∀ r : ℝ≥0∞, transForm body (ρ.bindProb x r)
  | .allMod name I body, ρ => ∀ M : ModuleImpl I, transForm body (ρ.bindMod name M)
  | .allModRestr name I gs body, ρ =>
      ∀ M : ModuleImpl I, ModuleRespectsLocs (globLocs gs) M →
        transForm body (ρ.bindMod name M)
  | .allModOn name I body, ρ =>
      ∀ (M : ModuleImpl I) (L : LocSet), ModuleRespectsOn L M →
        transForm body (ρ.bindModOn name M L)
  | .allModRestrOn name I gs body, ρ =>
      ∀ (M : ModuleImpl I) (L : LocSet), Disjoint L (globLocs gs) →
        ModuleRespectsOn L M → ModuleRespectsLocs (globLocs gs) M →
          transForm body (ρ.bindModOn name M L)
  | .allOp path s body, ρ =>
      ∀ f : s.arg.interp → s.res.interp, transForm body (ρ.bindOp path f)
  | .allConst path t body, ρ =>
      ∀ v : t.interp, transForm body (ρ.bindConst path t v)
  | .lossless q s, ρ => ProcLossless (ρ.procs q s)
  | .isLossless d, ρ => SDistr.mass (evalTerm d ρ) = 1
  | .probCmp cmp a b, ρ => cmpRel cmp (transProb a ρ) (transProb b ρ)
  | .hoare q s arg pre post, ρ =>
      pHoare (fun h => transForm pre { ρ with memCur := h })
        (ρ.procs q s (evalTerm arg ρ))
        (fun r h' => transForm post { ρ with memCur := h', resCur := ⟨s.res, r⟩ })
  | .bdHoare q s arg pre post cmp bd, ρ =>
      ∀ h : Heap, transForm pre { ρ with memCur := h } →
        cmpRel cmp
          (prEventComp (ρ.procs q s (evalTerm arg ρ)) h
            (fun r h' => transForm post { ρ with memCur := h', resCur := ⟨s.res, r⟩ }))
          bd.value
  | .equiv q₁ s₁ arg₁ q₂ s₂ arg₂ pre post, ρ =>
      pRHL (fun h₁ h₂ => transForm pre { ρ with memLeft := h₁, memRight := h₂ })
        (ρ.procs q₁ s₁ (evalTerm arg₁ ρ))
        (ρ.procs q₂ s₂ (evalTerm arg₂ ρ))
        (fun r₁ h₁ r₂ h₂ => transForm post
          { ρ with memLeft := h₁, memRight := h₂,
                   resLeft := ⟨s₁.res, r₁⟩, resRight := ⟨s₂.res, r₂⟩ })

/-- The probability a probability expression denotes. -/
noncomputable def transProb : EcProb → FormEnv → ℝ≥0∞
  | .pr q s arg m ev, ρ =>
      prEventComp (ρ.procs q s (evalTerm arg { ρ with memCur := ρ.mem m })) (ρ.mem m)
        (fun r h' => transForm ev { ρ with memCur := h', resCur := ⟨s.res, r⟩ })
  | .const r, _ => r.value
  | .pvar x, ρ => ρ.probs x
  | .add a b, ρ => transProb a ρ + transProb b ρ
  | .mul a b, ρ => transProb a ρ * transProb b ρ
  | .absDiff a b, ρ => CatCrypt.Crypto.absDiff (transProb a ρ) (transProb b ρ)

end

/-- The Lean proposition an imported EasyCrypt statement denotes, translated
against the resolution environment `ρ` that binds the games and modules the
statement mentions.

This is a `Prop`, not a theorem. A generated file defines one of these per
imported lemma and leaves the proof open. -/
noncomputable def importedProp (ρ : ProcEnv) (f : EcForm) : Prop :=
  transForm f (initialFormEnv ρ)

/-- The Lean proposition a statement polymorphic in `n` type parameters denotes:
one binder over the type codes per parameter, in the order the source declares
them, around the imported statement at the codes they are bound to.

The binders range over `EcTy`, the codes the ingestion knows, and not over
`Type`; `Form.lean` records what that weakening is and why the alternative
re-indexes the heap model. -/
noncomputable def importedPropPoly (ρ : ProcEnv) : {n : Nat} → EcPolyForm n → Prop
  | 0, f => importedProp ρ f
  | _ + 1, f => ∀ a : EcTy, importedPropPoly ρ (f a)

@[simp] theorem importedPropPoly_zero (ρ : ProcEnv) (f : EcPolyForm 0) :
    importedPropPoly ρ f = importedProp ρ f := rfl

@[simp] theorem importedPropPoly_succ (ρ : ProcEnv) {n : Nat} (f : EcPolyForm (n + 1)) :
    importedPropPoly ρ f = ∀ a : EcTy, importedPropPoly ρ (f a) := rfl

/-- The Lean proposition an imported statement denotes at a fixed realization of
the abstract operators. This is the shape an imported `axiom` of a declaring
theory takes: the statement is a hypothesis about the realization the enclosing
statement binds, so its operators are supplied rather than quantified. A statement
that is itself the goal binds its own operators and carries its theory's axioms as
premises (`EcForm.assembleStatement`), and translates through `importedProp`. -/
noncomputable def importedPropWithOps (ρ : ProcEnv) (ops : OpEnv) (f : EcForm) : Prop :=
  transForm f { initialFormEnv ρ with ops := ops }

/-- The Lean proposition an imported statement denotes when the statement names
functor images: `images name` extends the resolution environment each time the
module binder `name` is instantiated. -/
noncomputable def importedPropWith (ρ : ProcEnv)
    (images : String → ProcEnv → ProcEnv) (f : EcForm) : Prop :=
  transForm f { initialFormEnv ρ with functorImages := images }

/-! ## Node unfolding

One equation per modal node, so a proof can see the CatCrypt judgement an
imported statement lands on without unfolding the whole translation, together
with the equations for the first-order nodes a statement about values is built
from. -/

@[simp] theorem transForm_allTy (t : EcTy) (x : String) (body : EcForm) (ρ : FormEnv) :
    transForm (.allTy t x body) ρ
      = ∀ v : t.interp, transForm body (ρ.bindVar x ⟨t, v⟩) := rfl

@[simp] theorem transForm_exTy (t : EcTy) (x : String) (body : EcForm) (ρ : FormEnv) :
    transForm (.exTy t x body) ρ
      = ∃ v : t.interp, transForm body (ρ.bindVar x ⟨t, v⟩) := rfl

@[simp] theorem transForm_eqT {t : EcTy} (a b : EcTerm t) (ρ : FormEnv) :
    transForm (.eqT a b) ρ = (evalTerm a ρ = evalTerm b ρ) := rfl

@[simp] theorem transForm_holds (b : EcTerm .bool) (ρ : FormEnv) :
    transForm (.holds b) ρ = (evalTerm b ρ = true) := rfl

@[simp] theorem transForm_equiv (q₁ : String) (s₁ : EcSig) (arg₁ : EcTerm s₁.arg)
    (q₂ : String) (s₂ : EcSig) (arg₂ : EcTerm s₂.arg) (pre post : EcForm) (ρ : FormEnv) :
    transForm (.equiv q₁ s₁ arg₁ q₂ s₂ arg₂ pre post) ρ
      = pRHL (fun h₁ h₂ => transForm pre { ρ with memLeft := h₁, memRight := h₂ })
          (ρ.procs q₁ s₁ (evalTerm arg₁ ρ))
          (ρ.procs q₂ s₂ (evalTerm arg₂ ρ))
          (fun r₁ h₁ r₂ h₂ => transForm post
            { ρ with memLeft := h₁, memRight := h₂,
                     resLeft := ⟨s₁.res, r₁⟩, resRight := ⟨s₂.res, r₂⟩ }) := rfl

@[simp] theorem transForm_hoare (q : String) (s : EcSig) (arg : EcTerm s.arg)
    (pre post : EcForm) (ρ : FormEnv) :
    transForm (.hoare q s arg pre post) ρ
      = pHoare (fun h => transForm pre { ρ with memCur := h })
          (ρ.procs q s (evalTerm arg ρ))
          (fun r h' => transForm post { ρ with memCur := h', resCur := ⟨s.res, r⟩ }) := rfl

@[simp] theorem transForm_bdHoare (q : String) (s : EcSig) (arg : EcTerm s.arg)
    (pre post : EcForm) (cmp : EcCmp) (bd : EcRealLit) (ρ : FormEnv) :
    transForm (.bdHoare q s arg pre post cmp bd) ρ
      = ∀ h : Heap, transForm pre { ρ with memCur := h } →
          cmpRel cmp
            (prEventComp (ρ.procs q s (evalTerm arg ρ)) h
              (fun r h' => transForm post { ρ with memCur := h', resCur := ⟨s.res, r⟩ }))
            bd.value := rfl

@[simp] theorem transForm_allModRestr (name : String) (I : EcInterface)
    (gs : List EcGlobal) (body : EcForm) (ρ : FormEnv) :
    transForm (.allModRestr name I gs body) ρ
      = ∀ M : ModuleImpl I, ModuleRespectsLocs (globLocs gs) M →
          transForm body (ρ.bindMod name M) := rfl

@[simp] theorem transForm_allModRestrOn (name : String) (I : EcInterface)
    (gs : List EcGlobal) (body : EcForm) (ρ : FormEnv) :
    transForm (.allModRestrOn name I gs body) ρ
      = ∀ (M : ModuleImpl I) (L : LocSet), Disjoint L (globLocs gs) →
          ModuleRespectsOn L M → ModuleRespectsLocs (globLocs gs) M →
            transForm body (ρ.bindModOn name M L) := rfl

@[simp] theorem transForm_allModOn (name : String) (I : EcInterface)
    (body : EcForm) (ρ : FormEnv) :
    transForm (.allModOn name I body) ρ
      = ∀ (M : ModuleImpl I) (L : LocSet), ModuleRespectsOn L M →
          transForm body (ρ.bindModOn name M L) := rfl

@[simp] theorem transForm_memEqOnMod (name : String) (m₁ m₂ : EcMemRef) (ρ : FormEnv) :
    transForm (.memEqOnMod name m₁ m₂) ρ
      = agreeOn (ρ.modFootprints name) (ρ.mem m₁) (ρ.mem m₂) := rfl

@[simp] theorem transForm_memEqOn (gs : List EcGlobal) (m₁ m₂ : EcMemRef) (ρ : FormEnv) :
    transForm (.memEqOn gs m₁ m₂) ρ
      = agreeOn (globLocs gs) (ρ.mem m₁) (ρ.mem m₂) := rfl

@[simp] theorem transForm_lossless (q : String) (s : EcSig) (ρ : FormEnv) :
    transForm (.lossless q s) ρ = ProcLossless (ρ.procs q s) := rfl

@[simp] theorem transForm_isLossless {t : EcTy} (d : EcTerm (.distr t)) (ρ : FormEnv) :
    transForm (.isLossless d) ρ = (SDistr.mass (evalTerm d ρ) = 1) := rfl

@[simp] theorem transForm_allOp (path : String) (s : EcSig) (body : EcForm)
    (ρ : FormEnv) :
    transForm (.allOp path s body) ρ
      = ∀ f : s.arg.interp → s.res.interp, transForm body (ρ.bindOp path f) := rfl

@[simp] theorem transForm_allConst (path : String) (t : EcTy) (body : EcForm)
    (ρ : FormEnv) :
    transForm (.allConst path t body) ρ
      = ∀ v : t.interp, transForm body (ρ.bindConst path t v) := rfl

@[simp] theorem transForm_imp (a b : EcForm) (ρ : FormEnv) :
    transForm (.imp a b) ρ = (transForm a ρ → transForm b ρ) := rfl

@[simp] theorem transForm_probCmp (cmp : EcCmp) (a b : EcProb) (ρ : FormEnv) :
    transForm (.probCmp cmp a b) ρ = cmpRel cmp (transProb a ρ) (transProb b ρ) := rfl

@[simp] theorem transProb_pr (q : String) (s : EcSig) (arg : EcTerm s.arg)
    (m : EcMemRef) (ev : EcForm) (ρ : FormEnv) :
    transProb (.pr q s arg m ev) ρ
      = prEventComp (ρ.procs q s (evalTerm arg { ρ with memCur := ρ.mem m })) (ρ.mem m)
          (fun r h' => transForm ev { ρ with memCur := h', resCur := ⟨s.res, r⟩ }) := rfl

@[simp] theorem transProb_absDiff (a b : EcProb) (ρ : FormEnv) :
    transProb (.absDiff a b) ρ
      = CatCrypt.Crypto.absDiff (transProb a ρ) (transProb b ρ) := rfl

/-! ## Bridges to the advantage vocabulary

The `pr` node translates to `prEventComp`, the general event probability. The
three lemmas below relate that image to the three probability notions CatCrypt's
game-hopping vocabulary is stated with, and so pin down exactly which extra
quantification an imported bound needs before it becomes an `Advantage` or an
`sdist` statement. -/

/-- The event `res` of a `bool`-returning computation has probability `prTrue`:
`prEventComp` filtered on `res = true` is the probability of returning `true`. -/
theorem prEventComp_res_eq_prTrue (G : SPComp Bool) (h₀ : Heap) :
    prEventComp G h₀ (fun r (_ : Heap) => r = true) = prTrue G h₀ := by
  simp [prEventComp, prEvent, prTrue, tsum_bool_prod_eq]

/-- The translation of `Pr[q(arg) @ m : res]` is the probability that the
procedure returns `true`. -/
theorem transProb_prTrueOf (q : String) (arg : EcTerm .unit) (m : EcMemRef) (ρ : FormEnv) :
    transProb (EcProb.prTrueOf q arg m) ρ
      = prTrue (ρ.procs q ⟨.unit, .bool⟩ (evalTerm arg { ρ with memCur := ρ.mem m }))
          (ρ.mem m) := by
  rw [EcProb.prTrueOf, transProb_pr, ← prEventComp_res_eq_prTrue]
  rfl

/-- `Advantage` is the absolute difference of the two `prTrue` values **at the
empty heap**. An imported bound at a universally quantified memory therefore
implies the `Advantage` bound by instantiating the memory at `Heap.empty`; the
converse does not hold. -/
theorem advantage_eq_absDiff_prTrue (G₀ G₁ : SPComp Bool) :
    Advantage G₀ G₁
      = CatCrypt.Crypto.absDiff (prTrue G₀ Heap.empty) (prTrue G₁ Heap.empty) := rfl

/-- `sdist` is reached from a family of imported bounds only when the bound is
quantified over the initial memory *and* over a post-composed distinguisher: the
supremum defining `sdist` ranges over both. -/
theorem sdist_le_of_forall_absDiff {α β : Type} (f g : α → SPComp β) (ε : ℝ≥0∞)
    (h : ∀ (D : β → SPComp Bool) (a : α) (h₀ : Heap),
      CatCrypt.Crypto.absDiff (prTrue (SPComp.bind (f a) D) h₀)
        (prTrue (SPComp.bind (g a) D) h₀) ≤ ε) :
    sdist f g ≤ ε :=
  iSup_le fun D => iSup_le fun a => iSup_le fun h₀ => h D a h₀

end CatCrypt.Crypto.EasyCryptImport

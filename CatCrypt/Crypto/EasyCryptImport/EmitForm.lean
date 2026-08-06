/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.EasyCryptImport.Emit
import CatCrypt.Crypto.EasyCryptImport.Form

/-!
# EasyCrypt import: the shallow reading of an imported statement

`importedProp ρ f` is the definition of what an imported statement means, and it
is the auditable one: it names the form, so a reader can compare it against the
export. It is not the statement a human proves against. Unfolding it gives a
proposition whose binders are named by `transForm`'s own source — `v`, `f`, `M` —
and whose leaves are environment lookups.

This module prints that unfolded proposition, with binders named from the form's
own data: a module binder by its source name, a quantified type by the source's
variable name, an abstract operator by the last component of its path, a memory
by the name the quantifier gives it. The output is a pair,

```lean
def fooStmt : Prop := importedProp ρ fooForm
theorem fooStmt_eq : fooStmt = <shallow statement> := <proof>
```

so the readable form is **derived** and the equation is what makes it usable.
A shallow statement without its equation would be a second statement of the same
lemma whose agreement with the first is unchecked, which is the duplication
`AGENTS.md` names as an anti-pattern; `emitStatementPair` therefore emits both or
neither, and a form node the printer cannot render is an `Except` error naming
the node rather than a statement with a hole in it.

## The two proof shapes, and what selects them

Measured against the built library rather than assumed:

* **`rfl`** discharges every covered node, the abstract-operator read and the
  real literal included. An operator read resolves through `OpEnv.bindOp`, whose
  two `dif`s test a path and a signature; at the literals a generated statement
  carries, both decide by evaluation, so the environment lookup reduces and the
  binder meets the read. A real literal prints at `ℕ` (`emitRealLit`), which is
  the type `EcRealLit.value` injects from, so the printed bound and the
  translated one are the same term.
* **`show <skeleton>; simp only [transProb_prTrueOf]; rfl`** is needed exactly
  when a `Pr[q(arg) @ m : res]` node is printed as `prTrue`. `prTrue` is not
  definitionally `prEventComp` at the event `res = true`; the two are related by
  `prEventComp_res_eq_prTrue`, which `transProb_prTrueOf` applies. The `show`
  restates the goal at the binder skeleton — the quantifier prefix with holes at
  the probability leaves — because the equation's left side is a `def` and the
  rewrite has to reach under the binders.

`EmitCheck.lean` compares generated text byte for byte, so a change to any arm
here changes a committed file and both move together.

## What has no printed image

Each is an `Except` error naming the node, and each names why.

* **`EcForm.memEq`**, which no decoder produces.
* **`EcForm.ifF` and `EcForm.letF`**, and `EcTerm.ite`, `EcTerm.letIn`: each
  binds or branches inside the proposition, so its image needs a term printer at
  a position where the shallow reading and the form disagree about scope.
* **`EcTerm.ofExpr`**: its image is `evalExpr` of a program expression against
  the local valuation, which is a second printer over `Ast.lean`.
* **`EcTerm.mapMem`, `EcTerm.listMem` and `EcTerm.fsetMem`**: each reads its
  code's decidable equality, and the value it takes at a code without one is not
  the operation, so the text would state the operation at codes where the term
  does not.
* **A procedure whose path the caller did not name** (`ShallowCtx.procNames`):
  the resolution environment is caller-supplied, so the text for `A.guess` or
  `Exp0(A).main` is the caller's to give. The equation's `rfl` is what checks the
  name it gave is the procedure the environment resolves.

## Main results

* `emitShallowForm`, `emitStatementPair`: the printer and the pair it emits.
* `shallowNeedsPrTrue`: whether the form forces the `simp only` proof, which is
  what selects between the two shapes.
* `emitStatementFile`: the pair wrapped in a generated module, with the
  provenance block of the export it comes from.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.EasyCryptImport

open scoped ENNReal

/-! ## Names taken from the form's data -/

/-- The last component of a path, which is the source name an EasyCrypt path ends
in: `Top.PseudoRF.dK` gives `dK`, `A./guess` gives `guess`. -/
def shallowLastName (p : String) : String := lastComponent p

/-- The characters a Lean identifier the printer generates may carry: the
alphanumerics, the underscore, and the subscript digits, which a Lean identifier
accepts and which the judgement binders `h₁` and `r₂` are written with. -/
def shallowIdentChar (c : Char) : Bool :=
  c.isAlphanum || c = '_' || ('₀' ≤ c && c ≤ '₉')

/-- The identifier a source name prints as: a name whose characters all survive
`shallowIdentChar` is printed as it stands, anything else is dropped, and a name
that ends up empty or starting with a digit is prefixed. -/
def shallowIdentOf (s : String) : String :=
  let keep := s.toList.filter shallowIdentChar
  match keep with
  | [] => "x"
  | c :: _ => if c.isDigit then "x" ++ String.ofList keep else String.ofList keep

/-- Whether the pieces a body splits into at a name have a gap between two
consecutive pieces bounded by a non-identifier character on each side, which is
where the name occurs as an identifier of its own rather than inside a longer
one. -/
def shallowBoundedOccurrence : List String → Bool
  | [] => false
  | [_] => false
  | pre :: rest =>
    let post := rest.headD ""
    let leftFree := match pre.toList.getLast? with
      | none => true
      | some c => !shallowIdentChar c
    let rightFree := match post.toList.head? with
      | none => true
      | some c => !shallowIdentChar c
    (leftFree && rightFree) || shallowBoundedOccurrence rest

/-- The binder to print for `nm` in a body that may not read it: a binder the body
does not read prints as `_`, which is what keeps generated code free of
unused-variable warnings. The body reads the name when it occurs at identifier
boundaries, so `r` is unread in `r₁ = r₂` and in `True`. -/
def shallowBinder (body nm : String) : String :=
  if shallowBoundedOccurrence (body.splitOn nm) then nm else "_"

/-- A name not already taken, by appending a numeral to the source-derived one. -/
def shallowFresh (used : List String) (want : String) : String :=
  let rec go (n : Nat) (fuel : Nat) : String :=
    match fuel with
    | 0 => want ++ "_"
    | fuel + 1 =>
      let cand := if n = 0 then want else want ++ toString n
      if used.contains cand then go (n + 1) fuel else cand
  go 0 (used.length + 1)

/-! ## The printing environment

One field per binding `FormEnv` carries, holding the Lean identifier the printed
statement binds it at. The procedure table is the one thing the form does not
determine: the resolution environment is the caller's, so the text for a
procedure is too. -/

/-- The identifiers a printed statement's binders carry, and the text a procedure
path is printed as. -/
structure ShallowCtx where
  /-- The Lean text for the computation a judgement or a probability node runs,
  keyed by the path it names. This is the procedure **applied to its argument**,
  which is well defined because such a node carries the unit argument: EasyCrypt
  leaves a judgement's argument implicit and `judgementArg` accepts no other, so
  the text cannot depend on an argument the printer would have to render. A path
  outside this table has no image. -/
  procNames : List (String × String) := []
  /-- The Lean text for the procedure itself, unapplied, keyed by its path. This
  is what `islossless` reads, since `ProcLossless` is a property of the function
  and not of one of its computations. -/
  procFnNames : List (String × String) := []
  /-- The identifier each quantified memory is bound at. -/
  mems : List (String × String) := []
  /-- The identifier each logical variable is bound at. -/
  locals : List (String × String) := []
  /-- The identifier each probability parameter is bound at. -/
  probs : List (String × String) := []
  /-- The identifier each module binder is bound at. -/
  mods : List (String × String) := []
  /-- The Lean text of the interface each module binder ranges over, keyed by the
  binder's source name. An `EcInterface` carries a function field, so a statement
  names the interface its binder ranges over rather than reconstructing it:
  `Emit.emitInterface` prints an `interfaceOfSigs` application over the declared
  signatures, which is what a generated program uses, while a statement refers to
  the interface value the caller committed. -/
  interfaces : List (String × String) := []
  /-- The identifier each abstract operator's realization is bound at. -/
  ops : List (String × String) := []
  /-- The identifier each module binder's footprint is bound at. -/
  footprints : List (String × String) := []
  /-- The identifiers the enclosing judgement's memories are bound at. -/
  memLeft : String := "h₁"
  /-- The right memory of the enclosing relational judgement. -/
  memRight : String := "h₂"
  /-- The ambient memory of a unary judgement or a probability event. -/
  memCur : String := "h"
  /-- The identifiers the enclosing judgement's results are bound at. -/
  resLeft : String := "r₁"
  /-- The right result of the enclosing relational judgement. -/
  resRight : String := "r₂"
  /-- The result of a unary judgement or a probability event. -/
  resCur : String := "r"
  /-- Every identifier already bound, so a new binder does not shadow one. -/
  used : List String := []

/-- Bind `want` at a fresh identifier, returning it and the extended context. -/
def ShallowCtx.fresh (C : ShallowCtx) (want : String) : String × ShallowCtx :=
  let nm := shallowFresh C.used (shallowIdentOf want)
  (nm, { C with used := nm :: C.used })

/-- The text a memory reference prints as. -/
def ShallowCtx.memText (C : ShallowCtx) : EcMemRef → Except String String
  | .named m =>
    match List.lookup m C.mems with
    | some nm => .ok nm
    | none => fail s!"the memory '{m}' is read where no quantifier binds it"
  | .side .left => .ok C.memLeft
  | .side .right => .ok C.memRight
  | .side .cur => .ok C.memCur

/-- The text the result of the enclosing judgement prints as. -/
def ShallowCtx.resText (C : ShallowCtx) : EcSide → String
  | .left => C.resLeft
  | .right => C.resRight
  | .cur => C.resCur

/-- The text the computation a judgement or probability node runs prints as. The
node's signature must take the unit argument, since the caller's text stands for
the procedure already applied. -/
def ShallowCtx.procText (C : ShallowCtx) (q : String) (s : EcSig) :
    Except String String :=
  if s.arg ≠ EcTy.unit then
    fail s!"a judgement or probability over '{q}', whose argument has type \
      {repr s.arg}: the caller's text stands for the procedure applied to its \
      argument, and it cannot depend on one the printer would have to render"
  else
    match List.lookup q C.procNames with
    | some t => .ok t
    | none =>
      fail s!"the procedure '{q}' has no printed name: the resolution environment \
        is supplied by the caller, so the text it resolves to is too"

/-- The text the interface a module binder ranges over prints as. -/
def ShallowCtx.interfaceText (C : ShallowCtx) (nm : String) : Except String String :=
  match List.lookup nm C.interfaces with
  | some t => .ok t
  | none =>
    fail s!"the module binder '{nm}' has no printed interface: an EcInterface \
      carries a function field, so the value the binder ranges over is named by \
      the caller"

/-- The text the procedure itself prints as, unapplied. -/
def ShallowCtx.procFnText (C : ShallowCtx) (q : String) : Except String String :=
  match List.lookup q C.procFnNames with
  | some t => .ok t
  | none =>
    fail s!"the procedure '{q}' has no printed name, unapplied: the resolution \
      environment is supplied by the caller, so the text it resolves to is too"

/-! ## Real literals

`EcRealLit.value` injects the numeral the form carries from `ℕ`, so the printed
text is the numeral at `ℕ` and the coercion into `ℝ≥0∞` is the elaborator's. The
numeral printed bare would be `One.one` at `1` and `Zero.zero` at `0`, neither of
which is the injection definitionally, and the equation the pair carries is
closed by `rfl`. -/

/-- The text a real literal prints as. -/
def emitRealLit (r : EcRealLit) : String :=
  if r.den == 1 then s!"({r.num} : ℕ)"
  else s!"(({r.num} : ℕ) / ({r.den} : ℕ) : ℝ≥0∞)"

/-! ## Terms -/

/-- Print the shallow reading of a term: the Lean text its value has under the
bindings `C` records. -/
def emitShallowTerm : {t : EcTy} → EcTerm t → ShallowCtx → Except String String
  | _, .var _ x, C =>
    match List.lookup x C.locals with
    | some nm => .ok nm
    | none => fail s!"the logical variable '{x}' is read where no binder binds it"
  | t, .lit v, _ => .ok (emitVal t v)
  | _, .ofExpr _, _ =>
    fail "a program expression in a statement: its value is evalExpr against the \
      local valuation, which this printer does not render"
  | _, .glob g m, C => do
    let mt ← C.memText m
    .ok s!"({mt}).gget ({emitGlobal g}).loc"
  | _, .res _ s, C => .ok (C.resText s)
  | _, .opApp path s arg, C =>
    match List.lookup path C.ops with
    | none =>
      fail s!"the abstract operator '{path}' is read where no binder binds it: an \
        assembled statement binds every operator it reads"
    | some nm =>
      if s.arg = EcTy.unit then .ok nm
      else do
        let a ← emitShallowTerm arg C
        .ok s!"({nm} {a})"
  | _, .app f x, C => do
    let g ← emitShallowTerm f C; let a ← emitShallowTerm x C; .ok s!"({g} {a})"
  | _, .lam a x body, C =>
    let (nm, C') := C.fresh x
    let C'' := { C' with locals := (x, nm) :: C'.locals }
    do let b ← emitShallowTerm body C''
       .ok s!"(fun {nm} : {emitTy a}.interp => {b})"
  | _, .bnot e, C => do let a ← emitShallowTerm e C; .ok s!"(!{a})"
  | _, .band a b, C => do
    let x ← emitShallowTerm a C; let y ← emitShallowTerm b C; .ok s!"({x} && {y})"
  | _, .bxor a b, C => do
    let x ← emitShallowTerm a C; let y ← emitShallowTerm b C; .ok s!"(xor {x} {y})"
  | _, .beq a b, C => do
    let x ← emitShallowTerm a C; let y ← emitShallowTerm b C
    .ok s!"(decide ({x} = {y}))"
  | _, .pair a b, C => do
    let x ← emitShallowTerm a C; let y ← emitShallowTerm b C; .ok s!"({x}, {y})"
  | _, .fst p, C => do let a ← emitShallowTerm p C; .ok s!"({a}).1"
  | _, .snd p, C => do let a ← emitShallowTerm p C; .ok s!"({a}).2"
  | _, .finAdd a b, C => do
    let x ← emitShallowTerm a C; let y ← emitShallowTerm b C; .ok s!"({x} + {y})"
  | _, .intAdd a b, C => do
    let x ← emitShallowTerm a C; let y ← emitShallowTerm b C; .ok s!"({x} + {y})"
  | _, .intMul a b, C => do
    let x ← emitShallowTerm a C; let y ← emitShallowTerm b C; .ok s!"({x} * {y})"
  | _, .intOpp a, C => do
    let x ← emitShallowTerm a C; .ok s!"(-{x})"
  | _, .intEdivz a b, C => do
    let x ← emitShallowTerm a C; let y ← emitShallowTerm b C
    .ok s!"(Int.ediv {x} {y}, Int.emod {x} {y})"
  | _, .intAbsz a, C => do
    let x ← emitShallowTerm a C; .ok s!"(Int.natAbs {x} : Int)"
  | _, .intGcd a b, C => do
    let x ← emitShallowTerm a C; let y ← emitShallowTerm b C
    .ok s!"(Int.gcd {x} {y} : Int)"
  | _, .intLe a b, C => do
    let x ← emitShallowTerm a C; let y ← emitShallowTerm b C
    .ok s!"(decide ({x} ≤ {y}))"
  | _, .listCons x l, C => do
    let a ← emitShallowTerm x C; let b ← emitShallowTerm l C
    .ok s!"(EcTy.listCons {a} {b})"
  | _, .listSize l, C => do
    let a ← emitShallowTerm l C; .ok s!"(EcTy.listSize {a})"
  | _, .iter n f x, C => do
    let a ← emitShallowTerm n C; let g ← emitShallowTerm f C
    let b ← emitShallowTerm x C
    .ok s!"(EcTy.iter {a} {g} {b})"
  | _, .iterop n opr x z, C => do
    let a ← emitShallowTerm n C; let g ← emitShallowTerm opr C
    let b ← emitShallowTerm x C; let c ← emitShallowTerm z C
    .ok s!"(EcTy.iterop {a} (fun u v => {g} u v) {b} {c})"
  | _, .choiceb p x0, C => do
    let q ← emitShallowTerm p C; let d ← emitShallowTerm x0 C
    .ok s!"(EcTy.choiceb {q} {d})"
  | _, .someT x, C => do
    let a ← emitShallowTerm x C; .ok s!"(EcTy.someVal {a})"
  | _, .optionGetD o d, C => do
    let a ← emitShallowTerm o C; let b ← emitShallowTerm d C
    .ok s!"(EcTy.optionGetD {a} {b})"
  | _, .listUniq _, _ =>
    fail "a list repetition test in a statement: its value is the test at the \
      element code's decidable equality, which this printer does not render"
  | _, .listMap f l, C => do
    let g ← emitShallowTerm f C; let s ← emitShallowTerm l C
    .ok s!"(EcTy.listMap {g} {s})"
  | _, .listFilter p l, C => do
    let q ← emitShallowTerm p C; let s ← emitShallowTerm l C
    .ok s!"(EcTy.listFilter {q} {s})"
  | _, .listAll p l, C => do
    let q ← emitShallowTerm p C; let s ← emitShallowTerm l C
    .ok s!"(EcTy.listAll {q} {s})"
  | _, .listHas p l, C => do
    let q ← emitShallowTerm p C; let s ← emitShallowTerm l C
    .ok s!"(EcTy.listHas {q} {s})"
  | _, .listCount p l, C => do
    let q ← emitShallowTerm p C; let s ← emitShallowTerm l C
    .ok s!"(EcTy.listCount {q} {s})"
  | _, .mapMem _ _, _ =>
    fail "a finite-map membership test in a statement: its value is the test at \
      the key code's decidable equality, which this printer does not render"
  | _, .listMem _ _, _ =>
    fail "a list membership test in a statement: its value is the test at the \
      element code's decidable equality, which this printer does not render"
  | _, .fsetMem _ _, _ =>
    fail "a finite-set membership test in a statement: its value is the test at \
      the element code's decidable equality, which this printer does not render"
  | _, .ite _ _ _, _ =>
    fail "a conditional term in a statement: the shallow reading branches on a \
      value, which this printer does not render"
  | _, .letIn _ _ _, _ =>
    fail "a let term in a statement: the shallow reading binds a value, which \
      this printer does not render"

/-! ## Whether the probability shape forces the rewrite

`Pr[q(arg) @ m : res]` prints as `prTrue`, which is not definitionally the
`prEventComp` the translation produces, so a statement carrying one is proved
through `transProb_prTrueOf` rather than by `rfl`. Every other covered node is
definitional. -/

mutual

/-- Whether a formula carries a probability node printed as `prTrue`. -/
def shallowNeedsPrTrue : EcForm → Bool
  | .not f => shallowNeedsPrTrue f
  | .and a b => shallowNeedsPrTrue a || shallowNeedsPrTrue b
  | .or a b => shallowNeedsPrTrue a || shallowNeedsPrTrue b
  | .imp a b => shallowNeedsPrTrue a || shallowNeedsPrTrue b
  | .iff a b => shallowNeedsPrTrue a || shallowNeedsPrTrue b
  | .allTy _ _ body => shallowNeedsPrTrue body
  | .exTy _ _ body => shallowNeedsPrTrue body
  | .allMem _ body => shallowNeedsPrTrue body
  | .exMem _ body => shallowNeedsPrTrue body
  | .allProb _ body => shallowNeedsPrTrue body
  | .allMod _ _ body => shallowNeedsPrTrue body
  | .allModRestr _ _ _ body => shallowNeedsPrTrue body
  | .allModOn _ _ body => shallowNeedsPrTrue body
  | .allModRestrOn _ _ _ body => shallowNeedsPrTrue body
  | .allOp _ _ body => shallowNeedsPrTrue body
  | .allConst _ _ body => shallowNeedsPrTrue body
  | .probCmp _ a b => shallowProbNeedsPrTrue a || shallowProbNeedsPrTrue b
  | _ => false

/-- Whether a probability expression is, or contains, a `Pr[… : res]` node. -/
def shallowProbNeedsPrTrue : EcProb → Bool
  | .pr _ _ _ _ (.holds (.res _ .cur)) => true
  | .pr _ _ _ _ _ => false
  | .const _ => false
  | .pvar _ => false
  | .add a b => shallowProbNeedsPrTrue a || shallowProbNeedsPrTrue b
  | .mul a b => shallowProbNeedsPrTrue a || shallowProbNeedsPrTrue b
  | .absDiff a b => shallowProbNeedsPrTrue a || shallowProbNeedsPrTrue b

end

/-! ## Formulas and probabilities

`holes` prints the probability leaves as `_`, which is the skeleton the `show` of
the generated proof restates the goal at: the quantifier prefix and the shape of
the comparison, with the probabilities left for the rewrite to reach. -/

mutual

/-- Print the shallow reading of a formula. With `holes`, a probability
expression prints as `_`. -/
def emitShallowForm (holes : Bool) : EcForm → ShallowCtx → Except String String
  | .tru, _ => .ok "True"
  | .fls, _ => .ok "False"
  | .holds b, C => do let t ← emitShallowTerm b C; .ok s!"{t} = true"
  | .eqT a b, C => do
    let x ← emitShallowTerm a C; let y ← emitShallowTerm b C; .ok s!"{x} = {y}"
  | .memEq _ _, _ =>
    fail "whole-memory equality: no decoder produces it, so no generated \
      statement carries it"
  | .memEqOn gs m₁ m₂, C => do
    let a ← C.memText m₁; let b ← C.memText m₂
    let gsText := String.intercalate ", " (gs.map emitGlobal)
    .ok s!"agreeOn (globLocs [{gsText}]) {a} {b}"
  | .memEqOnMod nm m₁ m₂, C => do
    let a ← C.memText m₁; let b ← C.memText m₂
    match List.lookup nm C.footprints with
    | some L => .ok s!"agreeOn {L} {a} {b}"
    | none =>
      fail s!"'glob {nm}' is compared where no binder carries the module's \
        footprint"
  | .not f, C => do let a ← emitShallowForm holes f C; .ok s!"¬ ({a})"
  | .and a b, C => do
    let x ← emitShallowForm holes a C; let y ← emitShallowForm holes b C
    .ok s!"({x}) ∧ ({y})"
  | .or a b, C => do
    let x ← emitShallowForm holes a C; let y ← emitShallowForm holes b C
    .ok s!"({x}) ∨ ({y})"
  | .imp a b, C => do
    let x ← emitShallowForm holes a C; let y ← emitShallowForm holes b C
    .ok s!"({x}) → {y}"
  | .iff a b, C => do
    let x ← emitShallowForm holes a C; let y ← emitShallowForm holes b C
    .ok s!"({x}) ↔ ({y})"
  | .ifF _ _ _, _ =>
    fail "a conditional formula: its shallow reading branches on a value, which \
      this printer does not render"
  | .letF _ _ _, _ =>
    fail "a let formula: its shallow reading binds a value, which this printer \
      does not render"
  | .allTy t x body, C =>
    let (nm, C') := C.fresh x
    let C'' := { C' with locals := (x, nm) :: C'.locals }
    do let b ← emitShallowForm holes body C''
       .ok s!"∀ {nm} : {emitTy t}.interp, {b}"
  | .exTy t x body, C =>
    let (nm, C') := C.fresh x
    let C'' := { C' with locals := (x, nm) :: C'.locals }
    do let b ← emitShallowForm holes body C''
       .ok s!"∃ {nm} : {emitTy t}.interp, {b}"
  | .allMem m body, C =>
    let (nm, C') := C.fresh m
    let C'' := { C' with mems := (m, nm) :: C'.mems }
    do let b ← emitShallowForm holes body C''
       .ok s!"∀ {nm} : Heap, {b}"
  | .exMem m body, C =>
    let (nm, C') := C.fresh m
    let C'' := { C' with mems := (m, nm) :: C'.mems }
    do let b ← emitShallowForm holes body C''
       .ok s!"∃ {nm} : Heap, {b}"
  | .allProb x body, C =>
    let (nm, C') := C.fresh x
    let C'' := { C' with probs := (x, nm) :: C'.probs }
    do let b ← emitShallowForm holes body C''
       .ok s!"∀ {nm} : ℝ≥0∞, {b}"
  | .allMod nm _ body, C =>
    let (m, C') := C.fresh nm
    let C'' := { C' with mods := (nm, m) :: C'.mods }
    do let I ← C.interfaceText nm
       let b ← emitShallowForm holes body C''
       .ok s!"∀ {m} : ModuleImpl {I}, {b}"
  | .allModRestr nm _ gs body, C =>
    let (m, C') := C.fresh nm
    let C'' := { C' with mods := (nm, m) :: C'.mods }
    let gsText := String.intercalate ", " (gs.map emitGlobal)
    do let I ← C.interfaceText nm
       let b ← emitShallowForm holes body C''
       .ok s!"∀ {m} : ModuleImpl {I}, \
         ModuleRespectsLocs (globLocs [{gsText}]) {m} → {b}"
  | .allModOn nm _ body, C =>
    let (m, C') := C.fresh nm
    let (L, C'') := C'.fresh "L"
    let C₃ := { C'' with mods := (nm, m) :: C''.mods,
                         footprints := (nm, L) :: C''.footprints }
    do let I ← C.interfaceText nm
       let b ← emitShallowForm holes body C₃
       .ok s!"∀ ({m} : ModuleImpl {I}) ({L} : LocSet), \
         ModuleRespectsOn {L} {m} → {b}"
  | .allModRestrOn nm _ gs body, C =>
    let (m, C') := C.fresh nm
    let (L, C'') := C'.fresh "L"
    let C₃ := { C'' with mods := (nm, m) :: C''.mods,
                         footprints := (nm, L) :: C''.footprints }
    let gsText := String.intercalate ", " (gs.map emitGlobal)
    do let I ← C.interfaceText nm
       let b ← emitShallowForm holes body C₃
       .ok s!"∀ ({m} : ModuleImpl {I}) ({L} : LocSet), \
         Disjoint {L} (globLocs [{gsText}]) → ModuleRespectsOn {L} {m} → \
         ModuleRespectsLocs (globLocs [{gsText}]) {m} → {b}"
  | .allOp path s body, C =>
    let (nm, C') := C.fresh (shallowLastName path)
    let C'' := { C' with ops := (path, nm) :: C'.ops }
    do let b ← emitShallowForm holes body C''
       .ok s!"∀ {nm} : {emitTy s.arg}.interp → {emitTy s.res}.interp, {b}"
  | .allConst path t body, C =>
    let (nm, C') := C.fresh (shallowLastName path)
    let C'' := { C' with ops := (path, nm) :: C'.ops }
    do let b ← emitShallowForm holes body C''
       .ok s!"∀ {nm} : {emitTy t}.interp, {b}"
  | .lossless q _, C => do
    let p ← C.procFnText q
    .ok s!"ProcLossless ({p})"
  | .isLossless d, C => do
    let t ← emitShallowTerm d C
    .ok s!"SDistr.mass {t} = 1"
  | .probCmp cmp a b, C =>
    if holes then
      .ok (match cmp with
           | .le => "_ ≤ _" | .lt => "_ < _" | .eq => "_ = _"
           | .ge => "_ ≤ _" | .gt => "_ < _")
    else do
      let x ← emitShallowProb a C
      let y ← emitShallowProb b C
      .ok (match cmp with
           | .le => s!"{x} ≤ {y}" | .lt => s!"{x} < {y}" | .eq => s!"{x} = {y}"
           | .ge => s!"{y} ≤ {x}" | .gt => s!"{y} < {x}")
  | .hoare q s _ pre post, C => do
    let p ← C.procText q s
    let (hpre, C₁) := C.fresh "h"
    let preT ← emitShallowForm holes pre { C₁ with memCur := hpre }
    let (hpost, C₂) := C.fresh "h"
    let (r, C₃) := C₂.fresh "r"
    let postT ← emitShallowForm holes post
      { C₃ with memCur := hpost, resCur := r }
    .ok s!"pHoare (fun {shallowBinder preT hpre} => {preT}) ({p}) \
      (fun {shallowBinder postT r} {shallowBinder postT hpost} => {postT})"
  | .bdHoare q s _ pre post cmp bd, C => do
    let p ← C.procText q s
    let (h, C₁) := C.fresh "h"
    let preT ← emitShallowForm holes pre { C₁ with memCur := h }
    let (hpost, C₂) := C₁.fresh "h"
    let (r, C₃) := C₂.fresh "r"
    let postT ← emitShallowForm holes post
      { C₃ with memCur := hpost, resCur := r }
    let ev := s!"prEventComp ({p}) {h} (fun {shallowBinder postT r} \
      {shallowBinder postT hpost} => {postT})"
    let bdT := emitRealLit bd
    let cmpT := match cmp with
      | .le => s!"{ev} ≤ {bdT}" | .lt => s!"{ev} < {bdT}" | .eq => s!"{ev} = {bdT}"
      | .ge => s!"{bdT} ≤ {ev}" | .gt => s!"{bdT} < {ev}"
    .ok s!"∀ {h} : Heap, {preT} → {cmpT}"
  | .equiv q₁ s₁ _ q₂ s₂ _ pre post, C => do
    let p₁ ← C.procText q₁ s₁
    let p₂ ← C.procText q₂ s₂
    let (h₁, Ca) := C.fresh "h₁"
    let (h₂, Cb) := Ca.fresh "h₂"
    let preT ← emitShallowForm holes pre { Cb with memLeft := h₁, memRight := h₂ }
    let (r₁, Cc) := C.fresh "r₁"
    let (r₂, Cd) := Cc.fresh "r₂"
    let (k₁, Ce) := Cd.fresh "h₁"
    let (k₂, Cf) := Ce.fresh "h₂"
    let postT ← emitShallowForm holes post
      { Cf with memLeft := k₁, memRight := k₂, resLeft := r₁, resRight := r₂ }
    .ok s!"pRHL (fun {shallowBinder preT h₁} {shallowBinder preT h₂} => {preT}) \
      ({p₁}) ({p₂}) (fun {shallowBinder postT r₁} {shallowBinder postT k₁} \
      {shallowBinder postT r₂} {shallowBinder postT k₂} => {postT})"

/-- Print the shallow reading of a probability expression. -/
def emitShallowProb : EcProb → ShallowCtx → Except String String
  | .pr q s _ m ev, C => do
    let p ← C.procText q s
    let mt ← C.memText m
    match ev with
    | .holds (.res _ .cur) => .ok s!"prTrue ({p}) {mt}"
    | _ =>
      let (h, C₁) := C.fresh "h"
      let (r, C₂) := C₁.fresh "r"
      let evT ← emitShallowForm false ev { C₂ with memCur := h, resCur := r }
      .ok s!"prEventComp ({p}) {mt} (fun {r} {h} => {evT})"
  | .const r, _ => .ok (emitRealLit r)
  | .pvar x, C =>
    match List.lookup x C.probs with
    | some nm => .ok nm
    | none => fail s!"the probability parameter '{x}' is read where no quantifier \
        binds it"
  | .add a b, C => do
    let x ← emitShallowProb a C; let y ← emitShallowProb b C; .ok s!"({x} + {y})"
  | .mul a b, C => do
    let x ← emitShallowProb a C; let y ← emitShallowProb b C; .ok s!"({x} * {y})"
  | .absDiff a b, C => do
    let x ← emitShallowProb a C; let y ← emitShallowProb b C
    .ok s!"(CatCrypt.Crypto.absDiff {x} {y})"

end

/-! ## The emitted pair -/

/-- The proof text the equation is closed with, and the shape is selected by the
printer's own decision: a `prTrue` leaf is the one covered image that is not
definitional. -/
def emitShallowProof (f : EcForm) (skeleton : String) : String :=
  if shallowNeedsPrTrue f then
    emitLines
      [ "  by",
        "    show (" ++ skeleton ++ ") = _",
        "    simp only [transProb_prTrueOf]",
        "    rfl" ]
  else "  rfl\n"

/-- The definition of an imported statement together with the equation that gives
its shallow reading. `rhoText` is the resolution environment the statement is
translated against and `formText` the name of the committed form.

Both declarations or neither: a shallow statement whose equation the printer
could not produce is a second statement of the lemma with nothing checking that
the two agree. -/
def emitStatementPair (declName rhoText formText : String) (f : EcForm)
    (C : ShallowCtx) : Except String String := do
  let stmt ← emitShallowForm false f C
  let skeleton ← emitShallowForm true f C
  .ok (emitLines
    [ "/-- The imported statement, as the translation defines it. -/",
      "noncomputable def " ++ declName ++ " : Prop :=",
      "  importedProp " ++ rhoText ++ " " ++ formText,
      "",
      "/-- The shallow reading of that statement, derived from the form. -/",
      "theorem " ++ declName ++ "_eq :",
      "    " ++ declName ++ " =",
      "      " ++ stmt ++ " :="]
    ++ emitShallowProof f skeleton)

/-! ## The generated file -/

/-- The provenance block of a generated statement file: the source path, the
source digest, the schema name and version, the EasyCrypt build identity the
exporter recorded, the theory root, and what the declarations below do and do not
assert. -/
def statementProvenanceBlock (e : EcExport) (item : String) : String :=
  emitLines
    [ "/-!",
      "# Generated EasyCrypt import: " ++ item,
      "",
      "This file is generated from an EasyCrypt export by `emitStatementFile`",
      "(`CatCrypt/Crypto/EasyCryptImport/EmitForm.lean`). Regenerate it rather",
      "than editing it.",
      "",
      "* source: `" ++ e.source ++ "`",
      "* source_digest: `" ++ e.sourceDigest.getD "(absent)" ++ "`",
      "* schema: `" ++ schemaName ++ "` version " ++ toString schemaVersion,
      "* EasyCrypt build: `" ++ e.ecHash ++ "`",
      "* theory root: `" ++ e.root ++ "`",
      "",
      "The EasyCrypt exporter that produced the JSON and the ingestion that",
      "decoded it are unverified, and both are in the trust base of the",
      "declarations below: no theorem relates the source file to the AST literal",
      "here.",
      "",
      "The statement itself is not asserted: an EasyCrypt proof is not a Lean",
      "proof. The declarations below are the imported proposition and its shallow",
      "reading, together with the equation between the two.",
      "-/" ]

/-- A generated Lean module holding one imported statement and its shallow
reading: the copyright header, the `imports` and `opens` the caller names, the
provenance block of `e`, and the pair `emitStatementPair` prints.

The imports and the opens are the caller's because the statement's text is: it
names the resolution environment, the committed form, and the Lean computation
each procedure path resolves to, and those live in whichever module the caller
committed them in. -/
def emitStatementFile (e : EcExport) (item declName rhoText formText : String)
    (imports opens : List String) (f : EcForm) (C : ShallowCtx) :
    Except String String := do
  let decls ← emitStatementPair declName rhoText formText f C
  .ok (copyrightHeader
    ++ String.join (imports.map (fun m => "import " ++ m ++ "\n"))
    ++ "\n" ++ statementProvenanceBlock e item
    ++ "\nset_option autoImplicit false\n"
    ++ "\nnamespace " ++ generatedNamespace ++ "\n\n"
    ++ String.join (opens.map (fun n => "open " ++ n ++ "\n"))
    ++ (if opens.isEmpty then "" else "\n")
    ++ decls
    ++ "\nend " ++ generatedNamespace ++ "\n")

/-! ## Checks

Each arm is pinned by the text it prints. The statements below are the forms of
`Examples/OTPEquivImport.lean`, `Examples/RestrictedImport.lean`,
`Examples/AdversaryEquivImport.lean` and `Examples/PRFParamImport.lean`, whose
hand-written equations are the specification this printer reproduces. -/

section Check

/-- The signature of an argument-free experiment. -/
private def chkMainSig : EcSig := ⟨.unit, .bool⟩

/-- The interface of the one-procedure adversary those examples quantify over. -/
private def chkAdvInterface : EcInterface where
  names := ["guess"]
  sig := fun _ => ⟨.bool, .bool⟩

/-- The global the restriction is stated against. -/
private def chkKGlobal : EcGlobal := { name := "Top.Otp./k", id := 0, ty := .bool }

/-- The context the two experiment paths are named in. -/
private def chkExpCtx : ShallowCtx where
  procNames :=
    [("Top.Exp0(A)./main", "expImpl A false"),
     ("Top.Exp1(A)./main", "expImpl A true"),
     ("Top.OTP0./main", "lowerClosedGame (otpGame false)"),
     ("Top.OTP1./main", "lowerClosedGame (otpGame true)")]
  procFnNames := [("A./guess", "A.proc \"guess\"")]
  interfaces := [("A", "advInterface")]

-- `equiv[OTP0.main ~ OTP1.main : true ==> ={res}]`, the no-operator case, whose
-- hand-written equation is closed by `rfl`.
#guard emitShallowForm false
    (.equiv "Top.OTP0./main" chkMainSig (.lit (t := .unit) ())
            "Top.OTP1./main" chkMainSig (.lit (t := .unit) ())
       .tru (.eqT (.res .bool .left) (.res .bool .right))) chkExpCtx
  == .ok "pRHL (fun _ _ => True) (lowerClosedGame (otpGame false)) \
      (lowerClosedGame (otpGame true)) (fun r₁ _ r₂ _ => r₁ = r₂)"

-- `forall (A <: Adv{-Otp}) &m, Pr[Exp0(A).main() @ &m : res] = Pr[…]`: the
-- module binder takes its source name, the memory quantifier its own, and the
-- two probabilities print as `prTrue`.
#guard emitShallowForm false
    (.allModRestr "A" chkAdvInterface [chkKGlobal]
      (.allMem "&m"
        (.probCmp .eq
          (EcProb.prTrueOf "Top.Exp0(A)./main" (.lit (t := .unit) ()) (.named "&m"))
          (EcProb.prTrueOf "Top.Exp1(A)./main" (.lit (t := .unit) ()) (.named "&m")))))
    chkExpCtx
  == .ok "∀ A : ModuleImpl advInterface, ModuleRespectsLocs (globLocs \
      [(EcGlobal.mk \"Top.Otp./k\" 0 EcTy.bool)]) A → ∀ m : Heap, \
      prTrue (expImpl A false) m = prTrue (expImpl A true) m"

-- and the skeleton the generated proof restates the goal at: the same prefix
-- with the probabilities left as holes.
#guard emitShallowForm true
    (.allModRestr "A" chkAdvInterface [chkKGlobal]
      (.allMem "&m"
        (.probCmp .eq
          (EcProb.prTrueOf "Top.Exp0(A)./main" (.lit (t := .unit) ()) (.named "&m"))
          (EcProb.prTrueOf "Top.Exp1(A)./main" (.lit (t := .unit) ()) (.named "&m")))))
    chkExpCtx
  == .ok "∀ A : ModuleImpl advInterface, ModuleRespectsLocs (globLocs \
      [(EcGlobal.mk \"Top.Otp./k\" 0 EcTy.bool)]) A → ∀ m : Heap, _ = _"

-- The probability shape is what selects the proof, and it selects it from the
-- form rather than from the printed text.
#guard shallowNeedsPrTrue
    (.allMem "&m" (.probCmp .eq
      (EcProb.prTrueOf "Top.Exp0(A)./main" (.lit (t := .unit) ()) (.named "&m"))
      (EcProb.prTrueOf "Top.Exp1(A)./main" (.lit (t := .unit) ()) (.named "&m")))) == true

#guard shallowNeedsPrTrue
    (.equiv "Top.OTP0./main" chkMainSig (.lit (t := .unit) ())
            "Top.OTP1./main" chkMainSig (.lit (t := .unit) ())
       .tru (.eqT (.res .bool .left) (.res .bool .right))) == false

-- The abstract-operator case: the binder takes the last component of the
-- operator's path, so the goal reads `dK` and not `v`.
#guard emitShallowForm false
    (.allConst "Top.PseudoRF.dK" (.distr (.opaque "Top.PseudoRF.K"))
      (.isLossless (.opApp "Top.PseudoRF.dK"
        ⟨.unit, .distr (.opaque "Top.PseudoRF.K")⟩ (.lit (t := .unit) ()))))
    {}
  == .ok "∀ dK : (EcTy.distr (EcTy.opaque \"Top.PseudoRF.K\")).interp, \
      SDistr.mass dK = 1"

-- An arrow-typed operator binds a function, at the codes its signature carries.
#guard emitShallowForm false
    (.allOp "Top.RF.dR" ⟨.bool, .distr .bool⟩
      (.isLossless (.opApp "Top.RF.dR" ⟨.bool, .distr .bool⟩ (.lit (t := .bool) true))))
    {}
  == .ok "∀ dR : EcTy.bool.interp → (EcTy.distr EcTy.bool).interp, \
      SDistr.mass (dR true) = 1"

-- A module binder that carries its footprint binds both, and the footprint is
-- what `={glob A}` compares.
#guard emitShallowForm false
    (.allModRestrOn "A" chkAdvInterface [chkKGlobal]
      (.equiv "Top.Exp0(A)./main" chkMainSig (.lit (t := .unit) ())
              "Top.Exp1(A)./main" chkMainSig (.lit (t := .unit) ())
        (.memEqOnMod "A" (.side .left) (.side .right))
        (.eqT (.res .bool .left) (.res .bool .right)))) chkExpCtx
  == .ok "∀ (A : ModuleImpl advInterface) (L : LocSet), Disjoint L (globLocs \
      [(EcGlobal.mk \"Top.Otp./k\" 0 EcTy.bool)]) → ModuleRespectsOn L A → \
      ModuleRespectsLocs (globLocs [(EcGlobal.mk \"Top.Otp./k\" 0 EcTy.bool)]) \
      A → pRHL (fun h₁ h₂ => agreeOn L h₁ h₂) (expImpl A false) \
      (expImpl A true) (fun r₁ _ r₂ _ => r₁ = r₂)"

-- `islossless A.guess` reads the procedure the caller named.
#guard emitShallowForm false (.lossless "A./guess" ⟨.bool, .bool⟩) chkExpCtx
  == .ok "ProcLossless (A.proc \"guess\")"

-- A bounded Hoare judgement at the trivial pre- and postcondition: the memory the
-- precondition reads is the one the computation starts from, and the bound is the
-- numeral the form carries, at `ℕ`.
#guard emitShallowForm false
    (.bdHoare "Top.OTP0./main" chkMainSig (.lit (t := .unit) ())
      .tru .tru EcCmp.eq (EcRealLit.mk 1 1)) chkExpCtx
  == .ok "∀ h : Heap, True → prEventComp (lowerClosedGame (otpGame false)) h \
      (fun _ _ => True) = (1 : ℕ)"

-- `EcCmp.ge` puts the bound on the left, as `cmpRel` does.
#guard emitShallowForm false
    (.bdHoare "Top.OTP0./main" chkMainSig (.lit (t := .unit) ())
      .tru (.holds (.res .bool .cur)) EcCmp.ge (EcRealLit.mk 0 1)) chkExpCtx
  == .ok "∀ h : Heap, True → (0 : ℕ) ≤ prEventComp (lowerClosedGame (otpGame \
      false)) h (fun r _ => r = true)"

-- A real constant prints as its numeral at `ℕ`.
#guard emitShallowProb (EcProb.const (EcRealLit.mk 0 1)) chkExpCtx == .ok "(0 : ℕ)"

-- The form of `exp_ll` in `Examples/RestrictedImport.lean`, whose hand-written
-- equation is the specification this printer reproduces: the restriction against
-- the declared global, and the losslessness of the functor image as the bounded
-- Hoare judgement. The hand-written side names the footprint `otpLocs`, which is
-- `globLocs` of the same list.
#guard emitShallowForm false
    (.allModRestr "A" chkAdvInterface [chkKGlobal]
      (.imp (.lossless "A./guess" ⟨.bool, .bool⟩)
        (.bdHoare "Top.Exp0(A)./main" chkMainSig (.lit (t := .unit) ())
          .tru .tru EcCmp.eq (EcRealLit.mk 1 1)))) chkExpCtx
  == .ok "∀ A : ModuleImpl advInterface, ModuleRespectsLocs (globLocs \
      [(EcGlobal.mk \"Top.Otp./k\" 0 EcTy.bool)]) A → (ProcLossless (A.proc \
      \"guess\")) → ∀ h : Heap, True → prEventComp (expImpl A false) h \
      (fun _ _ => True) = (1 : ℕ)"

-- and the equation of that pair is closed by `rfl`, as the hand-written one is.
#guard shallowNeedsPrTrue
    (.allModRestr "A" chkAdvInterface [chkKGlobal]
      (.imp (.lossless "A./guess" ⟨.bool, .bool⟩)
        (.bdHoare "Top.Exp0(A)./main" chkMainSig (.lit (t := .unit) ())
          .tru .tru EcCmp.eq (EcRealLit.mk 1 1)))) == false

-- A binder the body reads only inside a longer identifier prints as `_`.
#guard shallowBinder "r₁ = r₂" "r" == "_"
#guard shallowBinder "r₁ = r₂" "r₁" == "r₁"
#guard shallowBinder "True" "r" == "_"

-- A procedure the caller did not name has no text, rather than a guessed one.
#guard (match emitShallowForm false (.lossless "B./guess" ⟨.bool, .bool⟩) chkExpCtx with
        | .error m => m.startsWith "ec-import: the procedure 'B./guess'"
        | _ => false)

-- A statement reading an operator no binder binds is rejected: an assembled
-- statement binds every operator it reads.
#guard (match emitShallowForm false
            (.isLossless (.opApp "Top.PseudoRF.dK"
              ⟨.unit, .distr (.opaque "Top.PseudoRF.K")⟩ (.lit (t := .unit) ()))) {} with
        | .error m => m.startsWith "ec-import: the abstract operator"
        | _ => false)

-- Two binders of one source name do not collide.
#guard emitShallowForm false
    (.allTy .bool "b" (.allTy .bool "b" (.eqT (.var .bool "b") (.var .bool "b")))) {}
  == .ok "∀ b : EcTy.bool.interp, ∀ b1 : EcTy.bool.interp, b1 = b1"

end Check

end CatCrypt.Crypto.EasyCryptImport

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.EasyCryptImport.Ast
import HaxLean.JsonSize

/-!
# EasyCrypt import: JSON ingestion

This module decodes the EasyCrypt exporter's JSON into the importer's Lean AST
(`Ty.lean`, `Ast.lean`). It is the ingestion half of the exporter boundary: the
exporter serialises EasyCrypt's typed AST after typechecking, and the functions
here turn that serialisation into `EcTy`, `EcExpr`, `EcStmt`, `EcProcAt`,
`EcModule` and `EcGame` values.

**The exporter and this decoder are unverified, and both are in the trust base of
every imported definition.** No theorem relates an `.ec` source file to the
`EcGame` value this module produces; a theorem proved about an imported game is a
theorem about the Lean game, and its relation to the EasyCrypt source holds
modulo the exporter and this decoder. Two properties bound the damage: the
decoder has no default for any field — a missing, mistyped or unrecognised node
is a decode error rather than a plausible-looking value — and the envelope's
schema version must equal `schemaVersion` exactly.

## Schema

The accepted format is the internally tagged JSON of schema version
`schemaVersion`: every node is an object with a `"kind"` discriminator whose
value is EasyCrypt's own constructor name (`Sasgn`, `Eop`, `ME_Structure`,
`Th_module`), and the variant's fields sit alongside it. Exporter drift therefore
surfaces as an unknown `"kind"` rather than as a silent misparse.

## Node table

| JSON node | AST image |
|---|---|
| `Tconstr p []`, `p` in `tyPaths` | the table's `EcTy` |
| `Tconstr p [a, b]`, `p` in `mapTyPaths` | `EcTy.map` at the two decoded arguments |
| `Tconstr p [a]`, `p` in `optionTyPaths` / `listTyPaths` / `fsetTyPaths` / `distrTyPaths` | `EcTy.option` / `EcTy.list` / `EcTy.fset` / `EcTy.distr` at the decoded argument |
| `Evar` at a `distr` code in distribution position | `EcDistr.ofExpr` of the read, the first-class distribution a formal or local holds |
| `Ttuple []` / `Ttuple [t₁, …, tₙ]` | `EcTy.unit` / the right-nested `EcTy.prod`, `t₁ × (t₂ × (… × tₙ))` |
| `Evar` at `PVloc`, `Elocal` | `EcExpr.var` |
| `Eint` at a `fin` code or at `int` | `EcExpr.lit` |
| `Eop p`, `p` in `constPaths` | `EcExpr.lit` |
| `Eop p`, `p` in `emptyMapPaths`, at a `map` code | `EcExpr.lit []` |
| `Eop p`, `p` in `emptyFsetPaths`, at an `fset` code | `EcExpr.lit ∅` |
| `Eop p`, `p` in `emptyListPaths` / `nonePaths`, at a `list` / `option` code | `EcExpr.lit []` / `EcExpr.lit none` |
| `Eop p`, `p` in `witnessPaths`, at any code | `EcExpr.lit default`, the canonical inhabitant — the reading `oget` already takes |
| `Eapp` of `fset1` / `` `|` `` / `mem` | `EcExpr.fsetSingle` / `.fsetUnion` / `.fsetMem` |
| `Eapp` of `Some` / `::` / `rcons` / `size` / `mem` / `nth` | `EcExpr.someE` / `.listCons` / `.listRcons` / `.listSize` / `.listMem` / `.listNth` |
| `Eapp` of `bnot`/`band`/`bxor`/`beq`/`finAdd` | the matching `EcExpr` node |
| `Eapp` of `bor`/`bimp` | the de Morgan image over `bnot`/`band` |
| `Eapp` of integer `+` / `≤` | `EcExpr.intAdd` / `.intLe` |
| `Eapp` of integer `<` | `EcExpr.bnot` of the reversed `.intLe` |
| `Eapp` of `_.[_<-_]` / `dom` | `EcExpr.mapSet` / `.mapMem` |
| `Eapp` of `oget` / `odflt` to `_.[_]` | `EcExpr.mapGetD`, at the value type's canonical inhabitant / at the given default |
| `Etuple [a, b]`, `Eproj` at index 0 / 1 | `EcExpr.pair`, `EcExpr.fst` / `.snd` |
| `Sasgn` to `PVloc` | `EcStmt.assign` |
| `Sasgn` to an `LvTuple` of locals | `EcStmt.assignTuple` |
| `Sasgn` to `PVloc` of an `Evar` at `PVglob` | `EcStmt.load` |
| `Sasgn` to `PVglob` | `EcStmt.store` |
| a registered global read inside a statement's expression | an `EcStmt.load` into a hoisted local prepended to the statement, the read rewritten to that local (`hoistGlobalReads`) |
| `Srnd` from a declared-uniform nullary operator | `EcStmt.sample` |
| `Srnd` from `dunit` / `dmap` / `dcond` / `(\)` / `dlet` / `` `*` `` / `dscale` / `drestrict` | `EcStmt.sampleD` at the matching `EcDistr` |
| `Equant` of one `ELambda` binder, as a distribution operator's function argument | the binder and body of `EcDistr.map` / `.cond` / `.letD` / `.restrict` |
| `Sif` | `EcStmt.ite` |
| `Swhile` of the bounded idiom, after its initialisation | `EcStmt.forN` |
| `Scall` without an lvalue, to the enclosing module | `EcStmt.call` |
| `Scall` without an lvalue, at a cross-path in `procSigs` | `EcStmt.callProc`, the result bound to the anonymous local |
| `Scall` with an lvalue | `EcStmt.callProc` |
| `Scall` with an `LvTuple` lvalue | `EcStmt.callProcTuple` |
| procedure with an `FBdef` body | `EcProcAt`, binding every formal of `sig.args` in declaration order; `sig.argty` is checked against the formals' types |
| procedure with an `FBalias` body, at a target in `procSigs` | `EcProcAt` whose body is one `EcStmt.callProc` to the target and whose return expression is that call's result (`decodeAliasBody`) |
| `Th_module` of `ME_Structure` without parameters | `EcModule`, and `EcGame` through `decodeGame` |
| `Th_module` of `ME_Structure` with one parameter | `EcFunctor` through `decodeFunctor` |
| `Th_module` of `ME_Structure` with any number of parameters | `EcFunctorN` through `decodeFunctorN` (`FunctorN.lean`) |
| a module type's `sig`, without parameters | `EcInterface` through `decodeModSig` |
| a `ModuleType` node in parameter position, its own parameters included | `EcInterface` through `decodeModTypeSig` |
| a `Th_modtype` with parameters | `EcModTypeN` through `decodeModTypeN` (`FunctorN.lean`) |
| `Th_type` of an `Abstract` body | a type-table entry at `EcTy.opaque`, through `decodeThType` |
| `Th_type` of a parameter-free `Concrete` body | a type-table entry at the decoded right-hand code, through `registerThTypes` |
| the `Th_type` items of a `Th_theory` item, theory-inner theories included | type-table entries at their fully qualified paths, through `registerThTypes` |
| `Th_type` of a `Datatype` body whose constructors take no argument | a type-table entry at `EcTy.fin` of the constructor count and one constant per constructor, through `decodeThTypeEnum` |
| `Th_type` carrying a `subtype` payload | `EcSubtypeDecl` through `decodeThTypeSubtype`, and a type-table entry at the realization of its bound (`registerThTypesAt`) |
| `Th_clear` | the paths it clears, through `decodeThClear` |

Boolean literals arrive as nullary operators (`Eop` at `Top.Pervasive.true`), and
application is curried with an argument list, so an operator's arity is checked
against the list length. Operator, type-constructor and distribution paths are
dispatch keys held by the ingestion, in `DecodeTables`: `ecPrelude` holds the
paths of EasyCrypt's boolean, unit and integer prelude, of its finite maps, and
of the distribution operators of the fragment, and
`DecodeTables.withFinType` / `.withIntType` / `.withMapType` / `.withOptionType` /
`.withListType` / `.withEmptyMap` / `.withUniformDistr` / `.withDistrOp` /
`.withGlobal` extend it. A path outside the
tables is a decode error, so a distribution operator the ingestion has not
registered can never decode to a sample, and only a nullary operator in
`distrPaths` decodes to the uniform `EcStmt.sample`.

## What `oget` reads at an unbound key

EasyCrypt's `oget None` is `witness`, an unspecified inhabitant of the type, and
`EcExpr.mapGetD` takes its default as an argument. `oget m.[k]` therefore decodes
at `EcExpr.lit default`, the canonical inhabitant `EcTy.interp` carries. This
fixes a value EasyCrypt leaves open: a Lean theorem about the imported program is
a theorem about that reading, and `odflt d m.[k]`, whose default the source
writes, is the shape with no such choice in it.

## Nodes with no image

* A `Swhile` node outside the bounded idiom: `EcStmt.forN` carries an iteration
  count, which the guard, the body and the statement before the loop have to
  determine together. The idiom, and what each near-miss reports, is stated at
  `DecodedItem` below.
* The finite-map lookup `m.[k]` on its own: its image would be an option-valued
  lookup node, which the AST does not have, so it decodes only under `oget` or
  `odflt`.
* A module whose body is an `ME_Alias` — one defined as an application of another
  module — rejected by body kind: the alias names the applied module by path and
  no body sits behind it.
* An identifier exported as a name with a uniqueness stamp: dropping the stamp
  makes two distinct binders of the same source name alias, so the object form
  of an identifier is rejected rather than truncated, and a stamped identifier
  node without a `stamp` field is a decode error rather than a program variable
  of that name.
* A call whose result is discarded, whose target is outside the enclosing
  module, and whose cross-path is not in `procSigs`: the schema carries no
  result type at such a call site, so the signature comes from the table — a
  functor parameter's procedures register from its module type, and an
  envelope module's from its decoded structure — and a callee outside it, an
  applied-functor path such as `O(S)./init` among them, is rejected.
* An `FBalias` procedure body whose target is a procedure of an applied functor,
  a procedure of the module the alias sits in, or a cross-path outside
  `procSigs`; and one whose target resolves at a signature other than the
  alias's own. The four scopes and what each does are stated at
  `decodeAliasBody`.
* The distribution operators outside `distrOpPaths` — `dnull`, `dbiased`,
  `dbin`, `duniform` over a list, `dlist`, `dfun`, `dopt`, `dfold`, `dinter` —
  each rejected by path.
* `Eif`, `Elet`, `Ematch`, `Smatch`, `Sraise`, `Sabstract`,
  `FBabs`, `Tfun`, nested modules, module parameters, and tuple expressions
  of arity above two (the tuple *type* decodes as a right-nested product, but
  `Etuple` and `Eproj` stay binary): each is rejected with a message naming
  the construct. `Equant` is rejected in expression position, and decodes only
  as a distribution operator's one-binder function argument. An `LvTuple`
  decodes under an assignment and under a call; under a random sample, and
  with a global component, it is rejected.
* A `Datatype` declaration with a constructor that takes an argument, or with no
  constructor at all: the first is a sum, which `EcTy` has no code for, and the
  second denotes the empty type, which no code interprets.
* A `PR_Ind` operator body, an inductive predicate: it holds of exactly what its
  constructors derive, and a parameter at an `EcSig` is a value a statement
  quantifies over rather than a definition.
* A `subtype` declaration at a carrier with no code, or with a predicate outside
  the integer-range shape: the type a predicate cuts out is the predicate, so a
  predicate read approximately would name a different type. The path registers as
  pending at the reason, so a type node naming it reports that.
* An `Unsupported` node, which the exporter emits for every construct outside
  its own coverage — formula positions among them — is a decode error carrying
  the exporter's `what` and `pp` fields.

## Totality

Every decoder is a `def`, not a `partial def`: recursion on the JSON tree is
well-founded for the `jsonSize` measure, with `getObj_decreases` and
`getArr_decreases` supplying the strict decrease for field lookups and for array
elements.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.EasyCryptImport

open Lean (Json)
open Hax.JsonSize

/-! ## Errors and field access -/

/-- The schema name the envelope must carry. -/
def schemaName : String := "catcrypt-ec-export"

/-- The schema version this decoder accepts, compared for exact equality. -/
def schemaVersion : Nat := 10

/-- A decode error, tagged with the pipeline stage. -/
def fail {α : Type} (msg : String) : Except String α :=
  .error ("ec-import: " ++ msg)

/-- The value of a field, or an error naming the field and the node. -/
def getObj (j : Json) (k : String) : Except String Json :=
  match j.getObjVal? k with
  | .ok v => .ok v
  | .error _ => fail s!"missing field '{k}' in {j.compress}"

/-- A field lookup strictly decreases the `jsonSize` measure. -/
theorem getObj_decreases {j : Json} {k : String} {v : Json}
    (h : getObj j k = .ok v) : jsonSize v < jsonSize j := by
  unfold getObj at h
  cases hv : j.getObjVal? k with
  | error e => rw [hv] at h; simp [fail] at h
  | ok w =>
    rw [hv] at h
    have hw : w = v := by simpa using h
    subst hw
    exact getObjVal?_decreases hv

/-- The array value of a field, or an error naming the field and the node. -/
def getArr (j : Json) (k : String) : Except String (Array Json) :=
  match j.getObjVal? k with
  | .ok (.arr a) => .ok a
  | .ok v => fail s!"field '{k}' is not an array: {v.compress}"
  | .error _ => fail s!"missing field '{k}' in {j.compress}"

/-- Every element of an array-valued field strictly decreases the `jsonSize`
measure. -/
theorem getArr_decreases {j : Json} {k : String} {arr : Array Json} {x : Json}
    (h : getArr j k = .ok arr) (hx : x ∈ arr) : jsonSize x < jsonSize j := by
  unfold getArr at h
  cases hv : j.getObjVal? k with
  | error e => rw [hv] at h; simp [fail] at h
  | ok w =>
    rw [hv] at h
    cases w with
    | arr a =>
      have ha : a = arr := by simpa using h
      subst ha
      exact Nat.lt_trans (jsonSize_lt_of_mem_arr hx) (getObjVal?_decreases hv)
    | null => simp [fail] at h
    | bool b => simp [fail] at h
    | num v => simp [fail] at h
    | str s => simp [fail] at h
    | obj kvs => simp [fail] at h

/-- The string value of a field, or an error naming the field and the node. -/
def getStr (j : Json) (k : String) : Except String String :=
  match j.getObjValAs? String k with
  | .ok s => .ok s
  | .error _ => fail s!"missing or non-string field '{k}' in {j.compress}"

/-- The natural-number value of a field, or an error naming the field and the
node. -/
def getNat (j : Json) (k : String) : Except String Nat :=
  match j.getObjValAs? Nat k with
  | .ok n => .ok n
  | .error _ => fail s!"missing or non-numeric field '{k}' in {j.compress}"

/-- The string value of an optional field. -/
def getStrOpt (j : Json) (k : String) : Option String :=
  match j.getObjValAs? String k with
  | .ok s => some s
  | .error _ => none

/-- The name of a source identifier. An identifier exported as an object carries
a uniqueness stamp, and a name read without its stamp aliases distinct binders,
so only the string form decodes. -/
def getIdent (j : Json) (k : String) : Except String String :=
  match j.getObjVal? k with
  | .ok (.str s) => .ok s
  | .ok (.obj _) =>
    fail s!"identifier '{k}' carries a uniqueness stamp in {j.compress}: a name \
      read without its stamp aliases distinct binders of the same source name"
  | .ok v => fail s!"identifier '{k}' is not a name: {v.compress}"
  | .error _ => fail s!"missing identifier '{k}' in {j.compress}"

/-- The identity of a stamped EasyCrypt identifier: the source name and the
uniqueness stamp, both read from the node. The stamp is what tells two binders of
one source name apart, so it is required rather than defaulted. -/
def getStampedIdent (j : Json) : Except String EcVarId := do
  let nm ← getIdent j "name"
  let st ← getNat j "stamp"
  .ok { name := nm, stamp := some st }

/-- The message for a node the exporter marked as outside its coverage. -/
def unsupportedMsg (j : Json) : String :=
  let what := (getStrOpt j "what").getD "?"
  let pp := (getStrOpt j "pp").getD ""
  s!"the exporter marked this node unsupported: what='{what}' pp='{pp}'"

/-- The last component of an EasyCrypt path, which is the procedure or variable
name a qualified name ends in. -/
def lastComponent (q : String) : String :=
  let bySlash := (q.splitOn "/").getLast?.getD q
  (bySlash.splitOn ".").getLast?.getD bySlash

/-! ## Dispatch tables

The exporter names operators, type constructors and distributions by their
EasyCrypt paths. The mapping from those paths to AST constructors belongs to the
ingestion: a `fin n` code carries a cardinality that no EasyCrypt type node
does, and `EcStmt.sample` is uniform on its carrier, so exactly which
distribution operators are the uniform ones is a decision the ingestion records
rather than reads. -/

/-- The operators of the accepted fragment, as dispatch-table targets. -/
inductive EcOpKind where
  /-- Boolean negation. -/
  | bnot
  /-- Boolean conjunction. -/
  | band
  /-- Boolean disjunction, decoded through its de Morgan image. -/
  | bor
  /-- Boolean implication, decoded through its de Morgan image. -/
  | bimp
  /-- Boolean exclusive-or. -/
  | bxor
  /-- Decidable equality. -/
  | beq
  /-- Addition on a finite scalar type. -/
  | finAdd
  /-- Integer addition. -/
  | intAdd
  /-- Integer multiplication. -/
  | intMul
  /-- Integer negation. -/
  | intOpp
  /-- Euclidean division, EasyCrypt's `edivz`, whose result is the quotient and
  the remainder as a pair. -/
  | intEdivz
  /-- The integer order, `a ≤ b`. -/
  | intLe
  /-- The strict integer order, decoded through `¬ (b ≤ a)`. -/
  | intLt
  /-- Binding a key in a finite map. -/
  | mapSet
  /-- Membership of a key in a finite map, EasyCrypt's `dom`. -/
  | mapMem
  /-- The lookup `m.[k]`, whose result is an option and which decodes only under
  `oget` or `odflt`. -/
  | mapLookup
  /-- `oget m.[k]`, the lookup at the canonical inhabitant of the value type. -/
  | mapOget
  /-- `odflt d m.[k]`, the lookup at an explicit default. -/
  | mapOdflt
  /-- The singleton finite set, EasyCrypt's `fset1`. -/
  | fsetSingle
  /-- The union of two finite sets, EasyCrypt's `` (`|`) ``. -/
  | fsetUnion
  /-- Membership in a finite set, EasyCrypt's `mem`. -/
  | fsetMem
  /-- The present option value, EasyCrypt's `Some`. -/
  | someE
  /-- List cons, EasyCrypt's `::`. -/
  | listCons
  /-- Appending one element at the end of a list, EasyCrypt's `rcons`. -/
  | listRcons
  /-- The length of a list, EasyCrypt's `size`. -/
  | listSize
  /-- Membership in a list, EasyCrypt's `mem`. -/
  | listMem
  /-- The `i`-th element of a list or a default, EasyCrypt's `nth`. -/
  | listNth
  deriving DecidableEq, Repr

/-- The distribution operators of the accepted fragment, as dispatch-table
targets. -/
inductive EcDistrOpKind where
  /-- The point mass, EasyCrypt's `dunit`. -/
  | dunit
  /-- The pushforward along a function, EasyCrypt's `dmap`. -/
  | dmap
  /-- Conditioning on a predicate, EasyCrypt's `dcond`. -/
  | dcond
  /-- Conditioning on the complement of a predicate, EasyCrypt's `(\)`. -/
  | dexcepted
  /-- The bind, EasyCrypt's `dlet`. -/
  | dlet
  /-- The independent product, EasyCrypt's ``(`*`)``. -/
  | dprod
  /-- Rescaling to mass one, EasyCrypt's `dscale`. -/
  | dscale
  /-- Restriction to a predicate, EasyCrypt's `drestrict`. -/
  | drestrict
  deriving DecidableEq, Repr

/-- A concrete operator declaration — EasyCrypt's `op f x₁ … xₙ = e`, where the
source fixes the operator's value instead of leaving it open.

The record holds the operator's own parameters, in source order, each at the
type code the declared type gives it, the result code the definition lands in,
and the body node the source writes the operator equal to. The body's free
variables are exactly `params`: an operator definition is closed, and every
other name it reads is an operator path.

A read of the operator expands to this definition, with the arguments of the
application bound to `params`. That expansion is the operator's meaning, and it
comes from the source. This is a different kind of entry from `opPaths`, where
the ingestion commits an EasyCrypt path to a Lean operation of its own choosing
and a wrong commitment produces a well-formed statement about a different
operator; here the operator's meaning is read off the declaration and nothing is
chosen.

Registering the definition rather than a name plus a defining equation keeps the
statement that reads the operator closed: a named constant carries no value, so
it needs its equation as a hypothesis on every statement that reads it, and the
statement is then about any realization satisfying that equation rather than
about the one the source names. Expanding also needs no `EcTerm` constructor
beyond `letIn`, which binds the parameters to the arguments at the read site. -/
structure EcOpDefn where
  /-- The operator's own path. -/
  path : String
  /-- The parameters, in source order, at their declared type codes. A nullary
  definition has none. -/
  params : List (EcVarId × EcTy)
  /-- The type code the definition's body has. -/
  res : EcTy
  /-- The body node, in the exporter's formula syntax. -/
  body : Json

/-- A definition the source writes over type parameters, kept as the exporter
wrote it.

`EcOpDefn` holds a definition whose parameter and result types are already codes,
which a polymorphic definition has none of until its type parameters are given
values. `associative ['a] (f : 'a -> 'a -> 'a)` is the shape: `'a` has no code
until the read site says what it is, and `f` has none at all, since `EcTy` has no
arrow. Both are read at a use site instead — the type arguments the node carries
give `'a` a code, and the value arguments replace the parameters in the body
before it is decoded, which is why the body stays a `Json` here and the
parameters stay the binder nodes the exporter wrote. -/
structure EcPolyOpDefn where
  /-- The operator's own path. -/
  path : String
  /-- The type parameters the declaration binds, in source order. -/
  tyParams : List String
  /-- The declaration node, whose defining form is the lambda over the value
  parameters. -/
  decl : Json

/-- The ingestion's dispatch tables: the EasyCrypt paths this decoder
recognises, and the module context it decodes in. Every lookup that misses is a
decode error. -/
structure DecodeTables where
  /-- Nullary type constructors and the `EcTy` code each denotes. -/
  tyPaths : List (String × EcTy)
  /-- Binary type constructors that denote the finite map at their two type
  arguments. -/
  mapTyPaths : List String
  /-- Unary type constructors that denote the option at their type argument. -/
  optionTyPaths : List String
  /-- Unary type constructors that denote the list at their type argument. -/
  listTyPaths : List String
  /-- Unary type constructors that denote the finite set at their type
  argument. -/
  fsetTyPaths : List String
  /-- Nullary operators that denote a literal. -/
  constPaths : List (String × EcVal)
  /-- Nullary operators that denote the empty finite map. -/
  emptyMapPaths : List String
  /-- Nullary operators that denote the empty finite set. -/
  emptyFsetPaths : List String
  /-- Nullary operators that denote the empty list. -/
  emptyListPaths : List String
  /-- Nullary operators that denote the absent option value. -/
  nonePaths : List String
  /-- Nullary operators that denote a type's unspecified inhabitant,
  EasyCrypt's `witness`. Like the `oget` default, its image is the canonical
  inhabitant the interpretation carries: a decision the ingestion records
  where EasyCrypt leaves the value open, so a theorem about the imported
  program is a theorem about that reading. -/
  witnessPaths : List String
  /-- Operators of the accepted fragment. -/
  opPaths : List (String × EcOpKind)
  /-- Nullary operators that denote the uniform distribution on their carrier. -/
  distrPaths : List String
  /-- Distribution operators of the accepted fragment. -/
  distrOpPaths : List (String × EcDistrOpKind)
  /-- Type constructors of distributions, `'a distr`. A type node names either
  EasyCrypt's declaration of the type, `Top.Pervasive.distr`, or the alias
  `Distr.ec` defines for it, `Top.Distr.distr`; the two denote one constructor,
  so both spellings decode at the same code. -/
  distrTyPaths : List String
  /-- Abstract operator declarations, keyed by the operator's path, at the
  signature its declaration gives it. An operator registered here is a parameter
  of the statement that reads it, not a value the ingestion knows
  (`Params.lean`), and a read of it decodes to `EcTerm.opApp` at the recorded
  signature. -/
  absOpPaths : List (String × EcSig)
  /-- Concrete operator declarations, keyed by the operator's path, at the
  definition its declaration gives it. An operator registered here is a
  definition the source fixes, not a parameter, and a read of it expands to the
  definition (`EcOpDefn`). A path this table holds is held by no other operator
  table: `decodeThOperatorConcrete` rejects a definition at a path the ingestion
  has already committed to a meaning of its own. -/
  defOpPaths : List (String × EcOpDefn)
  /-- The definitions the source writes over type parameters, keyed by path. A
  read of one expands at the type arguments its node carries; the declaration is
  held as written, since it has no codes until then. -/
  polyOpPaths : List (String × EcPolyOpDefn)
  /-- Module-scoped globals, keyed by the qualified name the exporter uses. -/
  globals : List (String × EcGlobal)
  /-- Procedure signatures, keyed by the cross-path a call site writes. A call
  that discards its result carries no result type of its own, so its signature
  resolves here: a functor parameter's procedures register from the module
  type it is declared at, and an envelope module's from its decoded
  structure. -/
  procSigs : List (String × EcSig)
  /-- Subtype declarations the ingestion read and holds no code for, keyed by the
  subtype's path, at the reason there is none. The entry gives the path no code,
  so a type node at it is a decode error; what the entry buys is that the error
  names the subtype and the reason instead of reporting a path the ingestion
  never saw. -/
  pendingSubtypes : List (String × String)
  /-- The path of the module being decoded, against which a call target is
  recognised as intra-module. -/
  modPath : String

/-- The paths of EasyCrypt's boolean, unit and integer prelude, its finite maps,
the uniform distribution on `bool`, and the distribution operators of the
accepted fragment. -/
def ecPrelude : DecodeTables where
  tyPaths :=
    [("Top.Pervasive.bool", .bool), ("Top.Pervasive.unit", .unit),
     ("Top.Pervasive.int", .int)]
  mapTyPaths := ["Top.FMap.fmap"]
  optionTyPaths := ["Top.Logic.option"]
  listTyPaths := ["Top.List.list"]
  fsetTyPaths := ["Top.FSet.fset"]
  constPaths :=
    [("Top.Pervasive.true", ⟨.bool, true⟩),
     ("Top.Pervasive.false", ⟨.bool, false⟩),
     ("Top.Pervasive.tt", ⟨.unit, ()⟩)]
  emptyMapPaths := ["Top.FMap.empty"]
  emptyFsetPaths := ["Top.FSet.fset0"]
  emptyListPaths := ["Top.List.[]"]
  nonePaths := ["Top.Logic.None"]
  witnessPaths := ["Top.Pervasive.witness"]
  opPaths :=
    [("Top.Pervasive.[!]", .bnot),
     ("Top.Pervasive./\\", .band),
     ("Top.Pervasive.&&", .band),
     ("Top.Pervasive.\\/", .bor),
     ("Top.Pervasive.||", .bor),
     ("Top.Pervasive.=>", .bimp),
     ("Top.Logic.^", .bxor),
     ("Top.Pervasive.=", .beq),
     ("Top.CoreInt.add", .intAdd),
     ("Top.CoreInt.mul", .intMul),
     ("Top.CoreInt.opp", .intOpp),
     ("Top.IntDiv.edivz", .intEdivz),
     ("Top.CoreInt.le", .intLe),
     ("Top.CoreInt.lt", .intLt),
     ("Top.FMap._.[_<-_]", .mapSet),
     ("Top.FMap._.[_]", .mapLookup),
     ("Top.FMap.dom", .mapMem),
     ("Top.Logic.oget", .mapOget),
     ("Top.Logic.odflt", .mapOdflt),
     ("Top.FSet.fset1", .fsetSingle),
     ("Top.FSet.`|`", .fsetUnion),
     ("Top.FSet.mem", .fsetMem),
     ("Top.Logic.Some", .someE),
     ("Top.List.::", .listCons),
     ("Top.List.rcons", .listRcons),
     ("Top.List.size", .listSize),
     ("Top.List.mem", .listMem),
     ("Top.List.nth", .listNth)]
  distrPaths := ["Top.DBool.dbool"]
  distrOpPaths :=
    [("Top.Distr.MUnit.dunit", .dunit),
     ("Top.Distr.dmap", .dmap),
     ("Top.Distr.DConditional.dcond", .dcond),
     ("Top.Dexcepted.\\", .dexcepted),
     ("Top.Distr.dlet", .dlet),
     ("Top.Distr.`*`", .dprod),
     ("Top.Distr.dscale", .dscale),
     ("Top.Distr.drestrict", .drestrict)]
  distrTyPaths := ["Top.Distr.distr", "Top.Pervasive.distr"]
  absOpPaths := []
  defOpPaths := []
  polyOpPaths := []
  globals := []
  procSigs := []
  pendingSubtypes := []
  modPath := ""

/-- Extend the tables with a finite scalar type of cardinality `n`, read from the
EasyCrypt type path `tyPath`, and its addition at `addPath`. -/
def DecodeTables.withFinType (T : DecodeTables) (tyPath : String) (n : Nat)
    (addPath : String) (pos : 0 < n := by omega) : DecodeTables :=
  { T with
    tyPaths := (tyPath, .fin n pos) :: T.tyPaths
    opPaths := (addPath, .finAdd) :: T.opPaths }

/-- Extend the tables with EasyCrypt's `int`, read from the type path
`tyPath`. -/
def DecodeTables.withIntType (T : DecodeTables) (tyPath : String) : DecodeTables :=
  { T with tyPaths := (tyPath, .int) :: T.tyPaths }

/-- Extend the tables with an abstract type at the type path `tyPath`, whose
code is `EcTy.opaque tyPath`. The code's carrier is fixed (see `Ty.lean`); what
the entry records is that the path names an abstract type, so a `Tconstr` at it
decodes rather than missing the table. -/
def DecodeTables.withOpaqueType (T : DecodeTables) (tyPath : String) :
    DecodeTables :=
  { T with tyPaths := (tyPath, .opaque tyPath) :: T.tyPaths }

/-- Extend the tables with an abstract operator declared at `path`, at the
signature `s` its declaration gives it. A read of the operator decodes to
`EcTerm.opApp` at `s`, and the statement that reads it quantifies over the
realization (`EcForm.allOp`). -/
def DecodeTables.withAbstractOp (T : DecodeTables) (path : String) (s : EcSig) :
    DecodeTables :=
  { T with absOpPaths := (path, s) :: T.absOpPaths }

/-- Extend the tables with the concrete operator `d` defines. A read of the
operator expands to `d`'s body under `d`'s parameters. -/
def DecodeTables.withConcreteOp (T : DecodeTables) (d : EcOpDefn) : DecodeTables :=
  { T with defOpPaths := (d.path, d) :: T.defOpPaths }

/-- Extend the tables with a definition written over type parameters, at its own
path. -/
def DecodeTables.withPolyOp (T : DecodeTables) (d : EcPolyOpDefn) :
    DecodeTables :=
  { T with polyOpPaths := (d.path, d) :: T.polyOpPaths }

/-- The name of the table that already gives `path` a meaning, when one does.

These are the tables whose entries the ingestion chooses: an entry says that an
EasyCrypt path denotes a particular Lean operation, value or code. A path they
hold decodes through them in both readers — the expression reader of this module
and the term reader of `FormJson.lean` — and `EcExpr` has neither a binder nor a
conditional, so a definition expanded at such a path would decode one way in a
formula and not at all in a program. The committed entry therefore takes
precedence, and a concrete declaration at such a path does not register. -/
def DecodeTables.opMeaningOwner (T : DecodeTables) (path : String) :
    Option String :=
  if (List.lookup path T.opPaths).isSome then some "opPaths"
  else if (List.lookup path T.constPaths).isSome then some "constPaths"
  else if (List.lookup path T.distrOpPaths).isSome then some "distrOpPaths"
  else if T.emptyMapPaths.contains path then some "emptyMapPaths"
  else if T.emptyFsetPaths.contains path then some "emptyFsetPaths"
  else if T.emptyListPaths.contains path then some "emptyListPaths"
  else if T.nonePaths.contains path then some "nonePaths"
  else if T.witnessPaths.contains path then some "witnessPaths"
  else if T.distrPaths.contains path then some "distrPaths"
  else if (List.lookup path T.absOpPaths).isSome then some "absOpPaths"
  else none

/-- Extend the tables with a finite-map type constructor at the type path
`tyPath`. An EasyCrypt `fmap` is a binary type constructor, and its two type
arguments are the key and value codes `decodeTy` reads off the node. -/
def DecodeTables.withMapType (T : DecodeTables) (tyPath : String) : DecodeTables :=
  { T with mapTyPaths := tyPath :: T.mapTyPaths }

/-- Extend the tables with an option type constructor at the type path
`tyPath`. -/
def DecodeTables.withOptionType (T : DecodeTables) (tyPath : String) :
    DecodeTables :=
  { T with optionTyPaths := tyPath :: T.optionTyPaths }

/-- Extend the tables with a list type constructor at the type path `tyPath`. -/
def DecodeTables.withListType (T : DecodeTables) (tyPath : String) :
    DecodeTables :=
  { T with listTyPaths := tyPath :: T.listTyPaths }

/-- Extend the tables with a finite-set type constructor at the type path
`tyPath`. -/
def DecodeTables.withFsetType (T : DecodeTables) (tyPath : String) :
    DecodeTables :=
  { T with fsetTyPaths := tyPath :: T.fsetTyPaths }

/-- Extend the tables with a nullary operator that denotes the empty finite
set. -/
def DecodeTables.withEmptyFset (T : DecodeTables) (path : String) : DecodeTables :=
  { T with emptyFsetPaths := path :: T.emptyFsetPaths }

/-- Extend the tables with a type alias: a `Tconstr` at `tyPath` decodes as the
code `t` the alias's right-hand side decoded to. -/
def DecodeTables.withAliasType (T : DecodeTables) (tyPath : String) (t : EcTy) :
    DecodeTables :=
  { T with tyPaths := (tyPath, t) :: T.tyPaths }

/-- Extend the tables with a nullary operator that denotes the empty finite
map. -/
def DecodeTables.withEmptyMap (T : DecodeTables) (path : String) : DecodeTables :=
  { T with emptyMapPaths := path :: T.emptyMapPaths }

/-- Extend the tables with an operator that denotes the uniform distribution on
its carrier. -/
def DecodeTables.withUniformDistr (T : DecodeTables) (path : String) :
    DecodeTables :=
  { T with distrPaths := path :: T.distrPaths }

/-- Extend the tables with a distribution operator of the accepted fragment,
read from the EasyCrypt path `path`. The operators of the fragment are in
`ecPrelude` at their theory paths; this is how a source that renames or clones one
of them is registered. -/
def DecodeTables.withDistrOp (T : DecodeTables) (path : String)
    (k : EcDistrOpKind) : DecodeTables :=
  { T with distrOpPaths := (path, k) :: T.distrOpPaths }

/-- Extend the tables with a module-scoped global. -/
def DecodeTables.withGlobal (T : DecodeTables) (g : EcGlobal) : DecodeTables :=
  { T with globals := (g.name, g) :: T.globals }

/-- Extend the tables with a procedure signature at the cross-path a call site
writes. -/
def DecodeTables.withProcSig (T : DecodeTables) (q : String) (s : EcSig) :
    DecodeTables :=
  { T with procSigs := (q, s) :: T.procSigs }

/-- Extend the tables with the procedure signatures of an interface, keyed by
the cross-paths a body calls them by: `xqualify pfx p` for each declared
`p`. This is how a functor parameter's procedures become resolvable at a call
site that carries no result type of its own. -/
def DecodeTables.withInterfaceX (T : DecodeTables) (pfx : String)
    (I : EcInterface) : DecodeTables :=
  I.names.foldl (fun T p => T.withProcSig (xqualify pfx p) (I.sig p)) T

/-! ## Casts

The AST is intrinsically typed, so a decoder that produced a value at the code it
read transports it to the code the context expects. -/

/-- Transport a dynamically typed value to a code it is equal to. -/
def EcVal.transport (v : EcVal) {t : EcTy} (h : v.ty = t) : t.interp :=
  cast (congrArg EcTy.interp h) v.val

/-- Transport an expression along an equality of type codes. -/
def EcExpr.castTy {a b : EcTy} (h : a = b) (e : EcExpr a) : EcExpr b :=
  cast (congrArg EcExpr h) e

/-- Transport a procedure along an equality of signatures. -/
def EcProcAt.castSig {s s' : EcSig} (h : s = s') (p : EcProcAt s) : EcProcAt s' :=
  cast (congrArg EcProcAt h) p

/-! ## Types -/

/-- The right-nested product of the type codes `a :: rest`, which is the image
of a tuple type: an `n`-ary tuple reads as `t₁ × (t₂ × (… × tₙ))`, and a value
of it destructures by that nesting — a triple's components are `fst`,
`fst ∘ snd` and `snd ∘ snd`. -/
def nestTuple (a : EcTy) : List EcTy → EcTy
  | [] => a
  | b :: rest => .prod a (nestTuple b rest)

/-- Decode an EasyCrypt type node. -/
def decodeTy (T : DecodeTables) (j : Json) : Except String EcTy :=
  match getStr j "kind" with
  | .error e => .error e
  | .ok "Tconstr" =>
    match getStr j "path" with
    | .error e => .error e
    | .ok p =>
      match _hargs : getArr j "args" with
      | .error e => .error e
      | .ok args =>
        if args.isEmpty then
          match List.lookup p T.tyPaths with
          | some t => .ok t
          | none =>
            match List.lookup p T.pendingSubtypes with
            | some why =>
              fail s!"type path '{p}' names a subtype the ingestion holds no \
                code for: {why}"
            | none =>
              fail s!"unknown type path '{p}': the ingestion's type table has no \
                entry, so the type has no EcTy code"
        else if T.mapTyPaths.contains p then
          match args.toList.attach with
          | [⟨kJ, _⟩, ⟨vJ, _⟩] =>
            match decodeTy T kJ with
            | .error e => .error e
            | .ok k =>
              if !k.hasEq then
                fail s!"finite-map type constructor '{p}' at the key type \
                  {repr k}: a lookup compares keys, and that type has no \
                  decidable equality"
              else
                match decodeTy T vJ with
                | .error e => .error e
                | .ok v => .ok (.map k v)
          | _ =>
            fail s!"finite-map type constructor '{p}' applied to {args.size} \
              arguments, expected 2"
        else if T.optionTyPaths.contains p then
          match args.toList.attach with
          | [⟨aJ, _⟩] =>
            match decodeTy T aJ with
            | .error e => .error e
            | .ok a => .ok (.option a)
          | _ =>
            fail s!"option type constructor '{p}' applied to {args.size} \
              arguments, expected 1"
        else if T.listTyPaths.contains p then
          match args.toList.attach with
          | [⟨aJ, _⟩] =>
            match decodeTy T aJ with
            | .error e => .error e
            | .ok a => .ok (.list a)
          | _ =>
            fail s!"list type constructor '{p}' applied to {args.size} \
              arguments, expected 1"
        else if T.fsetTyPaths.contains p then
          match args.toList.attach with
          | [⟨aJ, _⟩] =>
            match decodeTy T aJ with
            | .error e => .error e
            | .ok a =>
              if !a.hasEq then
                fail s!"finite-set type constructor '{p}' at the element type \
                  {repr a}: a finite set compares its elements, and that type \
                  has no decidable equality"
              else .ok (.fset a)
          | _ =>
            fail s!"finite-set type constructor '{p}' applied to {args.size} \
              arguments, expected 1"
        else if T.distrTyPaths.contains p then
          match args.toList.attach with
          | [⟨aJ, _⟩] =>
            match decodeTy T aJ with
            | .error e => .error e
            | .ok a => .ok (.distr a)
          | _ =>
            fail s!"distribution type constructor '{p}' applied to {args.size} \
              arguments, expected 1"
        else
          fail s!"parameterised type constructor '{p}': EcTy's parameterised \
            codes are the finite map, the option and the list, and the \
            ingestion's tables have no entry for the path"
  | .ok "Ttuple" =>
    match _harr : getArr j "args" with
    | .error e => .error e
    | .ok arr =>
      match arr.toList.attach.mapM (fun ⟨a, _⟩ => decodeTy T a) with
      | .error e => .error e
      | .ok ts =>
        match ts with
        | [] => .ok .unit
        | [_] =>
          fail s!"tuple type of arity 1: the exporter writes no such node, so \
            it has no image"
        | a :: rest => .ok (nestTuple a rest)
  | .ok "Unsupported" => fail (unsupportedMsg j)
  | .ok k => fail s!"unsupported type node kind '{k}' in {j.compress}"
termination_by jsonSize j
decreasing_by
  all_goals first
    | exact getArr_decreases _hargs (Array.mem_toList_iff.mp ‹_ ∈ Array.toList _›)
    | exact getArr_decreases _harr (Array.mem_toList_iff.mp ‹_ ∈ Array.toList _›)

/-- Decode the type node the field `k` of `j` holds. -/
def decodeTyField (T : DecodeTables) (j : Json) (k : String) : Except String EcTy := do
  let tyJ ← getObj j k
  decodeTy T tyJ

/-- Check that an expression node's own `ty` field is the code the context
expects. -/
def checkNodeTy (T : DecodeTables) (t : EcTy) (j : Json) : Except String Unit := do
  let t' ← decodeTyField T j "ty"
  if t' = t then .ok ()
  else
    fail s!"type mismatch: node has type {repr t'}, context expects {repr t}, \
      in {j.compress}"

/-! ## Expressions

Decoding is type-directed: `decodeExpr T t j` produces an `EcExpr t`, and the
node's own `ty` field must agree with `t`. The expected code also selects the
constructor — an `Etuple` decodes only at a `prod` code, an `Eint` only at a
`fin` code — so a node the AST cannot type is an error rather than a coercion. -/

/-- Decode an EasyCrypt expression node at the type code `t`. -/
def decodeExpr (T : DecodeTables) (t : EcTy) (j : Json) : Except String (EcExpr t) :=
  match checkNodeTy T t j with
  | .error e => .error e
  | .ok () =>
    match getStr j "kind" with
    | .error e => .error e
    | .ok "Elocal" =>
      match getStampedIdent j with
      | .error e => .error e
      | .ok x => .ok (.var t x)
    | .ok "Evar" =>
      match getObj j "pv" with
      | .error e => .error e
      | .ok pvJ =>
        match getStr pvJ "kind" with
        | .error e => .error e
        | .ok "PVloc" =>
          match getIdent pvJ "name" with
          | .error e => .error e
          | .ok x => .ok (.var t (EcVarId.ofName x))
        | .ok "PVglob" =>
          fail s!"global program variable in expression position in \
            {j.compress}: the AST reaches globals through EcStmt.load and \
            EcStmt.store only"
        | .ok k => fail s!"unknown program-variable kind '{k}' in {pvJ.compress}"
    | .ok "Eint" =>
      match t with
      | .fin n _ =>
        match getStr j "value" with
        | .error e => .error e
        | .ok s =>
          match s.toNat? with
          | none => fail s!"integer literal '{s}' is not a decimal natural"
          | some v =>
            if h : v < n then .ok (.lit ⟨v, h⟩)
            else fail s!"integer literal {v} is out of range for fin {n}"
      | .int =>
        match getStr j "value" with
        | .error e => .error e
        | .ok s =>
          match s.toInt? with
          | none => fail s!"integer literal '{s}' is not a decimal integer"
          | some v => .ok (.lit v)
      | _ =>
        fail s!"integer literal at type {repr t}: only a fin code and the int \
          code have one"
    | .ok "Eop" =>
      match getStr j "path" with
      | .error e => .error e
      | .ok p =>
        if T.emptyMapPaths.contains p then
          match t with
          | .map _ _ => .ok (.lit [])
          | _ =>
            fail s!"the empty finite map '{p}' at type {repr t}: only a map code \
              has one"
        else if T.emptyFsetPaths.contains p then
          match t with
          | .fset a => .ok (.lit (EcTy.fsetEmpty (a := a)))
          | _ =>
            fail s!"the empty finite set '{p}' at type {repr t}: only an fset \
              code has one"
        else if T.emptyListPaths.contains p then
          match t with
          | .list a => .ok (.lit (EcTy.listEmpty (a := a)))
          | _ =>
            fail s!"the empty list '{p}' at type {repr t}: only a list code \
              has one"
        else if T.nonePaths.contains p then
          match t with
          | .option a => .ok (.lit (EcTy.noneVal (a := a)))
          | _ =>
            fail s!"'{p}' at type {repr t}: only an option code has an absent \
              value"
        else if T.witnessPaths.contains p then
          .ok (.lit default)
        else
          match List.lookup p T.constPaths with
          | none =>
            fail s!"unknown nullary operator path '{p}': the ingestion's constant \
              table has no entry, so the operator has no EcExpr image"
          | some v =>
            if h : v.ty = t then .ok (.lit (v.transport h))
            else
              fail s!"constant '{p}' has type {repr v.ty}, context expects {repr t}"
    | .ok "Etuple" =>
      match t with
      | .prod a b =>
        match _harr : getArr j "args" with
        | .error e => .error e
        | .ok arr =>
          match arr.toList.attach with
          | [⟨x, _⟩, ⟨y, _⟩] =>
            match decodeExpr T a x with
            | .error e => .error e
            | .ok xe =>
              match decodeExpr T b y with
              | .error e => .error e
              | .ok ye => .ok (.pair xe ye)
          | _ => fail s!"tuple of {arr.size} components at a binary product code"
      | _ => fail s!"tuple at type {repr t}: only a prod code has one"
    | .ok "Eproj" =>
      match _htgt : getObj j "target" with
      | .error e => .error e
      | .ok tgtJ =>
        match decodeTyField T tgtJ "ty" with
        | .error e => .error e
        | .ok pty =>
          match getNat j "index" with
          | .error e => .error e
          | .ok idx =>
            match pty with
            | .prod a b =>
              match decodeExpr T (.prod a b) tgtJ with
              | .error e => .error e
              | .ok pe =>
                match idx with
                | 0 =>
                  if h : a = t then .ok (EcExpr.castTy h (.fst pe))
                  else
                    fail s!"first projection has type {repr a}, context expects \
                      {repr t}"
                | 1 =>
                  if h : b = t then .ok (EcExpr.castTy h (.snd pe))
                  else
                    fail s!"second projection has type {repr b}, context expects \
                      {repr t}"
                | _ => fail s!"projection index {idx} on a binary product"
            | _ =>
              fail s!"projection target has type {repr pty}, which is not a product"
    | .ok "Eapp" =>
      match getObj j "f" with
      | .error e => .error e
      | .ok fJ =>
        match getStr fJ "kind" with
        | .error e => .error e
        | .ok "Eop" =>
          match getStr fJ "path" with
          | .error e => .error e
          | .ok p =>
            match List.lookup p T.opPaths with
            | none =>
              fail s!"unknown operator path '{p}' applied in {j.compress}: the \
                ingestion's operator table has no entry, so the application has \
                no EcExpr image"
            | some op =>
              match _harr : getArr j "args" with
              | .error e => .error e
              | .ok arr =>
                match op, t with
                | .bnot, .bool =>
                  match arr.toList.attach with
                  | [⟨x, _⟩] =>
                    match decodeExpr T .bool x with
                    | .error e => .error e
                    | .ok xe => .ok (.bnot xe)
                  | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 1"
                | .band, .bool =>
                  match arr.toList.attach with
                  | [⟨x, _⟩, ⟨y, _⟩] =>
                    match decodeExpr T .bool x with
                    | .error e => .error e
                    | .ok xe =>
                      match decodeExpr T .bool y with
                      | .error e => .error e
                      | .ok ye => .ok (.band xe ye)
                  | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
                | .bxor, .bool =>
                  match arr.toList.attach with
                  | [⟨x, _⟩, ⟨y, _⟩] =>
                    match decodeExpr T .bool x with
                    | .error e => .error e
                    | .ok xe =>
                      match decodeExpr T .bool y with
                      | .error e => .error e
                      | .ok ye => .ok (.bxor xe ye)
                  | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
                | .bor, .bool =>
                  match arr.toList.attach with
                  | [⟨x, _⟩, ⟨y, _⟩] =>
                    match decodeExpr T .bool x with
                    | .error e => .error e
                    | .ok xe =>
                      match decodeExpr T .bool y with
                      | .error e => .error e
                      | .ok ye => .ok (.bnot (.band (.bnot xe) (.bnot ye)))
                  | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
                | .bimp, .bool =>
                  match arr.toList.attach with
                  | [⟨x, _⟩, ⟨y, _⟩] =>
                    match decodeExpr T .bool x with
                    | .error e => .error e
                    | .ok xe =>
                      match decodeExpr T .bool y with
                      | .error e => .error e
                      | .ok ye => .ok (.bnot (.band xe (.bnot ye)))
                  | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
                | .beq, .bool =>
                  match arr.toList.attach with
                  | [⟨x, _⟩, ⟨y, _⟩] =>
                    match decodeTyField T x "ty" with
                    | .error e => .error e
                    | .ok u =>
                      if !u.hasEq then
                        fail s!"equality at the type {repr u}: a distribution \
                          has no decidable equality, so the comparison has no \
                          EcExpr.beq image"
                      else
                        match decodeExpr T u x with
                        | .error e => .error e
                        | .ok xe =>
                          match decodeExpr T u y with
                          | .error e => .error e
                          | .ok ye => .ok (.beq xe ye)
                  | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
                | .finAdd, .fin n hn =>
                  match arr.toList.attach with
                  | [⟨x, _⟩, ⟨y, _⟩] =>
                    match decodeExpr T (.fin n hn) x with
                    | .error e => .error e
                    | .ok xe =>
                      match decodeExpr T (.fin n hn) y with
                      | .error e => .error e
                      | .ok ye => .ok (.finAdd xe ye)
                  | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
                | .intAdd, .int =>
                  match arr.toList.attach with
                  | [⟨x, _⟩, ⟨y, _⟩] =>
                    match decodeExpr T .int x with
                    | .error e => .error e
                    | .ok xe =>
                      match decodeExpr T .int y with
                      | .error e => .error e
                      | .ok ye => .ok (.intAdd xe ye)
                  | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
                | .intMul, .int =>
                  match arr.toList.attach with
                  | [⟨x, _⟩, ⟨y, _⟩] =>
                    match decodeExpr T .int x with
                    | .error e => .error e
                    | .ok xe =>
                      match decodeExpr T .int y with
                      | .error e => .error e
                      | .ok ye => .ok (.intMul xe ye)
                  | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
                | .intOpp, .int =>
                  match arr.toList.attach with
                  | [⟨x, _⟩] =>
                    match decodeExpr T .int x with
                    | .error e => .error e
                    | .ok xe => .ok (.intOpp xe)
                  | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 1"
                | .intEdivz, .prod .int .int =>
                  match arr.toList.attach with
                  | [⟨x, _⟩, ⟨y, _⟩] =>
                    match decodeExpr T .int x with
                    | .error e => .error e
                    | .ok xe =>
                      match decodeExpr T .int y with
                      | .error e => .error e
                      | .ok ye => .ok (.intEdivz xe ye)
                  | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
                | .intLe, .bool =>
                  match arr.toList.attach with
                  | [⟨x, _⟩, ⟨y, _⟩] =>
                    match decodeExpr T .int x with
                    | .error e => .error e
                    | .ok xe =>
                      match decodeExpr T .int y with
                      | .error e => .error e
                      | .ok ye => .ok (.intLe xe ye)
                  | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
                | .intLt, .bool =>
                  match arr.toList.attach with
                  | [⟨x, _⟩, ⟨y, _⟩] =>
                    match decodeExpr T .int x with
                    | .error e => .error e
                    | .ok xe =>
                      match decodeExpr T .int y with
                      | .error e => .error e
                      | .ok ye => .ok (.bnot (.intLe ye xe))
                  | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
                | .mapSet, .map a b =>
                  match arr.toList.attach with
                  | [⟨mJ, _⟩, ⟨kJ, _⟩, ⟨vJ, _⟩] =>
                    match decodeExpr T (.map a b) mJ with
                    | .error e => .error e
                    | .ok me =>
                      match decodeExpr T a kJ with
                      | .error e => .error e
                      | .ok ke =>
                        match decodeExpr T b vJ with
                        | .error e => .error e
                        | .ok ve => .ok (.mapSet me ke ve)
                  | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 3"
                | .mapMem, .bool =>
                  match arr.toList.attach with
                  | [⟨mJ, _⟩, ⟨kJ, _⟩] =>
                    match decodeTyField T mJ "ty" with
                    | .error e => .error e
                    | .ok (.map a b) =>
                      match decodeExpr T (.map a b) mJ with
                      | .error e => .error e
                      | .ok me =>
                        match decodeExpr T a kJ with
                        | .error e => .error e
                        | .ok ke => .ok (.mapMem me ke)
                    | .ok u =>
                      fail s!"'{p}' is applied to a value of type {repr u}, which \
                        is not a finite map"
                  | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
                | .mapLookup, _ =>
                  fail s!"the finite-map lookup '{p}' in {j.compress}: it returns \
                    an option, which has no EcTy code, so it decodes only as the \
                    argument of oget or of odflt"
                | .mapOget, u =>
                  match arr.toList.attach with
                  | [⟨getJ, _hgetO⟩] =>
                    match getStr getJ "kind" with
                    | .error e => .error e
                    | .ok "Eapp" =>
                      match getObj getJ "f" with
                      | .error e => .error e
                      | .ok gfJ =>
                        match getStr gfJ "path" with
                        | .error e => .error e
                        | .ok gp =>
                          match List.lookup gp T.opPaths with
                          | some .mapLookup =>
                            match _hginO : getArr getJ "args" with
                            | .error e => .error e
                            | .ok garr =>
                              match garr.toList.attach with
                              | [⟨mJ, _⟩, ⟨kJ, _⟩] =>
                                match decodeTyField T mJ "ty" with
                                | .error e => .error e
                                | .ok (.map a b) =>
                                  if h : b = u then
                                    match decodeExpr T (.map a b) mJ with
                                    | .error e => .error e
                                    | .ok me =>
                                      match decodeExpr T a kJ with
                                      | .error e => .error e
                                      | .ok ke =>
                                        .ok (EcExpr.castTy h (.mapGetD me ke (.lit default)))
                                  else
                                    fail s!"'{p}' of a lookup whose value type is \
                                      {repr b}, context expects {repr u}"
                                | .ok u =>
                                  fail s!"'{p}' of a lookup in a value of type \
                                    {repr u}, which is not a finite map"
                              | _ =>
                                fail s!"'{gp}' applied to {garr.size} arguments, \
                                  expected 2"
                          | _ =>
                            fail s!"'{p}' applied to '{gp}' in {j.compress}: the \
                              only argument of oget with an image is a finite-map \
                              lookup"
                    | .ok k =>
                      fail s!"'{p}' applied to a node of kind '{k}' in \
                        {j.compress}: the only argument of oget with an image is \
                        a finite-map lookup"
                  | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 1"
                | .mapOdflt, u =>
                  match arr.toList.attach with
                  | [⟨dJ, _hdD⟩, ⟨getJ, _hgetD⟩] =>
                    match getStr getJ "kind" with
                    | .error e => .error e
                    | .ok "Eapp" =>
                      match getObj getJ "f" with
                      | .error e => .error e
                      | .ok gfJ =>
                        match getStr gfJ "path" with
                        | .error e => .error e
                        | .ok gp =>
                          match List.lookup gp T.opPaths with
                          | some .mapLookup =>
                            match _hginD : getArr getJ "args" with
                            | .error e => .error e
                            | .ok garr =>
                              match garr.toList.attach with
                              | [⟨mJ, _⟩, ⟨kJ, _⟩] =>
                                match decodeTyField T mJ "ty" with
                                | .error e => .error e
                                | .ok (.map a b) =>
                                  if h : b = u then
                                    match decodeExpr T (.map a b) mJ with
                                    | .error e => .error e
                                    | .ok me =>
                                      match decodeExpr T a kJ with
                                      | .error e => .error e
                                      | .ok ke =>
                                        match decodeExpr T b dJ with
                                        | .error e => .error e
                                        | .ok de =>
                                          .ok (EcExpr.castTy h (.mapGetD me ke de))
                                  else
                                    fail s!"'{p}' of a lookup whose value type is \
                                      {repr b}, context expects {repr u}"
                                | .ok u =>
                                  fail s!"'{p}' of a lookup in a value of type \
                                    {repr u}, which is not a finite map"
                              | _ =>
                                fail s!"'{gp}' applied to {garr.size} arguments, \
                                  expected 2"
                          | _ =>
                            fail s!"'{p}' applied to '{gp}' in {j.compress}: the \
                              second argument of odflt has an image only as a \
                              finite-map lookup"
                    | .ok k =>
                      fail s!"'{p}' applied to a node of kind '{k}' in \
                        {j.compress}: the second argument of odflt has an image \
                        only as a finite-map lookup"
                  | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
                | .someE, .option a =>
                  match arr.toList.attach with
                  | [⟨xJ, _⟩] =>
                    match decodeExpr T a xJ with
                    | .error e => .error e
                    | .ok xe => .ok (.someE xe)
                  | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 1"
                | .listCons, .list a =>
                  match arr.toList.attach with
                  | [⟨xJ, _⟩, ⟨lJ, _⟩] =>
                    match decodeExpr T a xJ with
                    | .error e => .error e
                    | .ok xe =>
                      match decodeExpr T (.list a) lJ with
                      | .error e => .error e
                      | .ok le => .ok (.listCons xe le)
                  | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
                | .listRcons, .list a =>
                  match arr.toList.attach with
                  | [⟨lJ, _⟩, ⟨xJ, _⟩] =>
                    match decodeExpr T (.list a) lJ with
                    | .error e => .error e
                    | .ok le =>
                      match decodeExpr T a xJ with
                      | .error e => .error e
                      | .ok xe => .ok (.listRcons le xe)
                  | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
                | .listSize, .int =>
                  match arr.toList.attach with
                  | [⟨lJ, _⟩] =>
                    match decodeTyField T lJ "ty" with
                    | .error e => .error e
                    | .ok (.list a) =>
                      match decodeExpr T (.list a) lJ with
                      | .error e => .error e
                      | .ok le => .ok (.listSize le)
                    | .ok u =>
                      fail s!"'{p}' is applied to a value of type {repr u}, \
                        which is not a list"
                  | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 1"
                | .listMem, .bool =>
                  match arr.toList.attach with
                  | [⟨lJ, _⟩, ⟨xJ, _⟩] =>
                    match decodeTyField T lJ "ty" with
                    | .error e => .error e
                    | .ok (.list a) =>
                      if !a.hasEq then
                        fail s!"'{p}' at the element type {repr a}: membership \
                          compares elements, and that type has no decidable \
                          equality"
                      else
                        match decodeExpr T (.list a) lJ with
                        | .error e => .error e
                        | .ok le =>
                          match decodeExpr T a xJ with
                          | .error e => .error e
                          | .ok xe => .ok (.listMem le xe)
                    | .ok u =>
                      fail s!"'{p}' is applied to a value of type {repr u}, \
                        which is not a list"
                  | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
                | .listNth, u =>
                  match arr.toList.attach with
                  | [⟨dJ, _⟩, ⟨lJ, _⟩, ⟨iJ, _⟩] =>
                    match decodeTyField T lJ "ty" with
                    | .error e => .error e
                    | .ok (.list a) =>
                      if a = u then
                        match decodeExpr T u dJ with
                        | .error e => .error e
                        | .ok de =>
                          match decodeExpr T (.list u) lJ with
                          | .error e => .error e
                          | .ok le =>
                            match decodeExpr T .int iJ with
                            | .error e => .error e
                            | .ok ie => .ok (.listNth de le ie)
                      else
                        fail s!"'{p}' of a list whose element type is \
                          {repr a}, context expects {repr u}"
                    | .ok w =>
                      fail s!"'{p}' is applied to a value of type {repr w}, \
                        which is not a list"
                  | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 3"
                | .fsetSingle, .fset a =>
                  match arr.toList.attach with
                  | [⟨xJ, _⟩] =>
                    match decodeExpr T a xJ with
                    | .error e => .error e
                    | .ok xe => .ok (.fsetSingle xe)
                  | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 1"
                | .fsetUnion, .fset a =>
                  match arr.toList.attach with
                  | [⟨sJ, _⟩, ⟨tJ, _⟩] =>
                    match decodeExpr T (.fset a) sJ with
                    | .error e => .error e
                    | .ok se =>
                      match decodeExpr T (.fset a) tJ with
                      | .error e => .error e
                      | .ok te => .ok (.fsetUnion se te)
                  | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
                | .fsetMem, .bool =>
                  match arr.toList.attach with
                  | [⟨sJ, _⟩, ⟨xJ, _⟩] =>
                    match decodeTyField T sJ "ty" with
                    | .error e => .error e
                    | .ok (.fset a) =>
                      match decodeExpr T (.fset a) sJ with
                      | .error e => .error e
                      | .ok se =>
                        match decodeExpr T a xJ with
                        | .error e => .error e
                        | .ok xe => .ok (.fsetMem se xe)
                    | .ok u =>
                      fail s!"'{p}' is applied to a value of type {repr u}, which \
                        is not a finite set"
                  | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
                | _, _ =>
                  fail s!"operator '{p}' cannot produce a value of type {repr t}"
        | .ok k =>
          fail s!"application of a head of kind '{k}': the AST applies operators \
            only, and has no higher-order application"
    | .ok "Eif" =>
      fail s!"conditional expression in {j.compress}: EcExpr has no conditional, \
        and EcStmt.ite is the only image of a branch"
    | .ok "Elet" =>
      fail s!"let expression in {j.compress}: EcExpr has no binder, and \
        EcStmt.assign is the only image of a local binding"
    | .ok "Ematch" => fail s!"match expression in {j.compress}: EcExpr has no match"
    | .ok "Equant" => fail s!"quantified expression in {j.compress}: EcExpr has no binder"
    | .ok "Unsupported" => fail (unsupportedMsg j)
    | .ok k => fail s!"unsupported expression node kind '{k}' in {j.compress}"
termination_by jsonSize j
decreasing_by
  all_goals first
    | exact getObj_decreases _htgt
    | exact Nat.lt_trans
        (getArr_decreases _hginO (Array.mem_toList_iff.mp ‹_ ∈ Array.toList _›))
        (getArr_decreases _harr (Array.mem_toList_iff.mp _hgetO))
    | exact getArr_decreases _harr (Array.mem_toList_iff.mp _hdD)
    | exact Nat.lt_trans
        (getArr_decreases _hginD (Array.mem_toList_iff.mp ‹_ ∈ Array.toList _›))
        (getArr_decreases _harr (Array.mem_toList_iff.mp _hgetD))
    | exact getArr_decreases _harr (Array.mem_toList_iff.mp ‹_ ∈ Array.toList _›)

/-! ## Statements -/

/-- The image of an EasyCrypt lvalue: a local variable at a type code, or a
module-scoped global. -/
inductive DecodedLv where
  /-- A local variable and its type code. -/
  | loc (x : String) (t : EcTy)
  /-- A module-scoped global. -/
  | glob (g : EcGlobal)

/-- Decode an lvalue node. -/
def decodeLv (T : DecodeTables) (j : Json) : Except String DecodedLv := do
  match ← getStr j "kind" with
  | "LvVar" =>
    let t ← decodeTyField T j "ty"
    let pvJ ← getObj j "pv"
    match ← getStr pvJ "kind" with
    | "PVloc" =>
      let x ← getIdent pvJ "name"
      .ok (.loc x t)
    | "PVglob" =>
      let q ← getStr pvJ "xpath"
      match List.lookup q T.globals with
      | none =>
        fail s!"assignment to the unknown global '{q}': the ingestion's global \
          table has no location for it"
      | some g =>
        if g.ty = t then .ok (.glob g)
        else
          fail s!"global '{q}' is declared at type {repr g.ty} and assigned at \
            {repr t}"
    | k => fail s!"unknown program-variable kind '{k}' in {pvJ.compress}"
  | "LvTuple" =>
    fail s!"tuple lvalue under a random sample in {j.compress}: EcStmt.sampleD \
      writes a single variable, and only an assignment or a call destructures \
      a tuple"
  | k => fail s!"unsupported lvalue kind '{k}' in {j.compress}"

/-- The name a call binds a discarded result to, and the formal parameter name of
a procedure that takes none. EasyCrypt has no variable of this name, so the
binding cannot capture a source variable. -/
def anonymousLocal : String := "_"

/-- The binder name the decoder chooses for the `i`-th formal parameter when the
export carries none — EasyCrypt's `ov_name = None`, which a module type's
`proc f(_ : ty)` produces. An anonymous formal has no name a body occurrence
could reference, and the space makes the name one no EasyCrypt identifier can
be, so the binding cannot capture a source variable. -/
def anonymousParam (i : Nat) : String := "_ " ++ toString i

/-- Decode a tuple lvalue's components: each is a local program variable at
its declared type. A global component is rejected — a write to a global is a
store, and `EcStmt.assignTuple` binds local names only. -/
def decodeLvTupleItems (T : DecodeTables) (j : Json) :
    Except String (List (String × EcTy)) := do
  let itemsA ← getArr j "items"
  itemsA.toList.mapM (fun it => do
    let pvJ ← getObj it "pv"
    let k ← getStr pvJ "kind"
    if k ≠ "PVloc" then
      fail s!"tuple lvalue component of kind '{k}' in {j.compress}: a tuple \
        lvalue binds local variables, and a global component needs a store of \
        its own"
    else
      let nm ← getIdent pvJ "name"
      let ty ← decodeTyField T it "ty"
      .ok (nm, ty))

/-- The global an expression node reads, when the node is a global-variable
read. -/
def globalRead (T : DecodeTables) (j : Json) : Except String (Option EcGlobal) :=
  match j.getObjValAs? String "kind" with
  | .ok "Evar" => do
    let pvJ ← getObj j "pv"
    match ← getStr pvJ "kind" with
    | "PVglob" =>
      let q ← getStr pvJ "xpath"
      match List.lookup q T.globals with
      | none =>
        fail s!"read of the unknown global '{q}': the ingestion's global table \
          has no location for it"
      | some g => .ok (some g)
    | _ => .ok none
  | _ => .ok none

/-! ## Hoisting global reads out of expressions

EasyCrypt reads a module variable anywhere inside an expression; the AST
reaches globals through `EcStmt.load` and `EcStmt.store` only. The image of a
global read in expression position is a hoisting: each distinct global a
statement's expression reads loads into a hoisted local before the statement,
in first-occurrence order, and the read site becomes a read of that local.
Within one statement the source expression reads a snapshot of the globals,
and the loads preserve exactly that snapshot because nothing writes between
them and the statement. A statement that also writes one of the read globals
(`M.c <- M.c + 1`, the counter idiom) reads the pre-write snapshot either way.
A write through a tuple lvalue cannot interact: a tuple lvalue with a global
component is rejected before hoisting is reached. -/

/-- The local a hoisted global read binds: deterministic per global, and the
space makes the name one no EasyCrypt identifier can be, so the binding cannot
capture a source variable. Two statements hoisting one global reuse the name,
and each statement's own load precedes it. -/
def hoistedGlobal (q : String) : String := "_ " ++ q

/-- Append the globals of `more` that `acc` does not already hold, keeping
first-occurrence order. -/
def mergeGlobals (acc more : List EcGlobal) : List EcGlobal :=
  more.foldl (fun acc g =>
    if acc.any (·.name == g.name) then acc else acc ++ [g]) acc

/-- Rewrite the registered global reads of an expression node into local reads
of their hoisted names, collecting each read global once, in first-occurrence
order. A node outside the recognised expression shapes is left unrewritten, so
a global read under one still reports at its own decode; an unregistered
global's read is also left in place, for the same report. -/
def hoistGlobalReads (T : DecodeTables) (j : Json) : List EcGlobal × Json :=
  match getStr j "kind" with
  | .ok "Evar" =>
    match j.getObjVal? "pv" with
    | .ok pvJ =>
      match getStr pvJ "kind", getStr pvJ "xpath" with
      | .ok "PVglob", .ok q =>
        match List.lookup q T.globals with
        | some g =>
          ([g], j.setObjVal! "pv"
            (Json.mkObj [("kind", Json.str "PVloc"),
                         ("name", Json.str (hoistedGlobal q))]))
        | none => ([], j)
      | _, _ => ([], j)
    | .error _ => ([], j)
  | .ok "Eapp" =>
    match _hf : j.getObjVal? "f", _ha : getArr j "args" with
    | .ok fJ, .ok arr =>
      let fr := hoistGlobalReads T fJ
      let rs := arr.toList.attach.map (fun ⟨x, _⟩ => hoistGlobalReads T x)
      (rs.foldl (fun acc r => mergeGlobals acc r.1) fr.1,
        (j.setObjVal! "f" fr.2).setObjVal! "args"
          (Json.arr (rs.map (·.2)).toArray))
    | _, _ => ([], j)
  | .ok "Etuple" =>
    match _ht : getArr j "args" with
    | .ok arr =>
      let rs := arr.toList.attach.map (fun ⟨x, _⟩ => hoistGlobalReads T x)
      (rs.foldl (fun acc r => mergeGlobals acc r.1) [],
        j.setObjVal! "args" (Json.arr (rs.map (·.2)).toArray))
    | .error _ => ([], j)
  | .ok "Eproj" =>
    match _htg : j.getObjVal? "target" with
    | .ok tJ =>
      let r := hoistGlobalReads T tJ
      (r.1, j.setObjVal! "target" r.2)
    | .error _ => ([], j)
  | _ => ([], j)
termination_by jsonSize j
decreasing_by
  all_goals first
    | exact getObjVal?_decreases _hf
    | exact getObjVal?_decreases _htg
    | exact getArr_decreases _ha (Array.mem_toList_iff.mp ‹_ ∈ Array.toList _›)
    | exact getArr_decreases _ht (Array.mem_toList_iff.mp ‹_ ∈ Array.toList _›)

/-- Hoist the global reads of every element of a call's argument array,
deduplicating across the whole statement. -/
def hoistArgs (T : DecodeTables) (arr : Array Json) :
    List EcGlobal × Array Json :=
  let rs := arr.toList.map (hoistGlobalReads T)
  (rs.foldl (fun acc r => mergeGlobals acc r.1) [], (rs.map (·.2)).toArray)

/-! ## Distributions

A distribution node's own type is `'a distr` at the carrier the sample writes, and
`checkDistrTy` is what pins that carrier. `decodeDistr` then produces an
`EcDistr t`, whose constructors are the images of a declared-uniform nullary
operator, `dunit`, `dmap`, `dcond`, `dlet`, ``(`*`)``, `dscale` and `drestrict`;
EasyCrypt's `d \ X` is `dcond` at the negated predicate, which is that operator's
own definition. A distribution operator outside `distrOpPaths`, or a node of any
other shape, is a decode error naming the path or the kind. -/

/-- Check that a distribution node's own type is the distribution type over the
carrier `t`. -/
def checkDistrTy (T : DecodeTables) (t : EcTy) (j : Json) : Except String Unit := do
  let tyJ ← getObj j "ty"
  let dk ← getStr tyJ "kind"
  if dk ≠ "Tconstr" then
    fail s!"distribution type of kind '{dk}' in {tyJ.compress}"
  else
    let dp ← getStr tyJ "path"
    if !T.distrTyPaths.contains dp then
      fail s!"'{dp}' is not one of the ingestion's distribution type \
        constructors"
    else
      let args ← getArr tyJ "args"
      match args.toList with
      | [carrier] =>
        let u ← decodeTy T carrier
        if u = t then .ok ()
        else
          fail s!"distribution is on {repr u} and the sampled variable has \
            type {repr t}"
      | _ =>
        fail s!"distribution type '{dp}' applied to {args.size} arguments, \
          expected 1"

/-- The binder and the body node of a one-binder lambda `j`, with the proof that
the body is smaller than the lambda. The proof is what lets a recursive decoder
descend under the binder: `decodeDistr`'s `dlet` arm decodes the body as a
distribution, which is a recursive position `decodeLambda1` cannot serve. -/
structure Lambda1 (j : Json) where
  /-- The binder's type code. -/
  ty : EcTy
  /-- The binder's identity: its source name and its uniqueness stamp. -/
  binder : EcVarId
  /-- The body node. -/
  body : Json
  /-- The body is smaller than the lambda on the `jsonSize` measure. -/
  smaller : jsonSize body < jsonSize j

/-- Decode the header of a one-binder lambda: the binder's type code, the
binder's identity, and the body node. This is how a distribution operator whose
argument is a function reaches the AST — the binder is bound in the local
valuation the body reads. -/
def decodeLambdaHeader (T : DecodeTables) (j : Json) : Except String (Lambda1 j) := do
  let kind ← getStr j "kind"
  if kind ≠ "Equant" then
    fail s!"function argument of kind '{kind}' in {j.compress}: a distribution \
      operator's function argument has an image only as a one-binder lambda"
  else
    let q ← getStr j "quant"
    if q ≠ "ELambda" then
      fail s!"quantifier '{q}' in {j.compress}: only a lambda is a function"
    else
      let bs ← getArr j "binders"
      match bs.toList with
      | [b] =>
        let a ← decodeTyField T b "ty"
        let x ← getStampedIdent b
        match hbody : getObj j "body" with
        | .error e => .error e
        | .ok bodyJ =>
          .ok { ty := a, binder := x, body := bodyJ,
                smaller := getObj_decreases hbody }
      | _ =>
        fail s!"lambda of {bs.size} binders in {j.compress}: a distribution \
          operator's function argument has an image only at one binder"

/-- Decode a one-binder lambda whose body is an expression at the type code
`res`, as the binder's type code, the binder's identity, and the body. -/
def decodeLambda1 (T : DecodeTables) (res : EcTy) (j : Json) :
    Except String (EcTy × EcVarId × EcExpr res) := do
  let l ← decodeLambdaHeader T j
  let e ← decodeExpr T res l.body
  .ok (l.ty, l.binder, e)

/-- Decode an EasyCrypt distribution expression at the carrier code `t`. -/
def decodeDistr (T : DecodeTables) (t : EcTy) (j : Json) :
    Except String (EcDistr t) :=
  match checkDistrTy T t j with
  | .error e => .error e
  | .ok () =>
    match getStr j "kind" with
    | .error e => .error e
    | .ok "Evar" =>
      -- A distribution read out of a formal parameter or a local: the node is
      -- an expression at the `distr` code, and the distribution is its value.
      match decodeExpr T (.distr t) j with
      | .error e => .error e
      | .ok e => .ok (.ofExpr e)
    | .ok "Eop" =>
      match getStr j "path" with
      | .error e => .error e
      | .ok p =>
        if !T.distrPaths.contains p then
          fail s!"distribution '{p}' is not one of the ingestion's uniform \
            distributions, so it has no EcDistr.uniform image"
        else if h : t.isFin = true then .ok (.uniform t h)
        else
          fail s!"the uniform distribution at the type {repr t}: \
            EcDistr.uniform is uniform on its carrier, and that type is not \
            finite"
    | .ok "Eapp" =>
      match getObj j "f" with
      | .error e => .error e
      | .ok hdJ =>
        match getStr hdJ "kind" with
        | .error e => .error e
        | .ok "Eop" =>
          match getStr hdJ "path" with
          | .error e => .error e
          | .ok p =>
            match List.lookup p T.distrOpPaths with
            | none =>
              fail s!"unknown distribution operator path '{p}' applied in \
                {j.compress}: the ingestion's distribution-operator table has no \
                entry, so the distribution has no EcDistr image"
            | some op =>
              match _harr : getArr j "args" with
              | .error e => .error e
              | .ok arr =>
                match op with
                | .dunit =>
                  match arr.toList.attach with
                  | [⟨x, _⟩] =>
                    match decodeExpr T t x with
                    | .error e => .error e
                    | .ok xe => .ok (.point xe)
                  | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 1"
                | .dmap =>
                  match arr.toList.attach with
                  | [⟨dJ, _⟩, ⟨funJ, _⟩] =>
                    match decodeLambda1 T t funJ with
                    | .error e => .error e
                    | .ok (a, x, e) =>
                      match decodeDistr T a dJ with
                      | .error e => .error e
                      | .ok d => .ok (.map d x e)
                  | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
                | .dcond =>
                  match arr.toList.attach with
                  | [⟨dJ, _⟩, ⟨funJ, _⟩] =>
                    match decodeLambda1 T .bool funJ with
                    | .error e => .error e
                    | .ok (a, x, e) =>
                      if a = t then
                        match decodeDistr T t dJ with
                        | .error e => .error e
                        | .ok d => .ok (.cond d x e)
                      else
                        fail s!"'{p}' has a predicate on {repr a} and a \
                          distribution on {repr t}"
                  | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
                | .dexcepted =>
                  match arr.toList.attach with
                  | [⟨dJ, _⟩, ⟨funJ, _⟩] =>
                    match decodeLambda1 T .bool funJ with
                    | .error e => .error e
                    | .ok (a, x, e) =>
                      if a = t then
                        match decodeDistr T t dJ with
                        | .error e => .error e
                        | .ok d => .ok (.cond d x (.bnot e))
                      else
                        fail s!"'{p}' has a predicate on {repr a} and a \
                          distribution on {repr t}"
                  | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
                | .dlet =>
                  match arr.toList.attach with
                  | [⟨dJ, _hdJ⟩, ⟨funJ, _hfunJ⟩] =>
                    match decodeLambdaHeader T funJ with
                    | .error e => .error e
                    | .ok l =>
                      match decodeDistr T t l.body with
                      | .error e => .error e
                      | .ok body =>
                        match decodeDistr T l.ty dJ with
                        | .error e => .error e
                        | .ok d => .ok (.letD d l.binder body)
                  | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
                | .dprod =>
                  match t with
                  | .prod u v =>
                    match arr.toList.attach with
                    | [⟨aJ, _⟩, ⟨bJ, _⟩] =>
                      match decodeDistr T u aJ with
                      | .error e => .error e
                      | .ok d₁ =>
                        match decodeDistr T v bJ with
                        | .error e => .error e
                        | .ok d₂ => .ok (.prod d₁ d₂)
                    | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
                  | _ =>
                    fail s!"'{p}' at the carrier {repr t}: the independent \
                      product is a distribution over a pair"
                | .dscale =>
                  match arr.toList.attach with
                  | [⟨dJ, _⟩] =>
                    match decodeDistr T t dJ with
                    | .error e => .error e
                    | .ok d => .ok (.scale d)
                  | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 1"
                | .drestrict =>
                  match arr.toList.attach with
                  | [⟨dJ, _⟩, ⟨funJ, _⟩] =>
                    match decodeLambda1 T .bool funJ with
                    | .error e => .error e
                    | .ok (a, x, e) =>
                      if a = t then
                        match decodeDistr T t dJ with
                        | .error e => .error e
                        | .ok d => .ok (.restrict d x e)
                      else
                        fail s!"'{p}' has a predicate on {repr a} and a \
                          distribution on {repr t}"
                  | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
        | .ok k =>
          fail s!"application of a head of kind '{k}' in a distribution position \
            in {j.compress}: the AST applies distribution operators only"
    | .ok "Unsupported" => fail (unsupportedMsg j)
    | .ok k =>
      fail s!"distribution node of kind '{k}' in {j.compress}: a distribution \
        has an image only as a declared uniform operator or as an application of \
        a distribution operator of the accepted fragment"
termination_by jsonSize j
decreasing_by
  all_goals first
    | exact getArr_decreases _harr (Array.mem_toList_iff.mp ‹_ ∈ Array.toList _›)
    | exact getArr_decreases _harr (Array.mem_toList_iff.mp _hdJ)
    | exact Nat.lt_trans l.smaller
        (getArr_decreases _harr (Array.mem_toList_iff.mp _hfunJ))

/-- Decode a non-empty argument list as one typed expression: a single
argument at its own type, and two or more as the right-nested pair
`(a₁, (a₂, …))`, which is the nesting the callee's signature carries
(`decodeSigDef`) and the nesting `bindParams` destructures at call entry. -/
def decodeArgTuple (T : DecodeTables) (a : Json) (rest : List Json) :
    Except String ((t : EcTy) × EcExpr t) :=
  match rest with
  | [] => do
    let u ← decodeTyField T a "ty"
    let ae ← decodeExpr T u a
    .ok ⟨u, ae⟩
  | b :: rest' => do
    let u ← decodeTyField T a "ty"
    let ae ← decodeExpr T u a
    let ⟨v, be⟩ ← decodeArgTuple T b rest'
    .ok ⟨.prod u v, .pair ae be⟩

/-- Decode a call site's arguments at the signature they determine, together
with that signature: the export passes one expression per formal, and the
formals' types pair up as the callee's right-nested argument type. -/
def decodeCallArgs (T : DecodeTables) (res : EcTy) (arr : Array Json) :
    Except String ((s : EcSig) × EcExpr s.arg) := do
  match arr.toList with
  | [] => .ok ⟨{ arg := .unit, res := res }, .lit ()⟩
  | a :: rest =>
    let ⟨t, e⟩ ← decodeArgTuple T a rest
    .ok ⟨{ arg := t, res := res }, e⟩

/-! ## The bounded-loop idiom

EasyCrypt has no `for`, and `EcStmt.forN n body` carries an iteration count and
no counter. A `Swhile` node therefore decodes only at the shape whose iteration
count the block it sits in determines:

* the guard is `i < n`, at a program variable `i` and an integer literal `n`;
* the statement immediately before the loop is `i <- c`, at an integer literal
  `c`;
* the last statement of the body is `i <- i + 1`;
* no other statement of the body writes `i`, and the write set of every other
  statement of the body is determined by that statement — an argument-free
  `call` runs a procedure body in the caller's valuation, so a body containing
  one is rejected.

The image is `i <- c` followed by `EcStmt.forN (n - c).toNat body`, with the
increment left in the body: the loop then runs the body once per value of `i` in
`[c, n)` and leaves `i` at `max c n`, which is what the source does. A `Swhile`
that differs from this shape in any respect is a decode error naming the
respect, and `decodeItem` is what produces the marker `resolveLoops` matches
against its initialisation. -/

/-- The image of an EasyCrypt instruction inside a block: a statement, or a
`Swhile` of the recognised shape, which is a statement only once the block
supplies the counter's initial value. -/
inductive DecodedItem where
  /-- An instruction whose image is a statement on its own. -/
  | stmt (s : EcStmt)
  /-- An instruction whose image is a statement together with the loads its
  expression's global reads hoist: `pre` binds each read global into its
  hoisted local, in first-occurrence order, and `s` reads the locals. -/
  | stmts (pre : List EcStmt) (s : EcStmt)
  /-- A while loop of the recognised shape: the counter, the bound the guard
  compares it with, and the body, whose last statement increments the counter. -/
  | loop (counter : String) (bound : Int) (body : List EcStmt)

/-- The decoded item a statement and its hoisted loads make: the statement on
its own when nothing was hoisted. -/
def withHoisted (gs : List EcGlobal) (s : EcStmt) : DecodedItem :=
  match gs with
  | [] => .stmt s
  | _ => .stmts (gs.map (fun g => .load g (hoistedGlobal g.name))) s

/-- Resolve the loops of a decoded block against their initialisations. A loop
whose immediately preceding statement is not an integer-literal assignment to
its counter is a decode error: the iteration count is the distance from that
value to the guard's bound, and no other statement supplies it. -/
def resolveLoops : List DecodedItem → Except String (List EcStmt)
  | [] => .ok []
  | .stmt s :: .loop x n body :: rest =>
    match s.initOf with
    | some (y, c) =>
      if y = x then
        match resolveLoops rest with
        | .error e => .error e
        | .ok rest' => .ok (s :: .forN (n - c).toNat body :: rest')
      else
        fail s!"the while loop on the counter '{x}' follows an assignment to \
          '{y}': the statement before the loop has to give the counter its \
          initial value, which is what fixes the iteration count"
    | none =>
      fail s!"the while loop on the counter '{x}' does not follow an \
        integer-literal assignment to '{x}': the iteration count is the distance \
        from that value to the guard's bound, and nothing else supplies it"
  | .stmts pre s :: .loop x n body :: rest =>
    match s.initOf with
    | some (y, c) =>
      if y = x then
        match resolveLoops rest with
        | .error e => .error e
        | .ok rest' => .ok (pre ++ s :: .forN (n - c).toNat body :: rest')
      else
        fail s!"the while loop on the counter '{x}' follows an assignment to \
          '{y}': the statement before the loop has to give the counter its \
          initial value, which is what fixes the iteration count"
    | none =>
      fail s!"the while loop on the counter '{x}' does not follow an \
        integer-literal assignment to '{x}': the iteration count is the distance \
        from that value to the guard's bound, and nothing else supplies it"
  | .stmt s :: rest =>
    match resolveLoops rest with
    | .error e => .error e
    | .ok rest' => .ok (s :: rest')
  | .stmts pre s :: rest =>
    match resolveLoops rest with
    | .error e => .error e
    | .ok rest' => .ok (pre ++ s :: rest')
  | .loop x _ _ :: _ =>
    fail s!"the while loop on the counter '{x}' opens its block: the statement \
      before the loop has to give the counter its initial value, which is what \
      fixes the iteration count"

/-- Decode an EasyCrypt instruction node, as a statement or as a while loop
awaiting its initialisation. -/
def decodeItem (T : DecodeTables) (j : Json) : Except String DecodedItem :=
  match getStr j "kind" with
  | .error e => .error e
  | .ok "Sasgn" =>
    match getObj j "lv" with
    | .error e => .error e
    | .ok lvJ =>
      match getStr lvJ "kind" with
      | .error e => .error e
      | .ok "LvTuple" =>
        match decodeLvTupleItems T lvJ with
        | .error e => .error e
        | .ok [] =>
          fail s!"tuple lvalue of no components in {lvJ.compress}: the \
            exporter writes no such node"
        | .ok [_] =>
          fail s!"tuple lvalue of one component in {lvJ.compress}: the \
            exporter writes no such node"
        | .ok ((x, tx) :: rest) =>
          let t := nestTuple tx (rest.map (·.2))
          match getObj j "rhs" with
          | .error e => .error e
          | .ok rhsJ =>
            let (hgs, rhsJ') := hoistGlobalReads T rhsJ
            match decodeExpr T t rhsJ' with
            | .error e => .error e
            | .ok e => .ok (withHoisted hgs (.assignTuple t (x :: rest.map (·.1)) e))
      | .ok _ =>
        match decodeLv T lvJ with
        | .error e => .error e
        | .ok lv =>
          match getObj j "rhs" with
          | .error e => .error e
          | .ok rhsJ =>
            match lv with
            | .loc x t =>
              match globalRead T rhsJ with
              | .error e => .error e
              | .ok (some g) =>
                if g.ty = t then .ok (.stmt (.load g x))
                else
                  fail s!"global '{g.name}' is declared at type {repr g.ty} and \
                    read into a variable of type {repr t}"
              | .ok none =>
                let (hgs, rhsJ') := hoistGlobalReads T rhsJ
                match decodeExpr T t rhsJ' with
                | .error e => .error e
                | .ok e => .ok (withHoisted hgs (.assign t x e))
            | .glob g =>
              let (hgs, rhsJ') := hoistGlobalReads T rhsJ
              match decodeExpr T g.ty rhsJ' with
              | .error e => .error e
              | .ok e => .ok (withHoisted hgs (.store g e))
  | .ok "Srnd" =>
    match getObj j "lv" with
    | .error e => .error e
    | .ok lvJ =>
      match decodeLv T lvJ with
      | .error e => .error e
      | .ok (.glob g) =>
        fail s!"sampling into the global '{g.name}': EcStmt.sample writes a \
          local variable"
      | .ok (.loc x t) =>
        match getObj j "distr" with
        | .error e => .error e
        | .ok dJ =>
          match decodeDistr T t dJ with
          | .error e => .error e
          | .ok d =>
            match d.uniformFin with
            | some h => .ok (.stmt (.sample t x h.down))
            | none => .ok (.stmt (.sampleD t x d))
  | .ok "Sif" =>
    match getObj j "cond" with
    | .error e => .error e
    | .ok condJ =>
      let (hconds, condJ') := hoistGlobalReads T condJ
      match decodeExpr T .bool condJ' with
      | .error e => .error e
      | .ok c =>
        match _hthn : getArr j "then" with
        | .error e => .error e
        | .ok thnA =>
          match thnA.toList.attach.mapM (fun ⟨s, _⟩ => decodeItem T s) with
          | .error e => .error e
          | .ok thnItems =>
            match resolveLoops thnItems with
            | .error e => .error e
            | .ok thn =>
              match _hels : getArr j "else" with
              | .error e => .error e
              | .ok elsA =>
                match elsA.toList.attach.mapM (fun ⟨s, _⟩ => decodeItem T s) with
                | .error e => .error e
                | .ok elsItems =>
                  match resolveLoops elsItems with
                  | .error e => .error e
                  | .ok els => .ok (withHoisted hconds (.ite c thn els))
  | .ok "Swhile" =>
    match getObj j "cond" with
    | .error e => .error e
    | .ok condJ =>
      match decodeExpr T .bool condJ with
      | .error e => .error e
      | .ok c =>
        match c.ltGuard with
        | none =>
          fail s!"while guard in {j.compress}: the only while loop with an image \
            is the bounded one, whose guard is `i < n` at a program variable `i` \
            and an integer literal `n`"
        | some (x, n) =>
          if x.stamp.isSome then
            fail s!"the while guard compares the bound identifier '{x.name}': a \
              loop counter is a program variable, which carries no uniqueness \
              stamp"
          else
            match _hbody : getArr j "body" with
            | .error e => .error e
            | .ok bodyA =>
              match bodyA.toList.attach.mapM (fun ⟨s, _⟩ => decodeItem T s) with
              | .error e => .error e
              | .ok items =>
                match resolveLoops items with
                | .error e => .error e
                | .ok body =>
                  match body.getLast? with
                  | none =>
                    fail s!"the while loop on the counter '{x.name}' has an empty \
                      body, so nothing increments the counter"
                  | some last =>
                    if last.incrOf ≠ some x.name then
                      fail s!"the last statement of the while loop on the counter \
                        '{x.name}' is not `{x.name} <- {x.name} + 1`, so the \
                        iteration count is not the distance to the guard's bound"
                    else if !EcStmt.avoids x.name body.dropLast then
                      fail s!"the body of the while loop on the counter \
                        '{x.name}' writes '{x.name}' somewhere other than its \
                        last statement, or contains an argument-free call, whose \
                        writes the call site does not determine"
                    else .ok (.loop x.name n body)
  | .ok "Scall" =>
    match getStr j "proc" with
    | .error e => .error e
    | .ok q =>
      match getArr j "args" with
      | .error e => .error e
      | .ok argsA =>
        let (hargs, argsA') := hoistArgs T argsA
        match getObj j "lv" with
        | .error e => .error e
        | .ok Json.null =>
          if argsA'.isEmpty && T.modPath ≠ "" && q.startsWith T.modPath then
            .ok (.stmt (.call (lastComponent q)))
          else
            match List.lookup q T.procSigs with
            | some s =>
              match decodeCallArgs T s.res argsA' with
              | .error e => .error e
              | .ok ⟨s', arg⟩ =>
                if s'.arg ≠ s.arg then
                  fail s!"call to '{q}' passes an argument of type \
                    {repr s'.arg}, and the resolved signature takes \
                    {repr s.arg}"
                else
                  .ok (withHoisted hargs (.callProc q s' arg anonymousLocal))
            | none =>
              fail s!"call to '{q}' discards its result in {j.compress}: the \
                schema carries no result type at the call site and the \
                cross-path is not in the ingestion's signature table, so the \
                signature cannot be reconstructed — a functor parameter's \
                procedures register from its module type, and an envelope \
                module's from its decoded structure"
        | .ok lvJ =>
          match getStr lvJ "kind" with
          | .error e => .error e
          | .ok "LvTuple" =>
            match decodeLvTupleItems T lvJ with
            | .error e => .error e
            | .ok [] =>
              fail s!"tuple lvalue of no components in {lvJ.compress}: the \
                exporter writes no such node"
            | .ok [_] =>
              fail s!"tuple lvalue of one component in {lvJ.compress}: the \
                exporter writes no such node"
            | .ok ((x, tx) :: rest) =>
              let t := nestTuple tx (rest.map (·.2))
              match decodeCallArgs T t argsA' with
              | .error e => .error e
              | .ok ⟨s, arg⟩ =>
                .ok (withHoisted hargs (.callProcTuple q s arg (x :: rest.map (·.1))))
          | .ok _ =>
            match decodeLv T lvJ with
            | .error e => .error e
            | .ok (.glob g) =>
              fail s!"call result assigned to the global '{g.name}': \
                EcStmt.callProc writes a local variable"
            | .ok (.loc x t) =>
              match decodeCallArgs T t argsA' with
              | .error e => .error e
              | .ok ⟨s, arg⟩ => .ok (withHoisted hargs (.callProc q s arg x))
  | .ok "Smatch" =>
    fail s!"match instruction in {j.compress}: the AST has no match statement"
  | .ok "Sraise" =>
    fail s!"raise instruction in {j.compress}: the AST has no exceptions"
  | .ok "Sabstract" =>
    fail s!"abstract instruction in {j.compress}: an abstract statement has no \
      image, and an adversary call decodes from Scall"
  | .ok "Unsupported" => fail (unsupportedMsg j)
  | .ok k => fail s!"unsupported instruction kind '{k}' in {j.compress}"
termination_by jsonSize j
decreasing_by
  all_goals first
    | exact getArr_decreases _hthn (Array.mem_toList_iff.mp ‹_ ∈ Array.toList _›)
    | exact getArr_decreases _hels (Array.mem_toList_iff.mp ‹_ ∈ Array.toList _›)
    | exact getArr_decreases _hbody (Array.mem_toList_iff.mp ‹_ ∈ Array.toList _›)

/-- Decode a statement block. -/
def decodeStmts (T : DecodeTables) (js : List Json) : Except String (List EcStmt) := do
  let items ← js.mapM (decodeItem T)
  resolveLoops items

/-- Decode a single EasyCrypt instruction node. A while loop is a statement only
inside a block, where the statement before it gives its counter an initial
value. -/
def decodeStmt (T : DecodeTables) (j : Json) : Except String EcStmt := do
  match ← decodeItem T j with
  | .stmt s => .ok s
  | .stmts _ _ =>
    fail s!"statement with hoisted global loads stands alone: the loads bind \
      the globals the statement's expression reads, and only a block carries \
      them"
  | .loop x _ _ =>
    fail s!"the while loop on the counter '{x}' stands on its own: the statement \
      before the loop has to give the counter its initial value, which is what \
      fixes the iteration count"

/-! ## Procedures -/

/-- A procedure together with its signature. -/
structure SigProc where
  /-- The signature. -/
  sig : EcSig
  /-- The procedure at that signature. -/
  proc : EcProcAt sig

/-- The signature and body an undeclared procedure name is sent to. A name
outside a module's interface is undeclared, and the module's meaning does not
depend on either. -/
def undeclaredProc : SigProc :=
  { sig := { arg := .unit, res := .unit }
    proc := { params := [anonymousLocal], body := [], ret := .lit () } }

/-- The entry an association list of decoded procedures holds at `p`. -/
def sigProcOf (L : List (String × SigProc)) (p : String) : SigProc :=
  (List.lookup p L).getD undeclaredProc

/-- The interface an association list of signatures declares. -/
def interfaceOfSigs (L : List (String × EcSig)) : EcInterface where
  names := L.map (·.1)
  sig := fun p => (List.lookup p L).getD { arg := .unit, res := .unit }

/-- A decoded procedure: its name, the locals it declares, and the procedure
itself. -/
structure DecodedProc where
  /-- The procedure name as the exporter gives it. -/
  name : String
  /-- The declared local variables. -/
  locals : List String
  /-- The procedure and its signature. -/
  sp : SigProc

/-- Decode a procedure signature and its formal-parameter binder names in
declaration order. `args` is the authoritative formal list, one `{name, ty}`
entry per formal, with `name` null for an anonymous formal, which binds under a
positional name (`anonymousParam`); a procedure of no formals binds the
anonymous local to its unit argument. `argty` is EasyCrypt's `fs_arg`, the same
domain as one type — `unit` for no formals, the formal's own type for one, and
the tuple of the formals' types in declaration order otherwise — and is checked
against the formals' types: a disagreement between the two is a decode
error. -/
def decodeSigDef (T : DecodeTables) (j : Json) : Except String (EcSig × List String) := do
  let arg ← decodeTyField T j "argty"
  let res ← decodeTyField T j "ret"
  let argsA ← getArr j "args"
  let formals ← argsA.toList.mapM (fun a => do
    let ty ← decodeTyField T a "ty"
    match a.getObjVal? "name" with
    | .ok Json.null => .ok ((none : Option String), ty)
    | .ok _ => do
      let nm ← getIdent a "name"
      .ok (some nm, ty)
    | .error _ => fail s!"formal parameter without a name field in {a.compress}")
  let expected := match formals.map (·.2) with
    | [] => EcTy.unit
    | t :: rest => nestTuple t rest
  if arg ≠ expected then
    fail s!"the signature's argty {repr arg} is not the formals' types \
      {repr expected}: args is the binder list and argty its tupled domain, \
      and the two disagree"
  else
    match formals with
    | [] => .ok ({ arg := arg, res := res }, [anonymousLocal])
    | _ =>
      .ok ({ arg := arg, res := res },
        formals.zipIdx.map (fun (f, i) => f.1.getD (anonymousParam i)))

/-- Decode a procedure signature as a module type declares it. -/
def decodeSigDecl (T : DecodeTables) (j : Json) : Except String (String × EcSig) := do
  let name ← getStr j "name"
  let sigJ ← getObj j "sig"
  let (s, _) ← decodeSigDef T sigJ
  .ok (name, s)

/-- Decode a return expression, which is `null` for a procedure that returns
nothing. -/
def decodeRet (T : DecodeTables) (t : EcTy) (j : Json) : Except String (EcExpr t) :=
  match j with
  | Json.null =>
    match t with
    | .unit => .ok (.lit ())
    | _ => fail s!"procedure returns nothing but its result type is {repr t}"
  | _ => decodeExpr T t j

/-- The module path and the procedure name a cross-path `M./p` names, split at
its one `./`. A string with no `./`, or with more than one, is not a
cross-path. -/
def splitXPath (q : String) : Option (String × String) :=
  match q.splitOn "./" with
  | [m, p] => some (m, p)
  | _ => none

/-- The local an alias body binds its forwarded call's result to. The space makes
the name one no EasyCrypt identifier can be, so the binding captures neither a
formal nor a declared local. -/
def aliasResultLocal : String := "_ alias"

/-- The argument an alias body forwards: the formals read back in declaration
order and tupled at the signature's domain, which is the right-nested product
`bindParams` destructures the incoming argument by, so the forwarded value is the
one the alias was called with. A formal list that does not match the domain's
nesting has no such expression. -/
def formalsTuple : List String → (t : EcTy) → Option (EcExpr t)
  | [], _ => none
  | [x], t => some (.var t x)
  | x :: y :: rest, .prod a b =>
    (formalsTuple (y :: rest) b).map (fun e => EcExpr.pair (.var a x) e)
  | _ :: _ :: _, _ => none

/-- Decode an `FBalias` procedure body — EasyCrypt's `proc f = M.g`, a procedure
that names another procedure instead of giving statements — as a body that
forwards to the named procedure: the formals are read back at the signature's
domain, one `EcStmt.callProc` calls the target's cross-path at the alias's own
signature, and that call's result is the return expression. The alias is decoded
as a reference to the target and is never followed, so two aliases naming each
other decode without the decoder recurring.

The target's signature comes from `procSigs`, the table a result-discarding
cross-path call already resolves against, and the scopes a target sits in
resolve as follows.

* A procedure of another module of the envelope resolves: an envelope module
  registers its procedures at `xqualify path p`, which is the form the target
  is written in.
* A procedure of a functor parameter resolves: a parameter registers its module
  type's procedures at `xqualify paramName p`, again the form of the target.
* A procedure of the module being decoded is rejected. An earlier decode of the
  same item can have registered that module's own procedures, so the lookup can
  succeed and yield a procedure whose body is a call to itself.
* A procedure of an applied functor, whose module part is written `F(X)`, is
  rejected: an application has no module path, nothing registers under one, and
  the procedure it names is the functor's body at that argument.

A module nested inside another is rejected before a procedure is reached
(`decodeStructureBody`), so an alias to a procedure of an enclosing module
cannot arise in a body that decodes.

A target whose resolved signature is not the alias's declared signature is
rejected rather than called at either signature: the two name different
procedures, and the imported statement would be about the other one. -/
def decodeAliasBody (T : DecodeTables) (name : String) (s : EcSig)
    (params : List String) (defJ : Json) : Except String (EcProcAt s) := do
  let target ← getStr defJ "target"
  match splitXPath target with
  | none =>
    fail s!"procedure '{name}' is an alias of '{target}', which is not a \
      cross-path: an alias names its target as a module path and a procedure \
      name with a '/' between them"
  | some (mpath, _) =>
    if mpath.contains '(' then
      fail s!"procedure '{name}' is an alias of '{target}', a procedure of the \
        applied functor '{mpath}': an application has no module path of its \
        own, so no signature registers under one, and the procedure it names \
        is the functor's body at that argument"
    else if mpath = T.modPath then
      fail s!"procedure '{name}' is an alias of '{target}', a procedure of the \
        module the alias sits in: the body would be a call to a procedure of \
        that same module, and a pair of such aliases is a procedure defined as \
        a call to itself"
    else
      match List.lookup target T.procSigs with
      | none =>
        fail s!"procedure '{name}' is an alias of '{target}', whose signature \
          is not in the ingestion's signature table: a functor parameter's \
          procedures register from its module type, and an envelope module's \
          from its decoded structure"
      | some s' =>
        if s' ≠ s then
          fail s!"procedure '{name}' is an alias of '{target}', which resolves \
            at the signature {repr s'}, and the alias is declared at \
            {repr s}: the two name different procedures"
        else
          match formalsTuple params s.arg with
          | none =>
            fail s!"procedure '{name}' binds the formals {params} at the \
              domain {repr s.arg}, which an alias body cannot read back as the \
              argument it forwards"
          | some arg =>
            .ok { params := params
                  body := [.callProc target s arg aliasResultLocal]
                  ret := .var s.res aliasResultLocal }

/-- Decode a procedure: an `FBdef` body as its statements and return expression,
an `FBalias` body as a forwarding call to the procedure it names
(`decodeAliasBody`). -/
def decodeProc (T : DecodeTables) (j : Json) : Except String DecodedProc := do
  let name ← getStr j "name"
  let sigJ ← getObj j "sig"
  let (s, params) ← decodeSigDef T sigJ
  let defJ ← getObj j "def"
  let bk ← getStr defJ "kind"
  match bk with
  | "FBdef" =>
    let localsA ← getArr defJ "locals"
    let locals ← localsA.toList.mapM (fun v => getIdent v "name")
    let bodyA ← getArr defJ "body"
    let body ← decodeStmts T bodyA.toList
    let retJ ← getObj defJ "ret"
    let ret ← decodeRet T s.res retJ
    .ok { name := name, locals := locals
          sp := { sig := s, proc := { params := params, body := body, ret := ret } } }
  | "FBalias" =>
    let pr ← decodeAliasBody T name s params defJ
    .ok { name := name, locals := [], sp := { sig := s, proc := pr } }
  | _ =>
    fail s!"procedure '{name}' has body kind '{bk}': an FBdef body gives \
      statements and an FBalias body names another procedure, and no other \
      body has an EcProcAt image"

/-! ## Modules and games -/

/-- A decoded `ME_Structure` body: the module's name and path, its globals, the
procedures its body defines, and the signatures it declares. -/
structure DecodedStructure where
  /-- The source module name. -/
  name : String
  /-- The module's path, the prefix of a call target inside it. -/
  path : String
  /-- The module's `var` declarations. -/
  globals : List EcGlobal
  /-- The procedures the body defines. -/
  procs : List DecodedProc
  /-- The signatures the module declares. -/
  declared : List (String × EcSig)

/-- Check that every declared signature is the signature of a defined
procedure. -/
def checkDeclared (name : String) (ps : List DecodedProc)
    (declared : List (String × EcSig)) : Except String Unit :=
  declared.forM (fun (n, s) =>
    match ps.find? (fun d => d.name == n) with
    | none =>
      fail s!"module '{name}' declares the procedure '{n}', which its body does \
        not define"
    | some d =>
      if d.sp.sig = s then .ok ()
      else
        fail s!"procedure '{n}' of module '{name}' is declared at a signature \
          other than the one its body has")

/-- Decode the `ME_Structure` body and declared signatures of a module item at
the module's source name and path. This is the part a concrete module and a
functor body have in common. -/
def decodeStructureBody (T : DecodeTables) (baseId : Nat) (name mpath : String)
    (modJ : Json) : Except String DecodedStructure := do
  let bodyJ ← getObj modJ "body"
  let bk ← getStr bodyJ "kind"
  if bk ≠ "ME_Structure" then
    fail s!"module '{name}' has body kind '{bk}': only ME_Structure has a \
      module image"
  else
    let modsA ← getArr bodyJ "modules"
    if !modsA.isEmpty then
      let describe := fun (mJ : Json) =>
        let n := (getStr mJ "name").toOption.getD "?"
        match mJ.getObjVal? "body" with
        | .ok mbJ =>
          let bk := (getStr mbJ "kind").toOption.getD "?"
          match getStr mbJ "target" with
          | .ok tgt => s!"'{n}' ({bk} of '{tgt}')"
          | .error _ => s!"'{n}' ({bk})"
        | .error _ => s!"'{n}'"
      let ds := String.intercalate ", " (modsA.toList.map describe)
      fail s!"module '{name}' nests {ds}, which the AST does not nest: a \
        nested ME_Alias names a module resolved against the enclosing module's \
        binders, and a nested ME_Structure reads the enclosing module's state \
        or parameters, so neither is a top-level module under another name"
    else
      let varsA ← getArr bodyJ "vars"
      let gs ← (varsA.toList.zip (List.range varsA.size)).mapM
        (fun (v, i) => do
          let nm ← getIdent v "name"
          let t ← decodeTyField T v "ty"
          if hEq : t.hasEq then
            .ok ({ name := xqualify mpath nm, id := baseId + i, ty := t
                   hasEq := hEq } : EcGlobal)
          else
            fail s!"module variable '{nm}' at the type {repr t}: a global \
              lives in the heap at a countable type, and a distribution's \
              carrier is not countable, so the variable has no heap cell")
      let T' := { gs.foldl DecodeTables.withGlobal T with modPath := mpath }
      let procsA ← getArr bodyJ "procs"
      let ps ← procsA.toList.mapM (decodeProc T')
      let declA ← getArr modJ "sig"
      let declared ← declA.toList.mapM (decodeSigDecl T')
      checkDeclared name ps declared
      .ok { name := name, path := mpath, globals := gs, procs := ps
            declared := declared }

/-- Decode a `Th_module` item whose body is an `ME_Structure` and which takes no
parameter. -/
def decodeStructure (T : DecodeTables) (baseId : Nat) (j : Json) :
    Except String DecodedStructure := do
  let kind ← getStr j "kind"
  if kind ≠ "Th_module" then
    fail s!"theory item of kind '{kind}': only Th_module has a module image"
  else
    let name ← getStr j "name"
    let mpath ← getStr j "path"
    let modJ ← getObj j "module"
    let params ← getArr modJ "params"
    if !params.isEmpty then
      fail s!"module '{name}' takes {params.size} parameters, so it is a functor: \
        decode it with decodeFunctor or decodeFunctorN"
    else
      decodeStructureBody T baseId name mpath modJ

/-- The interface a decoded structure declares. -/
def decodeInterface (S : DecodedStructure) : EcInterface :=
  { names := S.declared.map (·.1)
    sig := fun p => (sigProcOf (S.procs.map (fun d => (d.name, d.sp))) p).sig }

/-- Decode the procedure declarations of a module signature node — its `procs`
array — as an interface, reading nothing else of the node. A module parameter is
not a type, so a signature's procedures cannot mention one: the procedure list
is the same whether the signature binds parameters or not, and what a parameter
scopes — which of its oracles each procedure may call, the export's `oinfos` —
is not carried. -/
def decodeModSigProcs (T : DecodeTables) (j : Json) : Except String EcInterface := do
  let procsA ← getArr j "procs"
  let decls ← procsA.toList.mapM (decodeSigDecl T)
  .ok (interfaceOfSigs decls)

/-- Decode a module signature — the `sig` of a `Th_modtype` item — as an
interface: the procedure names it declares and their signatures. A module type
has no bodies, so this is the whole of what a module of that type offers. A
parameterised module signature is rejected here, so a parameterised `Th_modtype`
routes to `decodeModTypeN` (`FunctorN.lean`), which keeps the parameter list. -/
def decodeModSig (T : DecodeTables) (j : Json) : Except String EcInterface := do
  let params ← getArr j "params"
  if params.size ≠ 0 then
    fail s!"module signature of {params.size} parameter(s): EcInterface declares \
      the procedures of an unparameterised module type"
  else
    decodeModSigProcs T j

/-- Decode the interface of a `Th_modtype` item. -/
def decodeModTypeInterface (T : DecodeTables) (j : Json) : Except String EcInterface := do
  let k ← getStr j "kind"
  if k ≠ "Th_modtype" then
    fail s!"item of kind '{k}' read as a module type"
  else
    let sigJ ← getObj j "sig"
    decodeModSig T sigJ

/-- Decode the interface a module type node requires of a module: the `sig` the
exporter resolves for it, with the node's own arguments already substituted in.
A module type that itself binds module parameters — a functor parameter declared
at a parameterised module type — resolves to its procedure list all the same,
through `decodeModSigProcs`; the parameter list is dropped, and with it the
oracle access it scopes. -/
def decodeModTypeSig (T : DecodeTables) (j : Json) : Except String EcInterface := do
  let k ← getStr j "kind"
  if k ≠ "ModuleType" then
    fail s!"node of kind '{k}' read as a module type"
  else
    let sigJ ← getObj j "sig"
    decodeModSigProcs T sigJ

/-- Decode a `Th_type` item as the path of an abstract type. The item must
declare no type parameters, its body must be the exporter's `Abstract` node, and
it must carry no subtype predicate: a parameterised, concrete or subtype
declaration is not a bare abstract type, and each is rejected with a message
naming the respect. The caller registers the returned path with
`DecodeTables.withOpaqueType`. -/
def decodeThType (j : Json) : Except String String := do
  let k ← getStr j "kind"
  if k ≠ "Th_type" then
    fail s!"item of kind '{k}' read as a type declaration"
  else
    let path ← getStr j "path"
    let declJ ← getObj j "decl"
    let params ← getArr declJ "params"
    if !params.isEmpty then
      fail s!"type declaration '{path}' binds {params.size} type parameter(s): \
        the opaque code is nullary, so only a parameter-free abstract type \
        has one"
    else
      let bodyJ ← getObj declJ "body"
      let bodyKind ← getStr bodyJ "kind"
      if bodyKind ≠ "Abstract" then
        fail s!"type declaration '{path}' has body kind '{bodyKind}': only an \
          abstract type declaration has an opaque code, and a concrete body \
          names a type this declaration aliases rather than declares"
      else
        match declJ.getObjVal? "subtype" with
        | .ok Json.null | .error _ => .ok path
        | .ok _ =>
          fail s!"type declaration '{path}' carries a subtype predicate: the \
            export carries the carrier and the predicate but no inhabitation \
            witness, every EcTy code is inhabited, and a predicate over \
            abstract operators has no code-level decision procedure, so the \
            subtype has no code a decoder could check"

/-- Decode a `Th_type` item as a transparent type alias: a parameter-free
`Concrete` body without a subtype predicate, whose right-hand type decodes
against the tables. Returns the alias's path and the code it abbreviates. -/
def decodeThTypeAlias (T : DecodeTables) (j : Json) :
    Except String (String × EcTy) := do
  let k ← getStr j "kind"
  if k ≠ "Th_type" then
    fail s!"item of kind '{k}' read as a type declaration"
  else
    let path ← getStr j "path"
    let declJ ← getObj j "decl"
    let params ← getArr declJ "params"
    if !params.isEmpty then
      fail s!"type alias '{path}' binds {params.size} type parameter(s)"
    else
      match declJ.getObjVal? "subtype" with
      | .ok Json.null | .error _ =>
        let bodyJ ← getObj declJ "body"
        let bk ← getStr bodyJ "kind"
        if bk ≠ "Concrete" then
          fail s!"type declaration '{path}' has body kind '{bk}', which is not \
            a Concrete alias"
        else
          let t ← decodeTyField T bodyJ "ty"
          .ok (path, t)
      | .ok _ =>
        fail s!"type alias '{path}' carries a subtype predicate"

/-! ### Subtype declarations

EasyCrypt's `subtype t = {x : c | P x}` exports as a `Th_type` whose `decl.subtype`
carries the carrier, the predicate, and — from schema version 8 — `nonempty`, a
reference `{path, axiom_kind}` to the nonemptiness obligation the declaration's
`Top.Subtype` clone left in the environment. The environment holds no witness: the
obligation's statement is a declaration and its proof is discarded, so `nonempty`
names the obligation and nothing certifies it was discharged.

What a decoder can do with that is bounded by two facts. `EcTy.interp` is a plain
function, so a code is a closed value and its interpretation is inhabited by
construction; and every corpus predicate cuts its carrier down by an **abstract
operator** — `{x : int | 0 <= x < p}` for a declared `op p : int` — so the
interpretation depends on the realization of that operator and no closed code
denotes it. The image of a subtype declaration is therefore a code the theory's
instantiation supplies, as a function of the parameters the predicate names, and
what these decoders produce is the declaration: the carrier, the predicate's
shape, and the located obligation. A declaration whose `nonempty` does not resolve
is rejected: assuming inhabitation of a subtype that may be empty proves anything
about the theory. -/

/-- The prelude paths an integer-range predicate is recognised by. EasyCrypt's
`&&` is the `bool` conjunction and is a different operator from the `/\` of a
formula, which is why it is not in `DecodeTables.opPaths`. -/
structure RangePredPaths where
  /-- Boolean conjunction on `bool`. -/
  conj : String
  /-- The integer order, `a <= b`. -/
  le : String
  /-- The strict integer order, `a < b`. -/
  lt : String

/-- The paths EasyCrypt's prelude gives those three operators. -/
def ecRangePredPaths : RangePredPaths where
  conj := "Top.Pervasive.&&"
  le := "Top.CoreInt.le"
  lt := "Top.CoreInt.lt"

/-- The predicate shapes a `subtype` declaration is recognised at. -/
inductive EcSubtypePred where
  /-- `fun x => lo <= x && x < c`, with `lo` an integer literal and `c` the path
  of a nullary operator. The bound is a parameter, so the type the predicate cuts
  out is a function of the realization of `c`. -/
  | intRangeOp (lo : Int) (bound : String)
  deriving DecidableEq, Repr

/-- A `subtype` declaration: the path it declares, the carrier its predicate cuts
down, the predicate's shape, and the nonemptiness obligation the declaration left
in the environment. -/
structure EcSubtypeDecl where
  /-- The subtype's own path. -/
  path : String
  /-- The carrier code. -/
  carrier : EcTy
  /-- The predicate's shape. -/
  pred : EcSubtypePred
  /-- The path of the nonemptiness obligation, `exists x, P x`. -/
  nonempty : String
  /-- `Axiom` or `Lemma`, as the export records it for the obligation. In practice
  `Lemma`, since the `[prove]`-tagged axiom of `Top.Subtype` is raised to an
  obligation by the clone; `Lemma` says the obligation is a goal of the source
  development and not that it was discharged. -/
  nonemptyKind : String
  deriving DecidableEq, Repr

/-- The arguments of an application of the operator `p`, when the node is one at
the expected arity. -/
def appArgsOf (p : String) (n : Nat) (j : Json) : Except String (List Json) := do
  let k ← getStr j "kind"
  if k ≠ "Fapp" then
    fail s!"node of kind '{k}' read as an application of '{p}'"
  else
    let fJ ← getObj j "f"
    let fk ← getStr fJ "kind"
    if fk ≠ "Fop" then
      fail s!"application of a head of kind '{fk}' read as an application of '{p}'"
    else
      let q ← getStr fJ "path"
      if q ≠ p then
        fail s!"application of '{q}' where '{p}' was expected"
      else
        let args ← getArr j "args"
        if args.size ≠ n then
          fail s!"'{p}' applied to {args.size} arguments, expected {n}"
        else .ok args.toList

/-- The integer a node is, when the node is an integer literal. -/
def intLitOf (j : Json) : Except String Int := do
  let k ← getStr j "kind"
  if k ≠ "Fint" then
    fail s!"node of kind '{k}' read as an integer literal"
  else
    let v ← getStr j "value"
    match v.toInt? with
    | some z => .ok z
    | none => fail s!"integer literal '{v}' is not a decimal integer"

/-- Check that a node is an occurrence of the bound variable `x`. -/
def checkLocalIs (x : EcVarId) (j : Json) : Except String Unit := do
  let k ← getStr j "kind"
  if k ≠ "Flocal" then
    fail s!"node of kind '{k}' read as an occurrence of the bound variable"
  else
    let y ← getStampedIdent j
    if y = x then .ok ()
    else
      fail s!"occurrence of '{y.name}' where the binder '{x.name}' was expected"

/-- The path of a nullary operator, when the node is one. -/
def nullaryOpOf (j : Json) : Except String String := do
  let k ← getStr j "kind"
  if k ≠ "Fop" then
    fail s!"node of kind '{k}' read as a nullary operator"
  else
    getStr j "path"

/-- Read `fun (x : int) => lo <= x && x < c` off a subtype predicate node, with
`lo` an integer literal and `c` a nullary operator path. Every other shape is
rejected: the type a predicate cuts out is the predicate, so a predicate read
approximately would name a different type. -/
def decodeRangePred (P : RangePredPaths) (j : Json) :
    Except String EcSubtypePred := do
  let k ← getStr j "kind"
  if k ≠ "Fquant" then
    fail s!"subtype predicate of kind '{k}': the export writes it as a lambda"
  else
    let q ← getStr j "quant"
    if q ≠ "Llambda" then
      fail s!"subtype predicate quantified by '{q}', expected a lambda"
    else
      let bs ← getArr j "binders"
      match bs.toList with
      | [bJ] =>
        let x ← getStampedIdent bJ
        let bodyJ ← getObj j "body"
        let conj ← appArgsOf P.conj 2 bodyJ
        match conj with
        | [lowJ, highJ] =>
          let low ← appArgsOf P.le 2 lowJ
          let high ← appArgsOf P.lt 2 highJ
          match low, high with
          | [loJ, xJ], [xJ', cJ] =>
            let lo ← intLitOf loJ
            let _ ← checkLocalIs x xJ
            let _ ← checkLocalIs x xJ'
            let c ← nullaryOpOf cJ
            .ok (.intRangeOp lo c)
          | _, _ => fail "subtype predicate: the two comparisons are not binary"
        | _ => fail "subtype predicate: the conjunction is not binary"
      | _ =>
        fail s!"subtype predicate binding {bs.size} variables, expected 1"

/-- Decode a `Th_type` item as a `subtype` declaration. The item must declare no
type parameters and carry a `subtype` payload whose `nonempty` reference resolves;
its carrier must be `int` and its predicate the integer-range shape
`decodeRangePred` reads. Each respect is rejected with a message naming it, and
the reference is checked before the predicate: a declaration whose nonemptiness
obligation the export could not locate has no image at all, since inhabiting a
possibly-empty subtype by assumption makes every statement about the theory
hold. -/
def decodeThTypeSubtype (T : DecodeTables) (P : RangePredPaths) (j : Json) :
    Except String EcSubtypeDecl := do
  let k ← getStr j "kind"
  if k ≠ "Th_type" then
    fail s!"item of kind '{k}' read as a subtype declaration"
  else
    let path ← getStr j "path"
    let declJ ← getObj j "decl"
    let params ← getArr declJ "params"
    if !params.isEmpty then
      fail s!"subtype declaration '{path}' binds {params.size} type \
        parameter(s): EcTy has no type variables"
    else
      match declJ.getObjVal? "subtype" with
      | .error _ | .ok Json.null =>
        fail s!"type declaration '{path}' carries no subtype payload, so it \
          declares no subtype"
      | .ok subJ =>
        match subJ.getObjVal? "nonempty" with
        | .error _ | .ok Json.null =>
          fail s!"subtype declaration '{path}' carries no nonemptiness \
            obligation: the export could not locate the `exists x, P x` its \
            Top.Subtype clone left, and a subtype inhabited by assumption \
            rather than by that obligation makes every statement of the theory \
            hold"
        | .ok neJ =>
          let nePath ← getStr neJ "path"
          let neKind ← getStr neJ "axiom_kind"
          let carrier ← decodeTyField T subJ "carrier"
          if carrier ≠ EcTy.int then
            fail s!"subtype declaration '{path}' cuts down the carrier \
              {repr carrier}: the recognised predicate is an integer range, so \
              only the int carrier has an image"
          else
            let predJ ← getObj subJ "pred"
            let pred ← decodeRangePred P predJ
            .ok { path := path, carrier := carrier, pred := pred,
                  nonempty := nePath, nonemptyKind := neKind }

/-- Extend the tables with the code a `subtype` declaration's Lean image is at, so
that a type node naming the subtype decodes to it. The code is not a value a
decoder can produce — the predicate names an abstract operator, so the type it cuts
out is a function of that operator's realization — and the caller supplies it at
the instantiation. Taking the decoded declaration is what keeps a path that was
never validated from being registered. -/
def DecodeTables.withSubtype (T : DecodeTables) (d : EcSubtypeDecl) (t : EcTy) :
    DecodeTables :=
  T.withAliasType d.path t

/-- The `Th_type` items of one envelope item, in declaration order: the item
itself, or, for a `Th_theory` item, the type declarations among its items,
theory-inner theories included. An inner item's path is already fully
qualified (`Top.H.inleaks`), so registration is flat. -/
def thTypeItems (j : Json) : List Json :=
  match getStr j "kind" with
  | .ok "Th_type" => [j]
  | .ok "Th_theory" =>
    match _hitems : getArr j "items" with
    | .ok arr => (arr.toList.attach.map (fun ⟨x, _⟩ => thTypeItems x)).flatten
    | .error _ => []
  | _ => []
termination_by jsonSize j
decreasing_by
  exact getArr_decreases _hitems (Array.mem_toList_iff.mp ‹_ ∈ Array.toList _›)

/-! ### Datatype declarations

A `Th_type` item whose body is the exporter's `Datatype` node declares an
EasyCrypt datatype: a list of constructors, each with the types of the arguments
it takes. A declaration whose constructors all take no argument declares a type of
one value per constructor, and its image is `EcTy.fin k` at the number of them,
with the constructor in position `i` at the value `i` (`Ty.lean`). Its
constructors are nullary operators at paths in the declaring theory's namespace —
`Top.T.c` for a constructor `c` of `Top.T.d` — which is how a formula names one,
so registering the declaration registers the type's path and one constant per
constructor.

A constructor that takes an argument makes the declaration a sum, and `EcTy` has
no sum code; a declaration with no constructor denotes the empty type, which no
code interprets. Each is rejected with a message naming the respect. -/

/-- The namespace an EasyCrypt path sits in: the path without its last
component. -/
def pathNamespace (p : String) : String :=
  ".".intercalate (p.splitOn ".").dropLast

/-- An enumeration declaration: the declared type's path, and the paths of its
constructors in declaration order. -/
structure EcEnumDecl where
  /-- The declared type's path. -/
  path : String
  /-- The constructors' paths, in the order the declaration writes them. -/
  ctors : List String
  deriving DecidableEq, Repr

/-- Decode a `Th_type` item as an enumeration declaration. The item must declare
no type parameters, its body must be the exporter's `Datatype` node, and every
constructor of that body must take no argument; the declaration must name at
least one constructor. Each respect is rejected with a message naming it. The
constructor paths the result carries are the declaring path's namespace qualified
by each constructor's name, which is the path a formula names a constructor
by. -/
def decodeThTypeEnum (j : Json) : Except String EcEnumDecl := do
  let k ← getStr j "kind"
  if k ≠ "Th_type" then
    fail s!"item of kind '{k}' read as a datatype declaration"
  else
    let path ← getStr j "path"
    let declJ ← getObj j "decl"
    let params ← getArr declJ "params"
    if !params.isEmpty then
      fail s!"datatype declaration '{path}' binds {params.size} type \
        parameter(s): EcTy has no type variables, so a parameterised datatype \
        has no code"
    else
      let bodyJ ← getObj declJ "body"
      let bodyKind ← getStr bodyJ "kind"
      if bodyKind ≠ "Datatype" then
        fail s!"type declaration '{path}' has body kind '{bodyKind}', which \
          declares no datatype"
      else
        let ctorsA ← getArr bodyJ "ctors"
        let ns := pathNamespace path
        let names ← ctorsA.toList.mapM (fun cJ => do
          let nm ← getStr cJ "name"
          let args ← getArr cJ "args"
          if !args.isEmpty then
            fail s!"datatype declaration '{path}' has the constructor '{nm}' at \
              {args.size} argument(s): a constructor that takes an argument \
              makes the declaration a sum, and EcTy has no sum code"
          else .ok (ns ++ "." ++ nm))
        if names.isEmpty then
          fail s!"datatype declaration '{path}' names no constructor, so it \
            denotes the empty type, which no EcTy code interprets"
        else .ok { path := path, ctors := names }

/-- Extend the tables with an enumeration declaration: its path at the code of
its cardinality, and each constructor path at the value of its position. A
constructor at a path the ingestion already gives a meaning keeps that meaning
and does not register. -/
def DecodeTables.withEnumType (T : DecodeTables) (d : EcEnumDecl) :
    DecodeTables :=
  if h : 0 < d.ctors.length then
    let t : EcTy := .fin d.ctors.length h
    d.ctors.zipIdx.foldl
      (fun T (c, i) =>
        if hi : i < d.ctors.length then
          if (T.opMeaningOwner c).isSome then T
          else { T with
                 constPaths := (c, ⟨t, (⟨i, hi⟩ : Fin d.ctors.length)⟩) ::
                   T.constPaths }
        else T)
      (T.withAliasType d.path t)
  else T

/-! ### Realizing a subtype declaration

`EcSubtypeDecl` carries the range a `subtype` declaration cuts out of `int`, and
that range's upper bound is a nullary operator the theory declares. A decoder
produces closed values, so the code exists only against a realization of that
operator: `SubtypeBounds` is the realization, and it comes from the caller that
instantiates the theory, the way `Examples/ZModPSubtypeImport.lean` supplies the
modulus.

A realization naming the bound gives the concrete range code, whose
interpretation is a finite type, so a value of the subtype can be sampled.

Without one the subtype registers as an abstract type. That is the shape HOL
gives a type definition: the type is opaque, and its relation to the carrier
travels through the theory's own `val` and `insub` operators, which are abstract
operators here, under the axioms `Top.Subtype` states about them. A statement
about the subtype is then a statement about that type and those operators,
parametric in both. Registering the carrier under the subtype's name is a
different thing and not an alternative: a statement decoded at `int` is a
statement about the integers, and the subtype's values are the integers its
predicate keeps.

An abstract registration takes the type to be inhabited. The source's
nonemptiness obligation establishes that; `EcSubtypeDecl.nonempty` locates it,
and its `Lemma` kind does not say the source discharged it, so this rests on the
trust the ingestion already places in the export. A declaration carrying no such
obligation does not decode at all, so it never reaches either route.

A declaration outside the recognised shape, or a realization putting the bound at
or below the range's lower end, records the reason instead, so a type node at the
path reports it rather than an absent table entry. -/

/-- The realizations of the nullary integer operators subtype predicates take
their bounds from, keyed by the operator's path. -/
abbrev SubtypeBounds := List (String × Int)

/-- The operator path a predicate takes its upper bound from. -/
def EcSubtypePred.boundPath : EcSubtypePred → String
  | .intRangeOp _ bound => bound

/-- The code a subtype declaration denotes at a realization of its bound. A bound
the realization does not name has no value here, and a realization putting the
bound at or below the range's lower end makes the declared type empty, which no
`EcTy` code interprets; each is an error naming the bound. -/
def EcSubtypeDecl.codeAt (d : EcSubtypeDecl) (β : SubtypeBounds) :
    Except String EcTy :=
  match d.pred with
  | .intRangeOp lo bound =>
    match List.lookup bound β with
    | none =>
      fail s!"subtype '{d.path}' is cut out of int below '{bound}', an operator \
        its theory declares, and the realization supplied here gives that \
        operator no value: the code is the range below the realization, so the \
        instantiation of the theory is where it comes from"
    | some hi =>
      if h : lo < hi then .ok (.intRange lo hi h)
      else
        fail s!"subtype '{d.path}' at '{bound}' = {hi} keeps the integers x with \
          {lo} <= x < {hi}, of which there are none: the type is empty at this \
          realization, every EcTy interpretation is inhabited, and the theory's \
          own bound axiom is what rules the realization out"

/-- Record that `path` names a subtype the tables hold no code for, at the reason
there is none. -/
def DecodeTables.withPendingSubtype (T : DecodeTables) (path why : String) :
    DecodeTables :=
  { T with pendingSubtypes := (path, why) :: T.pendingSubtypes }

/-- A decode error as the reason a table entry carries: the message without the
stage tag the rest of it is read with. -/
def reasonOf (m : String) : String :=
  if m.startsWith "ec-import: " then (m.drop "ec-import: ".length).toString else m

/-- The path a `Th_type` item declares, when the item carries a `subtype`
payload. -/
def subtypePathOf (j : Json) : Option String :=
  match getStr j "kind", getStr j "path", j.getObjVal? "decl" with
  | .ok "Th_type", .ok path, .ok declJ =>
    match declJ.getObjVal? "subtype" with
    | .ok Json.null | .error _ => none
    | .ok _ => some path
  | _, _, _ => none

/-- The `subtype` declarations among `items`, in declaration order, theory-inner
declarations included. -/
def subtypeDeclsOf (T : DecodeTables) (P : RangePredPaths) (items : List Json) :
    List EcSubtypeDecl :=
  (items.flatMap thTypeItems).filterMap (fun it =>
    (decodeThTypeSubtype T P it).toOption)

/-- The realization each `subtype` declaration of `items` needs before it has a
code: the subtype's path at the operator path its bound reads. This is the list a
caller instantiating the theory builds its `SubtypeBounds` against. -/
def subtypeBoundsNeeded (T : DecodeTables) (P : RangePredPaths)
    (items : List Json) : List (String × String) :=
  (subtypeDeclsOf T P items).map (fun d => (d.path, d.pred.boundPath))

/-- Extend the tables with each `subtype` declaration of `items`: at the code the
realization `β` of its bound gives it, at the abstract type when `β` names no
realization for that bound, and at the pending entry carrying the reason when the
declaration is outside the recognised shape or the realization empties the
range. -/
def registerThTypeSubtypes (T : DecodeTables) (P : RangePredPaths)
    (β : SubtypeBounds) (items : List Json) : DecodeTables :=
  (items.flatMap thTypeItems).foldl (fun T it =>
    match subtypePathOf it with
    | none => T
    | some path =>
      match decodeThTypeSubtype T P it with
      | .error m => T.withPendingSubtype path (reasonOf m)
      | .ok d =>
        match d.codeAt β with
        | .ok t => T.withSubtype d t
        | .error m =>
          if (List.lookup d.pred.boundPath β).isNone then T.withOpaqueType d.path
          else T.withPendingSubtype path (reasonOf m)) T

/-- Extend the tables with every declaration of `items` that declares a type, in
declaration order: an abstract `Th_type` registers its path at the opaque code, a
parameter-free `Concrete` alias whose right-hand side decodes against the tables
built so far registers its path at that code, so an alias may mention an earlier
declaration, and an enumeration registers its path and its constructors. The
`Th_type` items of a `Th_theory` register at their fully qualified paths. An item
that decodes as none of the three is skipped here and reports its error wherever
it is decoded on its own. -/
def registerThTypeDecls (T : DecodeTables) (items : List Json) : DecodeTables :=
  (items.flatMap thTypeItems).foldl (fun T it =>
    match decodeThType it with
    | .ok path => T.withOpaqueType path
    | .error _ =>
      match decodeThTypeAlias T it with
      | .ok (path, t) => T.withAliasType path t
      | .error _ =>
        match decodeThTypeEnum it with
        | .ok d => T.withEnumType d
        | .error _ => T) T

/-- Extend the tables with every type declaration of `items`, and with the
`subtype` declarations at the realization `β` of their bounds. -/
def registerThTypesAt (T : DecodeTables) (items : List Json)
    (P : RangePredPaths) (β : SubtypeBounds) : DecodeTables :=
  registerThTypeSubtypes (registerThTypeDecls T items) P β items

/-- Extend the tables with every type declaration of `items` at the empty
realization: the abstract types, the aliases and the enumerations register at
their codes, and each `subtype` declaration registers as an abstract type, since
the empty realization names no bound. -/
def registerThTypes (T : DecodeTables) (items : List Json) : DecodeTables :=
  registerThTypesAt T items ecRangePredPaths []

/-! ### Cleared theories

EasyCrypt's `clear [T]` marks a theory so that a clone of the enclosing theory
does not carry it. The item the exporter writes for it names those theories and
declares nothing of its own — no type, no operator, no statement.

It is not a deletion of what precedes it: the envelope still exports the cleared
theory's own items, and the statements after the clear are read against them, so
registration and decoding are the same whether the item is read or skipped. What
it would change is the item list of a clone, and an envelope is imported as
exported rather than cloned. Its image is therefore the list of paths, which an
envelope walk reads and carries no further. -/

/-- Decode a `Th_clear` item as the paths it clears. -/
def decodeThClear (j : Json) : Except String (List String) := do
  let k ← getStr j "kind"
  if k ≠ "Th_clear" then
    fail s!"item of kind '{k}' read as a clear item"
  else
    let pathsA ← getArr j "paths"
    pathsA.toList.mapM (fun p =>
      match p with
      | .str s => .ok s
      | _ => fail s!"cleared path is not a name: {p.compress}")

/-! ### Abstract operator declarations

A theory-level `op f : T.` without a definition declares a name and its type. Its
image is a parameter of every imported statement that reads it, at the signature
the type gives it (`Params.lean`), so what a decoder produces here is the path and
the `EcSig`, and the caller registers the pair with
`DecodeTables.withAbstractOp`. A declaration of `n` arguments is at the signature
whose argument code is the arguments' codes as the right-nested product, which is
the code an application's arguments nest into (`EcTerm.nestArgs`), so a read of
the declaration decodes at the signature the declaration registers. -/

/-- The argument type codes and the result type code an operator's declared type
gives it: the domains of an arrow type, in source order, and the type the arrows
land in. A type node that is no arrow is the type of a declaration of no
argument, so it contributes no domain and is the result itself. A domain that is
itself an arrow has no `EcTy` code and is rejected there, by `decodeTy`. -/
def decodeArrowTy (T : DecodeTables) (j : Json) :
    Except String (List EcTy × EcTy) :=
  match getStr j "kind" with
  | .error e => .error e
  | .ok "Tfun" =>
    match getObj j "dom" with
    | .error e => .error e
    | .ok domJ =>
      match decodeTy T domJ with
      | .error e => .error e
      | .ok d =>
        match _hcod : getObj j "cod" with
        | .error e => .error e
        | .ok codJ =>
          match decodeArrowTy T codJ with
          | .error e => .error e
          | .ok (ds, r) => .ok (d :: ds, r)
  | .ok _ =>
    match decodeTy T j with
    | .error e => .error e
    | .ok t => .ok ([], t)
termination_by jsonSize j
decreasing_by exact getObj_decreases _hcod

/-- Decode a `Th_operator` item as an abstract operator declaration: the path it
declares, and the signature its type gives it. The item must declare no type
parameters, and its body must be the exporter's `Abstract` or `AbstractPred`
node; each respect is rejected with a message naming it, and an inductive
predicate — the exporter's `PR_Ind` body — is rejected before the type
parameters, since what rules it out holds at any number of them. The signature
an arrow type gives is its domains as the right-nested product `EcSig.arg`, the nesting
the arguments of an application carry (`EcTerm.nestArgs`), and the type the
arrows land in as `EcSig.res`; a declaration of no argument is at `⟨unit, t⟩`. -/
def decodeThOperatorAbstract (T : DecodeTables) (j : Json) :
    Except String (String × EcSig) := do
  let k ← getStr j "kind"
  if k ≠ "Th_operator" then
    fail s!"item of kind '{k}' read as an operator declaration"
  else
    let path ← getStr j "path"
    let declJ ← getObj j "decl"
    let bodyJ ← getObj declJ "body"
    let bodyKind ← getStr bodyJ "kind"
    let tparams ← getArr declJ "tparams"
    if bodyKind = "PR_Ind" then
      fail s!"operator declaration '{path}' is an inductive predicate: it holds \
        of exactly what its constructors derive, which is a least fixed point, \
        and a parameter at an EcSig is a value the statement quantifies over \
        rather than a definition, so the declaration has no image"
    else if !tparams.isEmpty then
      fail s!"operator declaration '{path}' binds {tparams.size} type \
        parameter(s): EcTy has no type variables, so a polymorphic declaration \
        has no EcSig to be a parameter at"
    else
      if bodyKind ≠ "Abstract" && bodyKind ≠ "AbstractPred" then
        fail s!"operator declaration '{path}' has body kind '{bodyKind}': a \
          declaration without a definition is the exporter's Abstract body, or \
          its AbstractPred body for a predicate, and a body names the term the \
          operator abbreviates rather than declaring a parameter"
      else
        let tyJ ← getObj declJ "ty"
        let dr ← decodeArrowTy T tyJ
        match dr.1 with
        | [] => .ok (path, ⟨.unit, dr.2⟩)
        | d :: rest => .ok (path, ⟨nestTuple d rest, dr.2⟩)

/-- Whether `path` occurs in `j` as the value of a `path` field. The test is on
the rendered node, so it also answers yes to a type node at that path; it is used
to reject a definition that reads the operator it defines, and a rejection is
reported by the decoder that made it. -/
def mentionsPath (path : String) (j : Json) : Bool :=
  1 < (j.compress.splitOn ("\"path\":" ++ (Json.str path).compress)).length

/-- The parameters and the body a concrete operator's defining form gives it, at
the argument codes `ds` its declared type gives.

A definition of no argument is its form. A definition of arguments is written as
a lambda, and it must bind exactly as many variables as the declared type takes
arguments: a lambda of fewer binders leaves a function-typed body, and `EcTy` has
no arrow code for one. Each binder carries its own type node, which must decode
at the code the declared type gives that position. -/
def decodeOpDefnParams (T : DecodeTables) (path : String) (ds : List EcTy)
    (j : Json) : Except String (List (EcVarId × EcTy) × Json) := do
  match ds with
  | [] => .ok ([], j)
  | _ =>
    let k ← getStr j "kind"
    if k ≠ "Fquant" then
      fail s!"operator definition '{path}' takes {ds.length} argument(s) and its \
        defining form is a node of kind '{k}': the export writes such a \
        definition as a lambda, and a form of another kind is a function-typed \
        term, which has no EcTy code"
    else
      let q ← getStr j "quant"
      if q ≠ "Llambda" then
        fail s!"operator definition '{path}' has a defining form quantified by \
          '{q}', expected a lambda"
      else
        let bs ← getArr j "binders"
        if bs.size ≠ ds.length then
          fail s!"operator definition '{path}' takes {ds.length} argument(s) and \
            its defining lambda binds {bs.size}: the residual body is \
            function-typed, which has no EcTy code"
        else
          let ps ← (bs.toList.zip ds).mapM (fun (bJ, d) => do
            let x ← getStampedIdent bJ
            let gtyJ ← getObj bJ "gty"
            let gk ← getStr gtyJ "kind"
            if gk ≠ "GTty" then
              fail s!"operator definition '{path}' binds '{x.name}' at a binder \
                type of kind '{gk}': a parameter of a definition is bound at a \
                type, and GTty is the node that carries one"
            else
              let tJ ← getObj gtyJ "ty"
              let bt ← decodeTy T tJ
              if bt ≠ d then
                fail s!"operator definition '{path}' binds '{x.name}' at type \
                  {repr bt}, and its declared type gives that argument \
                  {repr d}"
              else .ok ((x, d)))
          let bodyJ ← getObj j "body"
          .ok (ps, bodyJ)

/-- Decode a `Th_operator` item as a concrete operator declaration: the path it
defines, its parameters at their declared codes, the result code, and the body
node it abbreviates. The item must declare no type parameters and its body must
be the exporter's `OP_Plain` node, or its `PR_Plain` node for a predicate; each
respect is rejected with a message naming it, and so is a definition at a path
the ingestion has already committed to a meaning (`DecodeTables.opMeaningOwner`)
or one whose form reads the operator it defines.

The rejections are of the declaration, so a read of a rejected operator finds no
entry and fails naming the path. Registering a definition whose shape the
decoder did not check would instead give the path a meaning the source does not
have. -/
def decodeThOperatorConcrete (T : DecodeTables) (j : Json) :
    Except String EcOpDefn := do
  let k ← getStr j "kind"
  if k ≠ "Th_operator" then
    fail s!"item of kind '{k}' read as an operator definition"
  else
    let path ← getStr j "path"
    let declJ ← getObj j "decl"
    let tparams ← getArr declJ "tparams"
    if !tparams.isEmpty then
      fail s!"operator definition '{path}' binds {tparams.size} type \
        parameter(s): EcTy has no type variables, so the definition has no \
        codes to expand at"
    else
      let bodyJ ← getObj declJ "body"
      let bodyKind ← getStr bodyJ "kind"
      if bodyKind ≠ "OP_Plain" && bodyKind ≠ "PR_Plain" then
        fail s!"operator declaration '{path}' has body kind '{bodyKind}': a \
          definition the source writes as a term is the exporter's OP_Plain \
          body, or its PR_Plain body for a predicate; OP_Fix declares a \
          recursive operator and OB_nott a notation, and neither abbreviates a \
          term of the accepted fragment"
      else
        match T.opMeaningOwner path with
        | some tbl =>
          fail s!"operator definition '{path}' is at a path the ingestion's \
            {tbl} already gives a meaning: that entry decides what the path \
            denotes in both readers, so the definition does not register"
        | none =>
          let formJ ← getObj bodyJ "form"
          if mentionsPath path formJ then
            fail s!"operator definition '{path}' names its own path in its \
              defining form: a read of an operator that reads itself expands \
              without end, and a recursive operator is the exporter's OP_Fix \
              body"
          else
            let tyJ ← getObj declJ "ty"
            let dr ← decodeArrowTy T tyJ
            let pb ← decodeOpDefnParams T path dr.1 formJ
            .ok { path := path, params := pb.1, res := dr.2, body := pb.2 }

/-- The `Th_operator` items of one envelope item, in declaration order: the item
itself, or, for a `Th_theory` item, the operator declarations among its items,
theory-inner theories included. An inner item's path is already fully qualified,
so registration is flat. -/
def thOperatorItems (j : Json) : List Json :=
  match getStr j "kind" with
  | .ok "Th_operator" => [j]
  | .ok "Th_theory" =>
    match _hitems : getArr j "items" with
    | .ok arr => (arr.toList.attach.map (fun ⟨x, _⟩ => thOperatorItems x)).flatten
    | .error _ => []
  | _ => []
termination_by jsonSize j
decreasing_by
  exact getArr_decreases _hitems (Array.mem_toList_iff.mp ‹_ ∈ Array.toList _›)

/-- Read a `Th_operator` item that defines an operator over type parameters. The
checks are `decodeThOperatorConcrete`'s, less the ones that need codes: the body
is the exporter's `OP_Plain`, or `PR_Plain` for a predicate, the path carries no
meaning the ingestion already gives it, and the defining form does not read the
path it defines. Nothing here is decoded, since the declaration has no codes
until a read site gives its type parameters values. -/
def decodeThOperatorPoly (T : DecodeTables) (j : Json) :
    Except String EcPolyOpDefn := do
  let k ← getStr j "kind"
  if k ≠ "Th_operator" then
    fail s!"item of kind '{k}' read as an operator definition"
  else
    let path ← getStr j "path"
    let declJ ← getObj j "decl"
    let tparams ← getArr declJ "tparams"
    if tparams.isEmpty then
      fail s!"operator definition '{path}' binds no type parameter: a definition \
        whose types are codes already is an EcOpDefn"
    else
      let names ← tparams.toList.mapM (fun t =>
        match t with
        | .str s => .ok s
        | _ => fail s!"operator definition '{path}' has a type parameter that is \
            not a name: {t.compress}")
      let bodyJ ← getObj declJ "body"
      let bodyKind ← getStr bodyJ "kind"
      if bodyKind ≠ "OP_Plain" && bodyKind ≠ "PR_Plain" then
        fail s!"operator declaration '{path}' has body kind '{bodyKind}': a \
          definition the source writes as a term is the exporter's OP_Plain \
          body, or its PR_Plain body for a predicate"
      else
        match T.opMeaningOwner path with
        | some tbl =>
          fail s!"operator definition '{path}' is at a path the ingestion's \
            {tbl} already gives a meaning"
        | none =>
          let formJ ← getObj bodyJ "form"
          if mentionsPath path formJ then
            fail s!"operator definition '{path}' names its own path in its \
              defining form: a read of an operator that reads itself expands \
              without end"
          else
            .ok { path := path, tyParams := names, decl := declJ }

/-- Extend the tables with every operator declaration of `items`, in declaration
order: an abstract declaration as a parameter (`absOpPaths`), a concrete one as
its definition (`defOpPaths`), and one written over type parameters as the
declaration itself (`polyOpPaths`). An item that decodes as none of the three — a
recursive definition, a notation, one whose type has no `EcTy` code, one at a
path the ingestion already gives a meaning — is skipped here and reports its
error wherever it is decoded on its own. The type declarations register first
(`registerThTypes`), since an operator's type names them.

Declaration order is also the order a definition may read: EasyCrypt's scoping
lets a definition name only operators declared before it, so the definitions a
read expands through are registered before the one that reads them and the
expansion terminates. -/
def registerThOperators (T : DecodeTables) (items : List Json) : DecodeTables :=
  (items.flatMap thOperatorItems).foldl (fun T it =>
    match decodeThOperatorAbstract T it with
    | .ok (path, s) => T.withAbstractOp path s
    | .error _ =>
      match decodeThOperatorConcrete T it with
      | .ok d => T.withConcreteOp d
      | .error _ =>
        match decodeThOperatorPoly T it with
        | .ok d => T.withPolyOp d
        | .error _ => T) T

/-- The module a decoded structure is: its interface holds the names the module
declares, at the signatures its bodies have; `checkDeclared` has already checked
that the two agree. -/
def moduleOfStructure (S : DecodedStructure) : EcModule :=
  let L : List (String × SigProc) := S.procs.map (fun d => (d.name, d.sp))
  { name := S.name
    interface := { names := S.declared.map (·.1)
                   sig := fun p => (sigProcOf L p).sig }
    globals := S.globals
    procs := fun p => (sigProcOf L p).proc }

/-- Decode a concrete module. Heap location ids for the module's globals run from
`baseId` upwards in declaration order, so distinct modules must be decoded at
disjoint ranges. -/
def decodeModule (T : DecodeTables) (baseId : Nat) (j : Json) :
    Except String EcModule := do
  let S ← decodeStructure T baseId j
  .ok (moduleOfStructure S)

/-- Decode a `Th_module` item that takes one module parameter as an `EcFunctor`:
the parameter's source name is the prefix the body calls its procedures by, its
interface comes from the module type the parameter is declared at, and the
functor's body is the item's `ME_Structure`. -/
def decodeFunctor (T : DecodeTables) (baseId : Nat) (j : Json) :
    Except String EcFunctor := do
  let kind ← getStr j "kind"
  if kind ≠ "Th_module" then
    fail s!"theory item of kind '{kind}': only Th_module has a functor image"
  else
    let name ← getStr j "name"
    let mpath ← getStr j "path"
    let modJ ← getObj j "module"
    let paramsA ← getArr modJ "params"
    match paramsA.toList with
    | [] =>
      fail s!"module '{name}' takes no parameter, so it is a module rather than \
        a functor: decode it with decodeModule"
    | [pJ] =>
      -- The parameter's stamp is not read. A call to the parameter is exported
      -- as the cross-path `<name>./p`, which carries the source name alone, so
      -- the name is what the body resolves against, and a functor binds one
      -- parameter, which no second binder of that name can shadow.
      let pname ← getIdent pJ "name"
      let mtJ ← getObj pJ "modtype"
      let I ← decodeModTypeSig T mtJ
      -- The parameter's procedures are resolvable inside the body: a call that
      -- discards its result carries no result type, and the signature comes
      -- from the module type the parameter is declared at.
      let S ← decodeStructureBody (T.withInterfaceX pname I) baseId name mpath modJ
      .ok { name := name, paramName := pname, paramInterface := I
            body := moduleOfStructure S }
    | _ =>
      fail s!"functor '{name}' takes {paramsA.size} parameters: EcFunctor binds a \
        single parameter, so decode it with decodeFunctorN"

/-- The signature of a game's `main`. -/
def mainSig : EcSig := { arg := .unit, res := .bool }

/-- The signature of the argument-free procedures a game's `EcStmt.call`
reaches. -/
def auxSig : EcSig := { arg := .unit, res := .unit }

/-- Decode a module whose `main` returns a bit as an `EcGame`. The game's
procedure table holds the module's argument-free procedures under their source
names, which is the name `EcStmt.call` carries. A module with a procedure of any
other signature is not a game: its procedures are reached through `callProc`
against a resolution environment, so it decodes with `decodeModule`. -/
def decodeGame (T : DecodeTables) (baseId : Nat) (j : Json) :
    Except String EcGame := do
  let S ← decodeStructure T baseId j
  match S.procs.find? (fun d => d.name == "main") with
  | none =>
    fail s!"module '{S.name}' declares no procedure 'main', so it is not a game"
  | some m =>
    if h : m.sp.sig = mainSig then
      let main : EcProcAt mainSig := EcProcAt.castSig h m.sp.proc
      let others := S.procs.filter (fun d => d.name != "main")
      let procs ← others.mapM (fun d =>
        if h' : d.sp.sig = auxSig then
          .ok (d.name, (EcProcAt.castSig h' d.sp.proc).body)
        else
          fail s!"procedure '{d.name}' of module '{S.name}' takes an argument or \
            returns a value, and EcGame.procs holds argument-free procedures \
            that return none: decode the module with decodeModule and resolve \
            the call against a ProcEnv")
      .ok { name := S.name, locals := m.locals, procs := procs
            body := main.body, ret := main.ret }
    else
      fail s!"procedure 'main' of module '{S.name}' does not have the signature \
        from unit to bool, so the module is not a game"

/-! ## Envelope

The envelope's `schema` and `version` are checked before any item is decoded, and
the version check is an exact equality: accepting a range would mean ignoring
fields a newer exporter added. Every envelope field is read, including the
`skipped_not_declarations` tally that schema version 2 introduced — reading it
rather than tolerating it keeps the exact-equality check honest in both
directions, since a field this decoder never reads could be dropped upstream
without the version check noticing. -/

/-- The exporter's envelope: the provenance fields and the undecoded theory
items. -/
structure EcExport where
  /-- The EasyCrypt build identity the exporter records. An installation that
  carries no build hash reports `"n/a"` here, so the field identifies no
  installation in that case. -/
  ecHash : String
  /-- The digest of the exported source file. -/
  sourceDigest : Option String
  /-- The path of the exported source file. -/
  source : String
  /-- The theory path the items belong to. -/
  root : String
  /-- The top-level theory items, in source order. -/
  items : List Json
  /-- The global actions the exporter walked past because they declare nothing,
  tallied by EasyCrypt constructor. -/
  skipped : List (String × Nat)
  /-- The names declared inside a section that the top level does not bind once
  the section closes: the section's `declare`d modules and axioms, which closing
  the section turns into the binders and hypotheses of the statements that used
  them, and its `local` declarations. -/
  sectionLocal : List String

/-- Decode the exporter's tally of the global actions that declare nothing. -/
def decodeNotes (j : Json) : Except String (List (String × Nat)) :=
  match j with
  | .obj kvs =>
    kvs.toList.reverse.foldlM (fun acc (kv : String × Json) =>
      match kv.2.getNat? with
      | .ok n => .ok ((kv.1, n) :: acc)
      | .error _ =>
        fail s!"the tally for '{kv.1}' is not a natural number: {kv.2.compress}") []
  | v => fail s!"'skipped_not_declarations' is not an object: {v.compress}"

/-- Decode the envelope, checking the schema name and the schema version. -/
def decodeEnvelope (j : Json) : Except String EcExport := do
  let s ← getStr j "schema"
  if s ≠ schemaName then
    fail s!"export declares schema '{s}', this ingestion reads '{schemaName}'"
  else
    let v ← getNat j "version"
    if v ≠ schemaVersion then
      fail s!"schema version mismatch: export declares {v}, this ingestion \
        accepts {schemaVersion} exactly"
    else
      let ecHash ← getStr j "ec_hash"
      let source ← getStr j "source"
      let root ← getStr j "root"
      let items ← getArr j "items"
      let notesJ ← getObj j "skipped_not_declarations"
      let skipped ← decodeNotes notesJ
      let sectJ ← getArr j "section_local"
      let sectionLocal ← sectJ.toList.mapM (fun x =>
        match x with
        | .str s => .ok s
        | v => fail s!"the section-local name {v.compress} is not a string")
      .ok { ecHash := ecHash, sourceDigest := getStrOpt j "source_digest"
            source := source, root := root, items := items.toList
            skipped := skipped, sectionLocal := sectionLocal }

/-- The envelope item declaring the module `name`. -/
def findItem (e : EcExport) (name : String) : Except String Json :=
  match e.items.find? (fun it =>
      match it.getObjValAs? String "name" with
      | .ok n => n == name
      | .error _ => false) with
  | some it => .ok it
  | none =>
    let names := e.items.filterMap (fun it =>
      match it.getObjValAs? String "name" with
      | .ok n => some n
      | .error _ => none)
    fail s!"the export of '{e.source}' declares no item named '{name}'; it \
      declares {names}"

/-- Decode the game `name` from an exporter envelope. -/
def importGame (T : DecodeTables) (name : String) (j : Json) :
    Except String EcGame := do
  let e ← decodeEnvelope j
  let it ← findItem e name
  decodeGame T 0 it

/-- Decode the module `name` from an exporter envelope, with its globals at
location ids from `baseId` upwards. -/
def importModule (T : DecodeTables) (name : String) (j : Json)
    (baseId : Nat := 0) : Except String EcModule := do
  let e ← decodeEnvelope j
  let it ← findItem e name
  decodeModule T baseId it

/-- Decode the module type `name` from an exporter envelope. -/
def importModType (T : DecodeTables) (name : String) (j : Json) :
    Except String EcInterface := do
  let e ← decodeEnvelope j
  let it ← findItem e name
  decodeModTypeInterface T it

/-- Decode the functor `name` from an exporter envelope, with the globals of its
body at location ids from `baseId` upwards. -/
def importFunctor (T : DecodeTables) (name : String) (j : Json)
    (baseId : Nat := 0) : Except String EcFunctor := do
  let e ← decodeEnvelope j
  let it ← findItem e name
  decodeFunctor T baseId it

/-! ## Golden tests

The checks below decode the exporter's own output for a one-time-pad theory —
`otp.expected.json` in this directory, the export of a source file declaring
`OTP0` and `OTP1` (the two message variants of the `otpGame` of
`Examples/OTPImport.lean`) and `OTPArg` (a conditional, a typed formal parameter
and a call) — and match the result against the expected AST. A second fixture,
`nonunif.expected.json`, carries one module per distribution operator of the
`EcDistr` fragment.

Well-founded recursion is not definitionally reducible, so the checks are
`#guard` commands, evaluated when this module is built and a build error when
they fail, rather than `rfl` proofs; and they match on the expected AST rather
than comparing with `=`, since the intrinsically typed `EcExpr` family carries no
`DecidableEq` instance. -/

section Golden

/-- The exporter's output for the one-time-pad theory, as text. -/
private def otpExportText : String := include_str "otp.expected.json"

/-- The exporter's output for the one-time-pad theory. -/
private def otpExport : Json :=
  match Json.parse otpExportText with
  | .ok j => j
  | .error _ => Json.null

-- The fixture parses.
#guard (match otpExport with | Json.obj _ => true | _ => false)

-- `OTP0` imports as the `otpGame`-shaped AST at message `false`: two statements,
-- a uniform `bool` sample into `k` and the assignment `c <- k ^ false`, with `c`
-- returned and both locals declared.
#guard (match importGame ecPrelude "OTP0" otpExport with
        | .ok { name := "OTP0", locals := ["k", "c"], procs := [],
                body := [.sample .bool "k",
                         .assign .bool "c" (.bxor (.var .bool "k") (.lit false))],
                ret := .var .bool "c" } => true
        | _ => false)

-- `OTP1` is the same game at message `true`.
#guard (match importGame ecPrelude "OTP1" otpExport with
        | .ok { name := "OTP1", locals := ["k", "c"], procs := [],
                body := [.sample .bool "k",
                         .assign .bool "c" (.bxor (.var .bool "k") (.lit true))],
                ret := .var .bool "c" } => true
        | _ => false)

-- `OTPArg` has a procedure that takes an argument, so it is a module rather than
-- a game: its interface declares `main` and `enc`, it has no globals, and `main`
-- calls `enc` at the exporter's qualified name, binding the result to `r`.
#guard (match importModule ecPrelude "OTPArg" otpExport with
        | .ok M =>
          M.name == "OTPArg" && M.interface.names == ["main", "enc"]
            && M.globals.isEmpty
            && (match M.procs "main" with
                | { params := _, body := [.callProc "Top.OTPArg./enc" _ _ "r"],
                    ret := _ } => true
                | _ => false)
        | _ => false)

-- The body of `enc` is the sample, then the conditional whose branches assign
-- `c` — the `Sif` image — and its formal parameter is the source name `m`.
#guard (match importModule ecPrelude "OTPArg" otpExport with
        | .ok M =>
          (match M.procs "enc" with
           | { params := ["m"],
               body := [.sample .bool "k",
                        .ite (.var .bool "m")
                          [.assign .bool "c" (.bxor (.var .bool "k") (.lit true))]
                          [.assign .bool "c" (.var .bool "k")]],
               ret := _ } => true
           | _ => false)
        | _ => false)

-- The signature `enc` is declared at is the one its body has: from `bool` to
-- `bool`.
#guard (match importModule ecPrelude "OTPArg" otpExport with
        | .ok M => M.interface.sig "enc" == { arg := .bool, res := .bool }
        | _ => false)

-- An envelope whose version is not `schemaVersion` is rejected, and the message
-- names both numbers.
#guard (match importGame ecPrelude "OTP0"
            (Json.mkObj [("schema", Json.str schemaName), ("version", Json.num 2),
                         ("ec_hash", Json.str "n/a"), ("source", Json.str "otp.ec"),
                         ("root", Json.str "Top"), ("items", Json.arr #[]),
                         ("skipped_not_declarations", Json.mkObj []),
                         ("section_local", Json.arr #[])]) with
        | .error m =>
          m == s!"ec-import: schema version mismatch: export declares 2, this \
                 ingestion accepts {schemaVersion} exactly"
        | _ => false)

-- An envelope whose schema name is not `schemaName` is rejected.
#guard (match importGame ecPrelude "OTP0"
            (Json.mkObj [("schema", Json.str "hax-export"),
                         ("version", Json.num schemaVersion),
                         ("ec_hash", Json.str "n/a"), ("source", Json.str "otp.ec"),
                         ("root", Json.str "Top"), ("items", Json.arr #[]),
                         ("skipped_not_declarations", Json.mkObj []),
                         ("section_local", Json.arr #[])]) with
        | .error _ => true
        | _ => false)

-- An envelope of the accepted version that is missing a field this ingestion
-- reads is rejected: no envelope field has a default.
#guard (match importGame ecPrelude "OTP0"
            (Json.mkObj [("schema", Json.str schemaName),
                         ("version", Json.num schemaVersion),
                         ("ec_hash", Json.str "n/a"), ("source", Json.str "otp.ec"),
                         ("root", Json.str "Top"), ("items", Json.arr #[])]) with
        | .error _ => true
        | _ => false)

-- The tally of global actions that declare nothing is read, not skipped: the
-- one-time-pad theory's only such action is its `require import`.
#guard (match decodeEnvelope otpExport with
        | .ok e => e.skipped == [("GthRequire", 1)]
        | _ => false)

/-- The `bool` type node. -/
private def jBool : Json :=
  Json.mkObj [("kind", Json.str "Tconstr"),
              ("path", Json.str "Top.Pervasive.bool"), ("args", Json.arr #[])]

/-- The type node of a finite scalar type of cardinality three. -/
private def jWord : Json :=
  Json.mkObj [("kind", Json.str "Tconstr"), ("path", Json.str "Top.W.word"),
              ("args", Json.arr #[])]

/-- The code that type node reads as. Naming it keeps the cardinality proof out
of the argument position of a decode whose result is matched on. -/
private def wordTy : EcTy := .fin 3

/-- The tables extended with that finite scalar type, its addition, and the
uniform distribution on it. -/
private def wordTables : DecodeTables :=
  (ecPrelude.withFinType "Top.W.word" 3 "Top.W.+").withUniformDistr
    "Top.W.dword"

/-- A `word`-typed local-variable read. -/
private def jLocalWord (x : String) : Json :=
  Json.mkObj [("ty", jWord), ("kind", Json.str "Evar"),
              ("pv", Json.mkObj [("kind", Json.str "PVloc"), ("name", Json.str x)])]

/-- The instruction `y <- x + x` at the finite scalar type. -/
private def jWordAdd : Json :=
  Json.mkObj
    [("kind", Json.str "Sasgn"),
     ("lv", Json.mkObj
       [("kind", Json.str "LvVar"), ("ty", jWord),
        ("pv", Json.mkObj [("kind", Json.str "PVloc"), ("name", Json.str "y")])]),
     ("rhs", Json.mkObj
       [("ty", jWord), ("kind", Json.str "Eapp"),
        ("f", Json.mkObj
          [("ty", jWord), ("kind", Json.str "Eop"),
           ("path", Json.str "Top.W.+"), ("targs", Json.arr #[])]),
        ("args", Json.arr #[jLocalWord "x", jLocalWord "x"])])]

-- Addition at a finite scalar type decodes to `finAdd`, at the cardinality the
-- ingestion's type table records.
#guard (match decodeStmt wordTables jWordAdd with
        | .ok (.assign (.fin 3) "y"
                 (.finAdd (.var (.fin 3) "x") (.var (.fin 3) "x"))) => true
        | _ => false)

-- The finite scalar type is unknown to the default tables, so the same
-- instruction is rejected rather than decoded at some other type.
#guard (match decodeStmt ecPrelude jWordAdd with
        | .error _ => true
        | _ => false)

-- A nullary distribution operator outside the ingestion's uniform table is
-- rejected, so no other nullary distribution decodes to `EcStmt.sample`. The
-- `jSample` check below is the same shape at `Top.DBool.dbool`, which does decode.
#guard (match decodeStmt ecPrelude
            (Json.mkObj
              [("kind", Json.str "Srnd"),
               ("lv", Json.mkObj
                 [("kind", Json.str "LvVar"), ("ty", jBool),
                  ("pv", Json.mkObj [("kind", Json.str "PVloc"),
                                     ("name", Json.str "k")])]),
               ("distr", Json.mkObj
                 [("ty", Json.mkObj
                    [("kind", Json.str "Tconstr"),
                     ("path", Json.str "Top.Distr.distr"),
                     ("args", Json.arr #[jBool])]),
                  ("kind", Json.str "Eop"),
                  ("path", Json.str "Top.DBool.dbiased"),
                  ("targs", Json.arr #[])])]) with
        | .error _ => true
        | _ => false)

-- A literal in range decodes at `fin 3`.
#guard (match decodeExpr wordTables wordTy
            (Json.mkObj [("ty", jWord), ("kind", Json.str "Eint"),
                         ("value", Json.str "1")]) with
        | .ok (.lit ⟨1, _⟩) => true
        | _ => false)

-- An out-of-range literal at `fin 3` is rejected.
#guard (match decodeExpr wordTables wordTy
            (Json.mkObj [("ty", jWord), ("kind", Json.str "Eint"),
                         ("value", Json.str "7")]) with
        | .error _ => true
        | _ => false)

-- A node whose own type disagrees with the context is rejected.
#guard (match decodeExpr wordTables .bool (jLocalWord "x") with
        | .error _ => true
        | _ => false)

-- A while loop whose guard is not a comparison of a counter with an integer
-- literal is rejected: nothing bounds the number of iterations.
#guard (match decodeStmt ecPrelude
            (Json.mkObj [("kind", Json.str "Swhile"),
                         ("cond", Json.mkObj
                           [("ty", jBool), ("kind", Json.str "Eop"),
                            ("path", Json.str "Top.Pervasive.true"),
                            ("targs", Json.arr #[])]),
                         ("body", Json.arr #[])]) with
        | .error _ => true
        | _ => false)

-- A node the exporter marked as outside its coverage is rejected.
#guard (match decodeStmt ecPrelude
            (Json.mkObj [("kind", Json.str "Unsupported"),
                         ("what", Json.str "Smatch"),
                         ("pp", Json.str "match x with")]) with
        | .error _ => true
        | _ => false)

-- An argument-free call inside the enclosing module decodes to `EcStmt.call` at
-- the callee's source name.
#guard (match decodeStmt { ecPrelude with modPath := "Top.G" }
            (Json.mkObj [("kind", Json.str "Scall"), ("lv", Json.null),
                         ("proc", Json.str "Top.G./aux"),
                         ("args", Json.arr #[])]) with
        | .ok (.call "aux") => true
        | _ => false)

-- A call that discards its result outside the enclosing module is rejected,
-- because the schema carries no result type at the call site.
#guard (match decodeStmt { ecPrelude with modPath := "Top.G" }
            (Json.mkObj [("kind", Json.str "Scall"), ("lv", Json.null),
                         ("proc", Json.str "Top.H./aux"),
                         ("args", Json.arr #[])]) with
        | .error _ => true
        | _ => false)

/-- The type node of a nullary type constructor at the path `p`. -/
private def jTyConstr (p : String) : Json :=
  Json.mkObj [("kind", Json.str "Tconstr"), ("path", Json.str p),
              ("args", Json.arr #[])]

/-- The type node of the pair of the type nodes `a` and `b`. -/
private def jTyProd (a b : Json) : Json :=
  Json.mkObj [("kind", Json.str "Ttuple"), ("args", Json.arr #[a, b])]

/-- The type node of the binary type constructor `p` at the type nodes `a` and
`b`. -/
private def jTyApp (p : String) (a b : Json) : Json :=
  Json.mkObj [("kind", Json.str "Tconstr"), ("path", Json.str p),
              ("args", Json.arr #[a, b])]

/-- The `int` type node EasyCrypt's prelude writes. -/
private def jInt : Json := jTyConstr "Top.Pervasive.int"

/-- An integer literal node. -/
private def jIntLit (v : String) : Json :=
  Json.mkObj [("ty", jInt), ("kind", Json.str "Eint"), ("value", Json.str v)]

/-- Whether an expression is the integer literal `v`. The type index is a field
of the match, so that the literal's own type is `Int` in the comparison. -/
private def litIsInt {t : EcTy} (e : EcExpr t) (v : Int) : Bool :=
  match t, e.litValue with
  | .int, some w => w == v
  | _, _ => false

/-- Whether an expression is the boolean literal `v`. -/
private def litIsBool {t : EcTy} (e : EcExpr t) (v : Bool) : Bool :=
  match t, e.litValue with
  | .bool, some w => w == v
  | _, _ => false

/-- Whether an expression is the empty finite map. -/
private def litIsEmptyMap {t : EcTy} (e : EcExpr t) : Bool :=
  match t, e.litValue with
  | .map _ _, some m => m.isEmpty
  | _, _ => false

-- An integer literal decodes at the `int` code.
#guard (match decodeExpr ecPrelude .int (jIntLit "7") with
        | .ok e => litIsInt e 7
        | _ => false)

-- A negative integer literal decodes at the same code.
#guard (match decodeExpr ecPrelude .int (jIntLit "-7") with
        | .ok e => litIsInt e (-7)
        | _ => false)

-- A literal whose text is not a decimal integer is rejected.
#guard (match decodeExpr ecPrelude .int (jIntLit "0x7") with
        | .error _ => true
        | _ => false)

-- An integer literal at a code that is neither `fin` nor `int` is rejected,
-- rather than coerced.
#guard (match decodeExpr ecPrelude .bool
            (Json.mkObj [("ty", jBool), ("kind", Json.str "Eint"),
                         ("value", Json.str "1")]) with
        | .error _ => true
        | _ => false)

-- `int` is in the prelude table.
#guard (match decodeTy ecPrelude jInt with
        | .ok .int => true
        | _ => false)

-- A renamed clone of `int` decodes once its type path is in the table.
#guard (match decodeTy (ecPrelude.withIntType "Top.Int.int") (jTyConstr "Top.Int.int") with
        | .ok .int => true
        | _ => false)

-- and is rejected while it is not, since the table has no entry for the path.
#guard (match decodeTy ecPrelude (jTyConstr "Top.Int.int") with
        | .error _ => true
        | _ => false)

-- A finite map decodes at the key and value codes its own type arguments carry.
#guard (match decodeTy ecPrelude (jTyApp "Top.FMap.fmap" jInt jBool) with
        | .ok (.map .int .bool) => true
        | _ => false)

-- A map type constructor outside the table is rejected, at the same node shape.
#guard (match decodeTy ecPrelude (jTyApp "Top.SmtMap.fmap" jInt jBool) with
        | .error _ => true
        | _ => false)

-- and decodes once the path is registered.
#guard (match decodeTy (ecPrelude.withMapType "Top.SmtMap.fmap")
            (jTyApp "Top.SmtMap.fmap" jInt jBool) with
        | .ok (.map .int .bool) => true
        | _ => false)

-- A map type constructor at one type argument is rejected: the code is binary.
#guard (match decodeTy ecPrelude
            (Json.mkObj [("kind", Json.str "Tconstr"),
                         ("path", Json.str "Top.FMap.fmap"),
                         ("args", Json.arr #[jInt])]) with
        | .error _ => true
        | _ => false)

/-- The type node of the unary constructor `p` applied to the type node `a`. -/
private def jTyApp1 (p : String) (a : Json) : Json :=
  Json.mkObj [("kind", Json.str "Tconstr"), ("path", Json.str p),
              ("args", Json.arr #[a])]

-- An option type decodes at the code of its type argument.
#guard (match decodeTy ecPrelude (jTyApp1 "Top.Logic.option" jBool) with
        | .ok (.option .bool) => true
        | _ => false)

-- A list type decodes at the code of its type argument, an abstract type
-- included.
#guard (match decodeTy (ecPrelude.withOpaqueType "Top.t")
            (jTyApp1 "Top.List.list" (jTyConstr "Top.t")) with
        | .ok (.list (.opaque "Top.t")) => true
        | _ => false)

-- An option type constructor at two type arguments is rejected: the code is
-- unary.
#guard (match decodeTy ecPrelude (jTyApp "Top.Logic.option" jInt jBool) with
        | .error _ => true
        | _ => false)

-- The finite-set constructor decodes at the `Finset` code of its argument.
#guard (match decodeTy ecPrelude (jTyApp1 "Top.FSet.fset" jBool) with
        | .ok (.fset .bool) => true
        | _ => false)

-- Set equality is quotient equality: two insertion orders build one value.
#guard EcTy.fsetUnion (a := .int)
    (EcTy.fsetSingle (a := .int) (1 : Int)) (EcTy.fsetSingle (a := .int) (2 : Int))
  == EcTy.fsetUnion (a := .int)
    (EcTy.fsetSingle (a := .int) (2 : Int)) (EcTy.fsetSingle (a := .int) (1 : Int))

-- and the union of a set with itself is that set.
#guard EcTy.fsetUnion (a := .bool)
    (EcTy.fsetSingle (a := .bool) true) (EcTy.fsetSingle (a := .bool) true)
  == EcTy.fsetSingle (a := .bool) true

-- A tuple type of arity three decodes as the right-nested product.
#guard (match decodeTy ecPrelude
            (Json.mkObj [("kind", Json.str "Ttuple"),
                         ("args", Json.arr #[jInt, jBool, jInt])]) with
        | .ok (.prod .int (.prod .bool .int)) => true
        | _ => false)

-- The nesting is right-associated: an arity-four tuple is `a × (b × (c × d))`.
#guard (match decodeTy ecPrelude
            (Json.mkObj [("kind", Json.str "Ttuple"),
                         ("args", Json.arr #[jInt, jBool, jInt, jBool])]) with
        | .ok (.prod .int (.prod .bool (.prod .int .bool))) => true
        | _ => false)

/-- A `Th_type` item declaring the abstract type `Top.pkey`, at the exporter's
shape for `type pkey.`. -/
private def jThTypeAbstract : Json :=
  Json.mkObj [("kind", Json.str "Th_type"), ("name", Json.str "pkey"),
              ("path", Json.str "Top.pkey"),
              ("decl", Json.mkObj
                [("params", Json.arr #[]),
                 ("body", Json.mkObj [("kind", Json.str "Abstract")]),
                 ("subtype", Json.null)])]

-- An abstract type declaration decodes as its path.
#guard (match decodeThType jThTypeAbstract with
        | .ok p => p == "Top.pkey"
        | _ => false)

-- A type declaration with a concrete body is rejected: it aliases a type rather
-- than declaring one.
#guard (match decodeThType
            (Json.mkObj [("kind", Json.str "Th_type"), ("name", Json.str "t"),
                         ("path", Json.str "Top.t"),
                         ("decl", Json.mkObj
                           [("params", Json.arr #[]),
                            ("body", Json.mkObj
                              [("kind", Json.str "Concrete"), ("ty", jInt)]),
                            ("subtype", Json.null)])]) with
        | .error _ => true
        | _ => false)

-- A parameterised type declaration is rejected: only a nullary abstract type
-- has an opaque code.
#guard (match decodeThType
            (Json.mkObj [("kind", Json.str "Th_type"), ("name", Json.str "t"),
                         ("path", Json.str "Top.t"),
                         ("decl", Json.mkObj
                           [("params", Json.arr #[Json.str "'a"]),
                            ("body", Json.mkObj [("kind", Json.str "Abstract")]),
                            ("subtype", Json.null)])]) with
        | .error _ => true
        | _ => false)

-- A type node at the abstract type's path is rejected against the default
-- tables, and decodes at the opaque code once the declaration is registered.
#guard (match decodeTy ecPrelude (jTyConstr "Top.pkey") with
        | .error _ => true
        | _ => false)
#guard (match decodeTy (registerThTypes ecPrelude [jThTypeAbstract])
            (jTyConstr "Top.pkey") with
        | .ok (.opaque "Top.pkey") => true
        | _ => false)

/-- A `Th_type` item declaring the abstract type `Top.T.t` inside a theory, at
the fully qualified path the exporter writes for it. -/
private def jThTypeInner : Json :=
  Json.mkObj [("kind", Json.str "Th_type"), ("name", Json.str "t"),
              ("path", Json.str "Top.T.t"),
              ("decl", Json.mkObj
                [("params", Json.arr #[]),
                 ("body", Json.mkObj [("kind", Json.str "Abstract")]),
                 ("subtype", Json.null)])]

/-- A `Th_theory` item holding that declaration, at the exporter's shape for a
named theory. -/
private def jThTheory : Json :=
  Json.mkObj [("kind", Json.str "Th_theory"), ("name", Json.str "T"),
              ("path", Json.str "Top.T"), ("mode", Json.str "abstract"),
              ("source", Json.null),
              ("items", Json.arr #[jThTypeInner])]

-- A theory's inner `Th_type` registers at its fully qualified path.
#guard (match decodeTy (registerThTypes ecPrelude [jThTheory])
            (jTyConstr "Top.T.t") with
        | .ok (.opaque "Top.T.t") => true
        | _ => false)

-- Registration recurses through a nested theory.
#guard (match decodeTy (registerThTypes ecPrelude
              [Json.mkObj [("kind", Json.str "Th_theory"), ("name", Json.str "O"),
                           ("path", Json.str "Top.O"),
                           ("mode", Json.str "concrete"), ("source", Json.null),
                           ("items", Json.arr #[jThTheory])]])
            (jTyConstr "Top.T.t") with
        | .ok (.opaque "Top.T.t") => true
        | _ => false)

/-- A `Th_type` item declaring the transparent alias `Top.keys = Top.pkey
fset`, at the exporter's shape for a `Concrete` body. -/
private def jThTypeAlias : Json :=
  Json.mkObj [("kind", Json.str "Th_type"), ("name", Json.str "keys"),
              ("path", Json.str "Top.keys"),
              ("decl", Json.mkObj
                [("params", Json.arr #[]),
                 ("body", Json.mkObj
                   [("kind", Json.str "Concrete"),
                    ("ty", jTyApp1 "Top.FSet.fset" (jTyConstr "Top.pkey"))]),
                 ("subtype", Json.null)])]

-- A Concrete alias registers at its decoded right-hand code, resolved against
-- the declarations before it.
#guard (match decodeTy (registerThTypes ecPrelude [jThTypeAbstract, jThTypeAlias])
            (jTyConstr "Top.keys") with
        | .ok (.fset (.opaque "Top.pkey")) => true
        | _ => false)

-- and stays unregistered while its right-hand side does not resolve.
#guard (match decodeTy (registerThTypes ecPrelude [jThTypeAlias])
            (jTyConstr "Top.keys") with
        | .error _ => true
        | _ => false)

/-- A `Th_type` item at the exporter's shape for a subtype declaration — the
`Top.word` of `datatypes/Word.eca`: an `Abstract` body beside a `subtype` node
carrying the carrier and the predicate, and no inhabitation witness. -/
private def jThTypeSubtype : Json :=
  Json.mkObj [("kind", Json.str "Th_type"), ("name", Json.str "word"),
              ("path", Json.str "Top.word"),
              ("decl", Json.mkObj
                [("params", Json.arr #[]),
                 ("body", Json.mkObj [("kind", Json.str "Abstract")]),
                 ("subtype", Json.mkObj
                   [("carrier",
                     jTyApp1 "Top.List.list" (jTyConstr "Top.Alphabet.t")),
                    ("pred", Json.mkObj [("kind", Json.str "Fquant")])])])]

-- A subtype declaration is rejected, and the message names the missing
-- inhabitation witness.
#guard (match decodeThType jThTypeSubtype with
        | .error m => m.startsWith
            "ec-import: type declaration 'Top.word' carries a subtype predicate"
        | _ => false)

-- Registration skips a subtype declaration rather than registering the bare
-- carrier under the subtype's name.
#guard (match decodeTy (registerThTypes ecPrelude [jThTypeSubtype])
            (jTyConstr "Top.word") with
        | .error _ => true
        | _ => false)

/-! ### Abstract operator declarations

The items below are the exported shapes of `crypto/PRF.eca`, transcribed from an
envelope of schema version 8:

```
type D.
type R.

abstract theory RF.
  op dR : D -> R distr.
end RF.

abstract theory PseudoRF.
  type K.
  op dK : K distr.
  op F : K -> D -> R.
end PseudoRF.
```
-/

/-- The type node of the arrow from the type node `a` to the type node `b`. -/
def jTyArrow (a b : Json) : Json :=
  Json.mkObj [("kind", Json.str "Tfun"), ("dom", a), ("cod", b)]

/-- The `Th_type` item declaring the abstract type `name` at `path`. -/
def jAbsTypeDecl (name path : String) : Json :=
  Json.mkObj [("kind", Json.str "Th_type"), ("name", Json.str name),
              ("path", Json.str path),
              ("decl", Json.mkObj
                [("params", Json.arr #[]),
                 ("body", Json.mkObj [("kind", Json.str "Abstract")]),
                 ("subtype", Json.null)])]

/-- The `Th_operator` item declaring `name` at `path`, at the type node `ty`,
with the body kind `bodyKind`. -/
private def jOpDecl (name path : String) (ty : Json) (bodyKind : String) : Json :=
  Json.mkObj [("kind", Json.str "Th_operator"), ("name", Json.str name),
              ("path", Json.str path),
              ("decl", Json.mkObj
                [("tparams", Json.arr #[]), ("ty", ty),
                 ("body", Json.mkObj [("kind", Json.str bodyKind)])])]

/-- The `Th_theory` item named `name` at `path`, holding `items`. -/
private def jTheoryDecl (name path : String) (items : Array Json) : Json :=
  Json.mkObj [("kind", Json.str "Th_theory"), ("name", Json.str name),
              ("path", Json.str path), ("mode", Json.str "abstract"),
              ("source", Json.null), ("items", Json.arr items)]

/-- The `Th_type` items declaring `PRF.eca`'s domain and range. -/
private def jPRFTypeD : Json := jAbsTypeDecl "D" "Top.D"

private def jPRFTypeR : Json := jAbsTypeDecl "R" "Top.R"

/-- The `Th_type` item declaring `PseudoRF`'s carrier. -/
private def jPRFTypeK : Json := jAbsTypeDecl "K" "Top.PseudoRF.K"

/-- The `Th_operator` item declaring the one-argument `dR : D -> R distr`. -/
private def jRFOpDR : Json :=
  jOpDecl "dR" "Top.RF.dR"
    (jTyArrow (jTyConstr "Top.D")
      (jTyApp1 "Top.Distr.distr" (jTyConstr "Top.R"))) "Abstract"

/-- The `Th_theory` item holding `RF`'s declaration. -/
private def jRFTheory : Json := jTheoryDecl "RF" "Top.RF" #[jRFOpDR]

/-- The `Th_operator` item declaring the abstract distribution `dK : K distr`. -/
private def jPRFOpDK : Json :=
  jOpDecl "dK" "Top.PseudoRF.dK"
    (jTyApp1 "Top.Distr.distr" (jTyConstr "Top.PseudoRF.K")) "Abstract"

/-- The `Th_operator` item declaring the two-argument `F : K -> D -> R`. -/
private def jPRFOpF : Json :=
  jOpDecl "F" "Top.PseudoRF.F"
    (jTyArrow (jTyConstr "Top.PseudoRF.K")
      (jTyArrow (jTyConstr "Top.D") (jTyConstr "Top.R"))) "Abstract"

/-- The `Th_theory` item holding `PseudoRF`'s three declarations. -/
private def jPRFTheory : Json :=
  jTheoryDecl "PseudoRF" "Top.PseudoRF" #[jPRFTypeK, jPRFOpDK, jPRFOpF]

/-- The envelope items of `PRF.eca`'s declarations, in declaration order. -/
private def jPRFItems : List Json :=
  [jPRFTypeD, jPRFTypeR, jRFTheory, jPRFTheory]

/-- The tables `PRF.eca`'s statements decode against: its carriers at the opaque
codes, then its abstract operators. -/
private def prfTables : DecodeTables :=
  registerThOperators (registerThTypes ecPrelude jPRFItems) jPRFItems

/-- The tables the operator declarations resolve their types against. -/
private def prfTyTables : DecodeTables := registerThTypes ecPrelude jPRFItems

-- The distribution-typed declaration decodes as a nullary signature at the
-- distribution code over its carrier.
#guard (match decodeThOperatorAbstract prfTyTables jPRFOpDK with
        | .ok (p, s) =>
            p == "Top.PseudoRF.dK"
              && s == { arg := .unit, res := .distr (.opaque "Top.PseudoRF.K") }
        | _ => false)

-- A declaration of one argument is at the signature whose argument code is that
-- argument's own code, and whose result code is what the arrow lands in.
#guard (match decodeThOperatorAbstract prfTyTables jRFOpDR with
        | .ok (p, s) =>
            p == "Top.RF.dR"
              && s == { arg := .opaque "Top.D", res := .distr (.opaque "Top.R") }
        | _ => false)

-- A declaration of two arguments is at the signature whose argument code is the
-- two codes as the pair, in source order.
#guard (match decodeThOperatorAbstract prfTyTables jPRFOpF with
        | .ok (p, s) =>
            p == "Top.PseudoRF.F"
              && s == { arg := .prod (.opaque "Top.PseudoRF.K") (.opaque "Top.D"),
                        res := .opaque "Top.R" }
        | _ => false)

-- and each registers under its path, through the theory walk.
#guard prfTables.absOpPaths.map Prod.fst
  == ["Top.PseudoRF.F", "Top.PseudoRF.dK", "Top.RF.dR"]

#guard List.lookup "Top.PseudoRF.F" prfTables.absOpPaths
  == some { arg := EcTy.prod (EcTy.opaque "Top.PseudoRF.K") (EcTy.opaque "Top.D"),
            res := EcTy.opaque "Top.R" }

-- A declaration whose carrier is not registered is rejected: the operator's type
-- resolves against the type table, and an unregistered path has no code.
#guard (match decodeThOperatorAbstract ecPrelude jPRFOpDK with
        | .error _ => true
        | _ => false)

/-! The items below are the exported shapes of `crypto/assumptions/AEAD.ec`:

```
type K, AData, Msg, Cph.
op enc : K -> AData -> Msg -> Cph distr.
```
-/

/-- The `Th_type` items of the four carriers `enc` is declared over. -/
private def jAeadTypes : List Json :=
  [jAbsTypeDecl "K" "Top.K", jAbsTypeDecl "AData" "Top.AData",
   jAbsTypeDecl "Msg" "Top.Msg", jAbsTypeDecl "Cph" "Top.Cph"]

/-- The `Th_operator` item declaring the three-argument
`enc : K -> AData -> Msg -> Cph distr`. -/
private def jAeadOpEnc : Json :=
  jOpDecl "enc" "Top.enc"
    (jTyArrow (jTyConstr "Top.K")
      (jTyArrow (jTyConstr "Top.AData")
        (jTyArrow (jTyConstr "Top.Msg")
          (jTyApp1 "Top.Distr.distr" (jTyConstr "Top.Cph"))))) "Abstract"

-- A declaration of three arguments is at the signature whose argument code is
-- the three codes as the right-nested product.
#guard (match decodeThOperatorAbstract (registerThTypes ecPrelude jAeadTypes)
            jAeadOpEnc with
        | .ok (p, s) =>
            p == "Top.enc"
              && s == { arg := .prod (.opaque "Top.K")
                                 (.prod (.opaque "Top.AData") (.opaque "Top.Msg")),
                        res := .distr (.opaque "Top.Cph") }
        | _ => false)

/-- The `Th_operator` item of `algebra/Ring.ec`'s `pred unit : t -> bool`, whose
body is the exporter's `AbstractPred` node. -/
private def jZRUnitPred : Json :=
  jOpDecl "unit" "Top.ZR.unit" (jTyArrow (jTyConstr "Top.ZR.t") jBool)
    "AbstractPred"

-- A predicate declaration is at the signature its type gives it, the booleans as
-- the result code.
#guard (match decodeThOperatorAbstract
            (registerThTypes ecPrelude [jAbsTypeDecl "t" "Top.ZR.t"])
            jZRUnitPred with
        | .ok (p, s) =>
            p == "Top.ZR.unit" && s == { arg := .opaque "Top.ZR.t", res := .bool }
        | _ => false)

-- A declaration whose argument is itself a function is rejected: an arrow has no
-- EcTy code, so the argument has none to be a component of.
#guard (match decodeThOperatorAbstract prfTyTables
            (jOpDecl "h" "Top.h"
              (jTyArrow (jTyArrow (jTyConstr "Top.D") (jTyConstr "Top.R"))
                (jTyConstr "Top.R")) "Abstract") with
        | .error m => m.startsWith
            "ec-import: unsupported type node kind 'Tfun'"
        | _ => false)

-- A polymorphic declaration is rejected by its type parameters.
#guard (match decodeThOperatorAbstract ecPrelude
            (Json.mkObj [("kind", Json.str "Th_operator"), ("name", Json.str "d"),
                         ("path", Json.str "Top.d"),
                         ("decl", Json.mkObj
                           [("tparams", Json.arr #[Json.str "'a"]),
                            ("ty", jTyArrow jBool jBool),
                            ("body", Json.mkObj
                              [("kind", Json.str "Abstract")])])]) with
        | .error m => m.startsWith
            "ec-import: operator declaration 'Top.d' binds 1 type parameter(s)"
        | _ => false)

/-! ### A subtype declaration

The item below is the exported shape of `algebra/ZModP.ec`'s

```
op p : int.
axiom ge2_p : 2 <= p.
subtype zmod = {x : int | 0 <= x < p}.
```

transcribed from an envelope of schema version 8. The bound is the declared `p`,
so the type the predicate cuts out is a function of `p`'s realization, and what
decodes is the declaration: the carrier, the range, and the path of the
nonemptiness obligation. `Examples/ZModPSubtypeImport.lean` supplies the code and
discharges the obligation from `ge2_p`. -/

/-- The `bool` type node. -/
private def jSubBool : Json := jTyConstr "Top.Pervasive.bool"

/-- The bound variable of the predicate, at the stamp the export writes. -/
private def jSubBinderX : Json :=
  Json.mkObj [("name", Json.str "x"), ("stamp", Json.num 86007),
              ("gty", Json.mkObj [("kind", Json.str "GTty"), ("ty", jInt)])]

/-- An integer literal in formula position. -/
private def jSubIntLit (v : String) : Json :=
  Json.mkObj [("ty", jInt), ("kind", Json.str "Fint"), ("value", Json.str v)]

/-- An occurrence of that variable. -/
private def jSubX : Json :=
  Json.mkObj [("ty", jInt), ("kind", Json.str "Flocal"),
              ("name", Json.str "x"), ("stamp", Json.num 86007)]

/-- An application of the integer comparison at `path` to `a` and `b`. -/
private def jSubCmp (path : String) (a b : Json) : Json :=
  Json.mkObj
    [("ty", jSubBool), ("kind", Json.str "Fapp"),
     ("f", Json.mkObj
       [("ty", Json.mkObj
          [("kind", Json.str "Tfun"), ("dom", jInt),
           ("cod", Json.mkObj
             [("kind", Json.str "Tfun"), ("dom", jInt), ("cod", jSubBool)])]),
        ("kind", Json.str "Fop"), ("path", Json.str path),
        ("targs", Json.arr #[])]),
     ("args", Json.arr #[a, b])]

/-- The predicate `fun (x : int) => 0 <= x && x < p`. -/
private def jSubPred (boundPath : String) : Json :=
  Json.mkObj
    [("ty", Json.mkObj
       [("kind", Json.str "Tfun"), ("dom", jInt), ("cod", jSubBool)]),
     ("kind", Json.str "Fquant"), ("quant", Json.str "Llambda"),
     ("binders", Json.arr #[jSubBinderX]),
     ("body", Json.mkObj
       [("ty", jSubBool), ("kind", Json.str "Fapp"),
        ("f", Json.mkObj
          [("ty", Json.mkObj
             [("kind", Json.str "Tfun"), ("dom", jSubBool),
              ("cod", Json.mkObj
                [("kind", Json.str "Tfun"), ("dom", jSubBool),
                 ("cod", jSubBool)])]),
           ("kind", Json.str "Fop"),
           ("path", Json.str "Top.Pervasive.&&"), ("targs", Json.arr #[])]),
        ("args", Json.arr
          #[jSubCmp "Top.CoreInt.le" (jSubIntLit "0") jSubX,
            jSubCmp "Top.CoreInt.lt" jSubX
              (Json.mkObj [("ty", jInt), ("kind", Json.str "Fop"),
                           ("path", Json.str boundPath),
                           ("targs", Json.arr #[])])])])]

/-- The `Th_type` item of `subtype zmod = {x : int | 0 <= x < p}`. -/
private def jZModSubtype : Json :=
  Json.mkObj
    [("kind", Json.str "Th_type"), ("name", Json.str "zmod"),
     ("path", Json.str "Top.ZModRing.zmod"),
     ("decl", Json.mkObj
       [("params", Json.arr #[]),
        ("body", Json.mkObj [("kind", Json.str "Abstract")]),
        ("subtype", Json.mkObj
          [("carrier", jInt), ("pred", jSubPred "Top.ZModRing.p"),
           ("nonempty", Json.mkObj
             [("path", Json.str "Top.ZModRing.Sub.inhabited"),
              ("axiom_kind", Json.str "Lemma")])])])]

-- The declaration decodes as its carrier, its range, and the located obligation.
#guard (match decodeThTypeSubtype ecPrelude ecRangePredPaths jZModSubtype with
        | .ok d =>
            d == { path := "Top.ZModRing.zmod", carrier := EcTy.int,
                   pred := .intRangeOp 0 "Top.ZModRing.p",
                   nonempty := "Top.ZModRing.Sub.inhabited",
                   nonemptyKind := "Lemma" }
        | _ => false)

-- The same declaration without the reference is rejected, and the message names
-- what assuming inhabitation would cost.
#guard (match decodeThTypeSubtype ecPrelude ecRangePredPaths
            (Json.mkObj
              [("kind", Json.str "Th_type"), ("name", Json.str "zmod"),
               ("path", Json.str "Top.ZModRing.zmod"),
               ("decl", Json.mkObj
                 [("params", Json.arr #[]),
                  ("body", Json.mkObj [("kind", Json.str "Abstract")]),
                  ("subtype", Json.mkObj
                    [("carrier", jInt), ("pred", jSubPred "Top.ZModRing.p"),
                     ("nonempty", Json.null)])])]) with
        | .error m => m.startsWith
            "ec-import: subtype declaration 'Top.ZModRing.zmod' carries no \
             nonemptiness obligation"
        | _ => false)

-- The `Top.word` fixture above carries neither a `nonempty` key nor a recognised
-- predicate, and is rejected by the reference rather than by the predicate.
#guard (match decodeThTypeSubtype ecPrelude ecRangePredPaths jThTypeSubtype with
        | .error m => m.startsWith
            "ec-import: subtype declaration 'Top.word' carries no nonemptiness \
             obligation"
        | _ => false)

-- A declaration whose carrier is not `int` is rejected: the recognised predicate
-- is an integer range.
#guard (match decodeThTypeSubtype ecPrelude ecRangePredPaths
            (Json.mkObj
              [("kind", Json.str "Th_type"), ("name", Json.str "w"),
               ("path", Json.str "Top.w"),
               ("decl", Json.mkObj
                 [("params", Json.arr #[]),
                  ("body", Json.mkObj [("kind", Json.str "Abstract")]),
                  ("subtype", Json.mkObj
                    [("carrier", jTyApp1 "Top.List.list" jBool),
                     ("pred", jSubPred "Top.ZModRing.p"),
                     ("nonempty", Json.mkObj
                       [("path", Json.str "Top.inhabited"),
                        ("axiom_kind", Json.str "Lemma")])])])]) with
        | .error m => m.startsWith
            "ec-import: subtype declaration 'Top.w' cuts down the carrier"
        | _ => false)

-- A predicate outside the recognised shape is rejected rather than approximated.
#guard (match decodeThTypeSubtype ecPrelude ecRangePredPaths
            (Json.mkObj
              [("kind", Json.str "Th_type"), ("name", Json.str "w"),
               ("path", Json.str "Top.w"),
               ("decl", Json.mkObj
                 [("params", Json.arr #[]),
                  ("body", Json.mkObj [("kind", Json.str "Abstract")]),
                  ("subtype", Json.mkObj
                    [("carrier", jInt),
                     ("pred", Json.mkObj [("kind", Json.str "Fop"),
                                          ("path", Json.str "Top.pred"),
                                          ("targs", Json.arr #[])]),
                     ("nonempty", Json.mkObj
                       [("path", Json.str "Top.inhabited"),
                        ("axiom_kind", Json.str "Lemma")])])])]) with
        | .error m => m.startsWith "ec-import: subtype predicate of kind 'Fop'"
        | _ => false)

-- Without a realization of its bound the subtype is an abstract type, at its own
-- path, the way HOL's type definition gives one.
#guard (match decodeTy (registerThTypes ecPrelude [jZModSubtype])
            (jTyConstr "Top.ZModRing.zmod") with
        | .ok (.opaque "Top.ZModRing.zmod") => true
        | _ => false)

-- The abstract type is not the carrier: a statement decoded at the subtype is
-- not a statement about the integers.
#guard (match decodeTy (registerThTypes ecPrelude [jZModSubtype])
            (jTyConstr "Top.ZModRing.zmod") with
        | .ok t => t != EcTy.int
        | _ => false)

-- Which realization each declaration waits on is still what a caller
-- instantiating the theory reads off the item list, since a realization buys the
-- concrete range code that sampling needs.
#guard (subtypeBoundsNeeded ecPrelude ecRangePredPaths [jZModSubtype]
        == [("Top.ZModRing.zmod", "Top.ZModRing.p")])

-- At a realization of that operator the path decodes at the range below it.
#guard (match decodeTy
            (registerThTypesAt ecPrelude [jZModSubtype] ecRangePredPaths
              [("Top.ZModRing.p", 7)])
            (jTyConstr "Top.ZModRing.zmod") with
        | .ok (.intRange 0 7 _) => true
        | _ => false)

/-- The `Th_type` item of `crypto/DiffieHellman.ec`'s `Top.GP.ZModE.exp`, the
`subtype exp = {x : int | 0 <= x < order}` its `PowZMod` clone declares. The
bound is `Top.G.order`, which the same envelope defines as the size of the
group's enumeration, so its value is a function of the theory's parameters like
the modulus of `ZModRing` is. -/
private def jGPExpSubtype : Json :=
  Json.mkObj
    [("kind", Json.str "Th_type"), ("name", Json.str "exp"),
     ("path", Json.str "Top.GP.ZModE.exp"),
     ("decl", Json.mkObj
       [("params", Json.arr #[]),
        ("body", Json.mkObj [("kind", Json.str "Abstract")]),
        ("subtype", Json.mkObj
          [("carrier", jInt), ("pred", jSubPred "Top.G.order"),
           ("nonempty", Json.mkObj
             [("path", Json.str "Top.GP.ZModE.Sub.inhabited"),
              ("axiom_kind", Json.str "Lemma")])])])]

-- Two subtype declarations register independently, each at its own bound's
-- realization, and a bound the realization does not name leaves its declaration
-- at the abstract type.
#guard (match decodeTy
            (registerThTypesAt ecPrelude [jZModSubtype, jGPExpSubtype]
              ecRangePredPaths [("Top.G.order", 5)])
            (jTyConstr "Top.GP.ZModE.exp") with
        | .ok (.intRange 0 5 _) => true
        | _ => false)
#guard (match decodeTy
            (registerThTypesAt ecPrelude [jZModSubtype, jGPExpSubtype]
              ecRangePredPaths [("Top.G.order", 5)])
            (jTyConstr "Top.ZModRing.zmod") with
        | .ok (.opaque "Top.ZModRing.zmod") => true
        | _ => false)

-- A realization emptying the range is an error, not an abstract type: the
-- theory's own bound axiom is what rules that realization out.
#guard (match decodeTy
            (registerThTypesAt ecPrelude [jZModSubtype] ecRangePredPaths
              [("Top.ZModRing.p", 0)])
            (jTyConstr "Top.ZModRing.zmod") with
        | .error m => m.startsWith
            "ec-import: type path 'Top.ZModRing.zmod' names a subtype"
        | _ => false)

/-- The `Th_type` item of `algebra/Poly.ec`'s `Top.Poly.poly`, the
`subtype poly = {p : prepoly | ispoly p}` its `PolyComRing` clone declares. The
carrier `Top.Poly.prepoly` is the function type `int -> coeff`, and the predicate
is an operator of the theory. -/
private def jPolySubtype : Json :=
  Json.mkObj
    [("kind", Json.str "Th_type"), ("name", Json.str "poly"),
     ("path", Json.str "Top.Poly.poly"),
     ("decl", Json.mkObj
       [("params", Json.arr #[]),
        ("body", Json.mkObj [("kind", Json.str "Abstract")]),
        ("subtype", Json.mkObj
          [("carrier", jTyArrow jInt (jTyConstr "Top.Poly.coeff")),
           ("pred", Json.mkObj [("kind", Json.str "Fop"),
                                ("path", Json.str "Top.Poly.ispoly"),
                                ("targs", Json.arr #[])]),
           ("nonempty", Json.mkObj
             [("path", Json.str "Top.Poly.inhabited"),
              ("axiom_kind", Json.str "Lemma")])])])]

-- A subtype at a carrier with no code is registered as pending too, and a type
-- node at its path reports the carrier rather than an unread path.
#guard (match decodeTy (registerThTypes ecPrelude [jPolySubtype])
            (jTyConstr "Top.Poly.poly") with
        | .error m => m.startsWith
            "ec-import: type path 'Top.Poly.poly' names a subtype the ingestion \
             holds no code for: unsupported type node kind 'Tfun'"
        | _ => false)

-- No realization gives it a code: the bound of the recognised predicate is not
-- what it waits on.
#guard (subtypeBoundsNeeded ecPrelude ecRangePredPaths [jPolySubtype] == [])

-- A realization at which the range is empty has no code: the type would have no
-- value, and the theory's own bound axiom is what rules that realization out.
#guard (match decodeThTypeSubtype ecPrelude ecRangePredPaths jZModSubtype with
        | .ok d =>
          (match d.codeAt [("Top.ZModRing.p", 0)] with
           | .error m => m.startsWith
               "ec-import: subtype 'Top.ZModRing.zmod' at 'Top.ZModRing.p' = 0"
           | _ => false)
        | _ => false)

#guard (match decodeThTypeSubtype ecPrelude ecRangePredPaths jZModSubtype with
        | .ok d =>
          (match decodeTy (ecPrelude.withSubtype d (.fin 7)) (jTyConstr d.path) with
           | .ok (.fin 7 _) => true
           | _ => false)
        | _ => false)

-- A defined operator is rejected by its body kind: it abbreviates a term rather
-- than declaring a parameter, and registration skips it.
#guard (match decodeThOperatorAbstract ecPrelude
            (Json.mkObj [("kind", Json.str "Th_operator"), ("name", Json.str "c"),
                         ("path", Json.str "Top.c"),
                         ("decl", Json.mkObj
                           [("tparams", Json.arr #[]), ("ty", jBool),
                            ("body", Json.mkObj
                              [("kind", Json.str "OP_Plain")])])]) with
        | .error m => m.startsWith
            "ec-import: operator declaration 'Top.c' has body kind 'OP_Plain'"
        | _ => false)

/-! ### An inductive predicate

The item below is the exported shape of `distributions/Distr.ec`'s

```
inductive isdistr (m : 'a -> real) =
| Distr of (forall x, 0%r <= m x) & …
```

whose body the exporter writes as `PR_Ind`: the arguments the predicate is
defined over, and one constructor per introduction rule, each with its binders
and its premises. -/

/-- A `Th_operator` item at the exporter's shape for an inductive predicate, at
`Top.isdistr`'s arguments and its single `Distr` constructor. -/
private def jIndPred : Json :=
  Json.mkObj
    [("kind", Json.str "Th_operator"), ("name", Json.str "isdistr"),
     ("path", Json.str "Top.isdistr"),
     ("decl", Json.mkObj
       [("tparams", Json.arr #[Json.str "'a"]),
        ("ty", jTyArrow jBool jBool),
        ("body", Json.mkObj
          [("kind", Json.str "PR_Ind"),
           ("args", Json.arr
             #[Json.mkObj [("name", Json.str "m"), ("stamp", Json.num 74251),
                           ("ty", jTyArrow jBool jBool)]]),
           ("ctors", Json.arr
             #[Json.mkObj [("name", Json.str "Distr"),
                           ("binders", Json.arr #[]),
                           ("spec", Json.arr #[])]])])])]

-- An inductive predicate is rejected by what it is, ahead of the type parameters
-- it also binds.
#guard (match decodeThOperatorAbstract ecPrelude jIndPred with
        | .error m => m.startsWith
            "ec-import: operator declaration 'Top.isdistr' is an inductive \
             predicate"
        | _ => false)

/-! ### Datatype declarations

The items below are exported shapes of `crypto/PROM.ec`'s

```
type flag = [ Unknown | Known ].
```

and of `crypto/KeyEncapsulationMechanisms.eca`'s `malbind_scenario`, declared
inside the theory `MALBIND`, whose constructors are therefore at paths in that
theory's namespace. -/

/-- A constructor node taking no argument. -/
private def jCtor0 (name : String) : Json :=
  Json.mkObj [("name", Json.str name), ("args", Json.arr #[])]

/-- A `Th_type` item at the exporter's shape for a datatype declaration. -/
private def jDatatype (path : String) (ctors : Array Json) : Json :=
  Json.mkObj
    [("kind", Json.str "Th_type"), ("name", Json.str (lastComponent path)),
     ("path", Json.str path),
     ("decl", Json.mkObj
       [("params", Json.arr #[]),
        ("body", Json.mkObj
          [("kind", Json.str "Datatype"), ("ctors", Json.arr ctors)]),
        ("subtype", Json.null)])]

/-- `type flag = [ Unknown | Known ].` -/
private def jFlagDatatype : Json :=
  jDatatype "Top.flag" #[jCtor0 "Unknown", jCtor0 "Known"]

-- The declaration decodes as its path and its constructors' paths, which sit in
-- the declaring path's namespace.
#guard (match decodeThTypeEnum jFlagDatatype with
        | .ok d => d == { path := "Top.flag", ctors := ["Top.Unknown", "Top.Known"] }
        | _ => false)

-- A type node at the declared path decodes at the code of its cardinality.
#guard (match decodeTy (registerThTypes ecPrelude [jFlagDatatype])
            (jTyConstr "Top.flag") with
        | .ok (.fin 2 _) => true
        | _ => false)

-- and each constructor is a constant at the value of its position.
#guard (match List.lookup "Top.Unknown"
            (registerThTypes ecPrelude [jFlagDatatype]).constPaths with
        | some v => v.ty == EcTy.fin 2 && v.get (.fin 2) == (0 : Fin 2)
        | none => false)
#guard (match List.lookup "Top.Known"
            (registerThTypes ecPrelude [jFlagDatatype]).constPaths with
        | some v => v.ty == EcTy.fin 2 && v.get (.fin 2) == (1 : Fin 2)
        | none => false)

/-- `type malbind_scenario = [ DECAPS_DECAPS | ENCAPS_DECAPS | ENCAPS_ENCAPS ].`,
declared inside the theory `MALBIND`. -/
private def jScenarioDatatype : Json :=
  jDatatype "Top.MALBIND.malbind_scenario"
    #[jCtor0 "DECAPS_DECAPS", jCtor0 "ENCAPS_DECAPS", jCtor0 "ENCAPS_ENCAPS"]

-- A declaration inside a theory puts its constructors in that theory's
-- namespace.
#guard (match decodeThTypeEnum jScenarioDatatype with
        | .ok d =>
            d.ctors == ["Top.MALBIND.DECAPS_DECAPS", "Top.MALBIND.ENCAPS_DECAPS",
                        "Top.MALBIND.ENCAPS_ENCAPS"]
        | _ => false)
#guard (match decodeTy (registerThTypes ecPrelude [jScenarioDatatype])
            (jTyConstr "Top.MALBIND.malbind_scenario") with
        | .ok (.fin 3 _) => true
        | _ => false)

-- `type xint = [ N of int | Inf ].` is a sum, and is rejected by the constructor
-- that takes an argument rather than read at the constructors it has none for.
#guard (match decodeThTypeEnum
            (jDatatype "Top.xint"
              #[Json.mkObj [("name", Json.str "N"),
                            ("args", Json.arr #[jInt])],
                jCtor0 "Inf"]) with
        | .error m => m.startsWith
            "ec-import: datatype declaration 'Top.xint' has the constructor 'N' \
             at 1 argument(s)"
        | _ => false)

-- `type 'a list = [ \"[]\" | \"::\" of 'a & 'a list ].` binds a type parameter,
-- which no code has.
#guard (match decodeThTypeEnum
            (Json.mkObj
              [("kind", Json.str "Th_type"), ("name", Json.str "list"),
               ("path", Json.str "Top.list"),
               ("decl", Json.mkObj
                 [("params", Json.arr #[Json.str "'a"]),
                  ("body", Json.mkObj
                    [("kind", Json.str "Datatype"),
                     ("ctors", Json.arr #[jCtor0 "[]"])]),
                  ("subtype", Json.null)])]) with
        | .error m => m.startsWith
            "ec-import: datatype declaration 'Top.list' binds 1 type parameter(s)"
        | _ => false)

-- A declaration with no constructor denotes the empty type, which no code
-- interprets.
#guard (match decodeThTypeEnum (jDatatype "Top.void" #[]) with
        | .error m => m.startsWith
            "ec-import: datatype declaration 'Top.void' names no constructor"
        | _ => false)

/-! ### A cleared theory

The item below is the exported shape of `algebra/Bigop.eca`'s
`clear [Support Support.Axioms]`. -/

-- A clear item decodes as the paths it removes, and declares nothing else.
#guard (match decodeThClear
            (Json.mkObj
              [("kind", Json.str "Th_clear"),
               ("paths", Json.arr
                 #[Json.str "Top.Support", Json.str "Top.Support.Axioms"])]) with
        | .ok ps => ps == ["Top.Support", "Top.Support.Axioms"]
        | _ => false)

-- A clear item declares no type, so type registration passes over it.
#guard ((registerThTypes ecPrelude
          [Json.mkObj
            [("kind", Json.str "Th_clear"),
             ("paths", Json.arr #[Json.str "Top.Support"])]]).tyPaths.length
        == ecPrelude.tyPaths.length)

/-! ### Concrete operator declarations

The items below are exported shapes of `datatypes/Int.ec`'s

```
op b2i (b : bool) = if b then 1 else 0.
op max (a b : int) = if a < b then b else a.
```

`core/CoreInt.ec`'s

```
op zero : int = 0.
```

`algebra/Poly.ec`'s

```
op PolyComRing.([-]) = polyN.
```

and `algebra/Bigalg.ec`'s notation for `ZM.(-)`, transcribed from envelopes of
schema version 10. The first three are definitions of the accepted shape; the
fourth is eta-contracted, so what its lambda would bind is left in a
function-typed body, and the fifth is a notation rather than a definition. -/

/-- The type node of a bound variable at the type node `ty`, at the name and
stamp the export writes. -/
private def jOpBinder (name : String) (stamp : Nat) (ty : Json) : Json :=
  Json.mkObj [("name", Json.str name), ("stamp", Json.num stamp),
              ("gty", Json.mkObj [("kind", Json.str "GTty"), ("ty", ty)])]

/-- An integer literal in formula position. -/
private def jFInt (v : String) : Json :=
  Json.mkObj [("ty", jInt), ("kind", Json.str "Fint"), ("value", Json.str v)]

/-- The defining form of `b2i`: `fun (b : bool) => if b then 1 else 0`. -/
private def jB2iForm : Json :=
  Json.mkObj
    [("ty", jTyArrow jBool jInt), ("kind", Json.str "Fquant"),
     ("quant", Json.str "Llambda"),
     ("binders", Json.arr #[jOpBinder "b" 6258 jBool]),
     ("body", Json.mkObj
       [("ty", jInt), ("kind", Json.str "Fif"),
        ("cond", Json.mkObj
          [("ty", jBool), ("kind", Json.str "Flocal"), ("name", Json.str "b"),
           ("stamp", Json.num 6258)]),
        ("then", jFInt "1"), ("else", jFInt "0")])]

/-- The `Th_operator` item defining `b2i : bool -> int`. -/
private def jB2iOp : Json :=
  Json.mkObj
    [("kind", Json.str "Th_operator"), ("name", Json.str "b2i"),
     ("path", Json.str "Top.b2i"),
     ("decl", Json.mkObj
       [("tparams", Json.arr #[]), ("ty", jTyArrow jBool jInt),
        ("body", Json.mkObj
          [("kind", Json.str "OP_Plain"), ("form", jB2iForm)])])]

/-- An occurrence of the bound variable `name` at the stamp `stamp`, at the type
node `ty`. -/
private def jFLocal (name : String) (stamp : Nat) (ty : Json) : Json :=
  Json.mkObj [("ty", ty), ("kind", Json.str "Flocal"), ("name", Json.str name),
              ("stamp", Json.num stamp)]

/-- The `Th_operator` item defining `max (a b : int) = if a < b then b else a`,
the exported shape of `datatypes/Int.ec`'s `max`. -/
private def jMaxOp : Json :=
  let a := jFLocal "a" 6828 jInt
  let b := jFLocal "b" 6829 jInt
  let ltTy := jTyArrow jInt (jTyArrow jInt jBool)
  let form :=
    Json.mkObj
      [("ty", jTyArrow jInt (jTyArrow jInt jInt)), ("kind", Json.str "Fquant"),
       ("quant", Json.str "Llambda"),
       ("binders", Json.arr #[jOpBinder "a" 6828 jInt, jOpBinder "b" 6829 jInt]),
       ("body", Json.mkObj
         [("ty", jInt), ("kind", Json.str "Fif"),
          ("cond", Json.mkObj
            [("ty", jBool), ("kind", Json.str "Fapp"),
             ("f", Json.mkObj
               [("ty", ltTy), ("kind", Json.str "Fop"),
                ("path", Json.str "Top.CoreInt.lt"), ("targs", Json.arr #[])]),
             ("args", Json.arr #[a, b])]),
          ("then", b), ("else", a)])]
  Json.mkObj
    [("kind", Json.str "Th_operator"), ("name", Json.str "max"),
     ("path", Json.str "Top.max"),
     ("decl", Json.mkObj
       [("tparams", Json.arr #[]),
        ("ty", jTyArrow jInt (jTyArrow jInt jInt)),
        ("body", Json.mkObj
          [("kind", Json.str "OP_Plain"), ("form", form)])])]

/-- The `Th_operator` item defining the nullary `zero : int`. -/
private def jCoreIntZeroOp : Json :=
  Json.mkObj
    [("kind", Json.str "Th_operator"), ("name", Json.str "zero"),
     ("path", Json.str "Top.zero"),
     ("decl", Json.mkObj
       [("tparams", Json.arr #[]), ("ty", jInt),
        ("body", Json.mkObj
          [("kind", Json.str "OP_Plain"), ("form", jFInt "0")])])]

/-- The `Th_operator` item defining `PolyComRing.([-])` as `polyN`, whose
defining form is the operator it abbreviates rather than a lambda. -/
private def jPolyNegOp : Json :=
  let poly := jTyConstr "Top.Poly.poly"
  Json.mkObj
    [("kind", Json.str "Th_operator"), ("name", Json.str "[-]"),
     ("path", Json.str "Top.Poly.PolyComRing.[-]"),
     ("decl", Json.mkObj
       [("tparams", Json.arr #[]), ("ty", jTyArrow poly poly),
        ("body", Json.mkObj
          [("kind", Json.str "OP_Plain"),
           ("form", Json.mkObj
             [("ty", jTyArrow poly poly), ("kind", Json.str "Fop"),
              ("path", Json.str "Top.Poly.polyN"),
              ("targs", Json.arr #[])])])])]

/-- The `Th_operator` item of `algebra/Bigalg.ec`'s notation `ZM.(-)`, whose body
is the exporter's `OB_nott` node. The body node carries the notation's arguments
and result type, which the decoder does not read: it rejects the declaration by
the body kind. -/
private def jZMSubNotation : Json :=
  let t := jTyConstr "Top.BigZModule.ZM.t"
  Json.mkObj
    [("kind", Json.str "Th_operator"), ("name", Json.str "-"),
     ("path", Json.str "Top.BigZModule.ZM.-"),
     ("decl", Json.mkObj
       [("tparams", Json.arr #[]), ("ty", jTyArrow t (jTyArrow t t)),
        ("body", Json.mkObj [("kind", Json.str "OB_nott")])])]

-- A definition of one argument decodes to its parameter, at the code its
-- declared type gives that argument, its result code, and the body its lambda
-- wraps.
#guard (match decodeThOperatorConcrete ecPrelude jB2iOp with
        | .ok d =>
            d.path == "Top.b2i"
              && d.params == [({ name := "b", stamp := some 6258 }, EcTy.bool)]
              && d.res == EcTy.int
              && (getStr d.body "kind" == .ok "Fif")
        | _ => false)

-- A definition of two arguments carries its parameters in source order: the
-- first binder is at the first domain of the declared type.
#guard (match decodeThOperatorConcrete ecPrelude jMaxOp with
        | .ok d =>
            d.path == "Top.max"
              && d.params == [({ name := "a", stamp := some 6828 }, EcTy.int),
                              ({ name := "b", stamp := some 6829 }, EcTy.int)]
              && d.res == EcTy.int
              && (getStr d.body "kind" == .ok "Fif")
        | _ => false)

-- A definition of no argument is its form, at the code its declared type is.
#guard (match decodeThOperatorConcrete ecPrelude jCoreIntZeroOp with
        | .ok d =>
            d.path == "Top.zero" && d.params == [] && d.res == EcTy.int
              && (getStr d.body "kind" == .ok "Fint")
              && (getStr d.body "value" == .ok "0")
        | _ => false)

-- Both register under their paths, through the same walk the abstract
-- declarations take, and the abstract table stays empty.
#guard (registerThOperators ecPrelude [jB2iOp, jCoreIntZeroOp]).defOpPaths.map
    Prod.fst == ["Top.zero", "Top.b2i"]

#guard (registerThOperators ecPrelude [jB2iOp, jCoreIntZeroOp]).absOpPaths == []

#guard (match List.lookup "Top.b2i"
            (registerThOperators ecPrelude [jB2iOp, jCoreIntZeroOp]).defOpPaths with
        | some d => d.params == [({ name := "b", stamp := some 6258 }, EcTy.bool)]
        | none => false)

-- An eta-contracted definition is rejected: its declared type takes an argument
-- its defining form does not bind, so the form is function-typed and has no
-- EcTy code.
#guard (match decodeThOperatorConcrete
            (ecPrelude.withOpaqueType "Top.Poly.poly") jPolyNegOp with
        | .error m => m.startsWith
            "ec-import: operator definition 'Top.Poly.PolyComRing.[-]' takes 1 \
             argument(s) and its defining form is a node of kind 'Fop'"
        | _ => false)

-- and it does not register, so a read of it reports the missing entry rather
-- than expanding to a term the decoder did not check.
#guard (registerThOperators (ecPrelude.withOpaqueType "Top.Poly.poly")
    [jPolyNegOp]).defOpPaths.isEmpty

/-- A `Th_operator` item defining a predicate over one type parameter, at the
shape `prelude/Logic.ec` declares `associative` in: `tparams` names the parameter
and the defining form is a lambda over the value parameter. -/
private def jPolyAssocOp : Json :=
  Json.mkObj
    [("kind", Json.str "Th_operator"), ("name", Json.str "assoc"),
     ("path", Json.str "Top.Logic.assoc"),
     ("decl", Json.mkObj
       [("tparams", Json.arr #[Json.str "'a"]),
        ("ty", Json.mkObj [("kind", Json.str "Tfun")]),
        ("body", Json.mkObj
          [("kind", Json.str "PR_Plain"),
           ("form", Json.mkObj [("kind", Json.str "Ftrue")])])])]

-- A definition over type parameters registers as written, since it has no codes
-- until a read site gives the parameters values.
#guard (match List.lookup "Top.Logic.assoc"
            (registerThOperators ecPrelude [jPolyAssocOp]).polyOpPaths with
        | some d => d.tyParams == ["'a"]
        | none => false)

-- It is not a definition the other two tables hold: those need codes.
#guard (registerThOperators ecPrelude [jPolyAssocOp]).defOpPaths.isEmpty
#guard (registerThOperators ecPrelude [jPolyAssocOp]).absOpPaths.isEmpty

-- A definition binding no type parameter is not one of these.
#guard (decodeThOperatorPoly ecPrelude jB2iOp).toOption.isNone

-- A notation is rejected by its body kind, before anything else the body carries
-- is read.
#guard (match decodeThOperatorConcrete ecPrelude jZMSubNotation with
        | .error m => m.startsWith
            "ec-import: operator declaration 'Top.BigZModule.ZM.-' has body kind \
             'OB_nott'"
        | _ => false)

-- A recursive declaration is rejected by its body kind for the same reason.
#guard (match decodeThOperatorConcrete ecPrelude
            (Json.mkObj
              [("kind", Json.str "Th_operator"), ("name", Json.str "is_int"),
               ("path", Json.str "Top.is_int"),
               ("decl", Json.mkObj
                 [("tparams", Json.arr #[]), ("ty", jTyArrow jInt jBool),
                  ("body", Json.mkObj [("kind", Json.str "OP_Fix")])])]) with
        | .error m => m.startsWith
            "ec-import: operator declaration 'Top.is_int' has body kind 'OP_Fix'"
        | _ => false)

-- An abstract declaration is not a definition, and the two decoders reject each
-- other's items by the same field.
#guard (match decodeThOperatorConcrete prfTyTables jPRFOpF with
        | .error m => m.startsWith
            "ec-import: operator declaration 'Top.PseudoRF.F' has body kind \
             'Abstract'"
        | _ => false)

#guard (match decodeThOperatorAbstract ecPrelude jB2iOp with
        | .error m => m.startsWith
            "ec-import: operator declaration 'Top.b2i' has body kind 'OP_Plain'"
        | _ => false)

-- A definition at a path the ingestion already gives a meaning is rejected: the
-- committed entry decides what the path denotes.
#guard (match decodeThOperatorConcrete ecPrelude
            (Json.mkObj
              [("kind", Json.str "Th_operator"), ("name", Json.str "add"),
               ("path", Json.str "Top.CoreInt.add"),
               ("decl", Json.mkObj
                 [("tparams", Json.arr #[]), ("ty", jTyArrow jBool jInt),
                  ("body", Json.mkObj
                    [("kind", Json.str "OP_Plain"), ("form", jB2iForm)])])]) with
        | .error m => m.startsWith
            "ec-import: operator definition 'Top.CoreInt.add' is at a path the \
             ingestion's opPaths already gives a meaning"
        | _ => false)

-- A definition whose form reads the operator it defines is rejected: expanding
-- a read of it would not terminate. No corpus definition has this shape — a
-- recursive EasyCrypt operator carries the exporter's OP_Fix body — and the item
-- below is built from `b2i` by making its condition a read of `b2i` itself.
#guard (match decodeThOperatorConcrete ecPrelude
            (Json.mkObj
              [("kind", Json.str "Th_operator"), ("name", Json.str "b2i"),
               ("path", Json.str "Top.b2i"),
               ("decl", Json.mkObj
                 [("tparams", Json.arr #[]), ("ty", jTyArrow jBool jInt),
                  ("body", Json.mkObj
                    [("kind", Json.str "OP_Plain"),
                     ("form", Json.mkObj
                       [("ty", jTyArrow jBool jInt), ("kind", Json.str "Fquant"),
                        ("quant", Json.str "Llambda"),
                        ("binders", Json.arr #[jOpBinder "b" 6258 jBool]),
                        ("body", Json.mkObj
                          [("ty", jInt), ("kind", Json.str "Fif"),
                           ("cond", Json.mkObj
                             [("ty", jBool), ("kind", Json.str "Fop"),
                              ("path", Json.str "Top.b2i"),
                              ("targs", Json.arr #[])]),
                           ("then", jFInt "1"), ("else", jFInt "0")])])])])]) with
        | .error m => m.startsWith
            "ec-import: operator definition 'Top.b2i' names its own path in its \
             defining form"
        | _ => false)

/-- A `Srnd` node sampling the local `x` of type `ty` from the distribution at
`distrPath`. -/
private def jSample (ty : Json) (distrPath : String) : Json :=
  Json.mkObj
    [("kind", Json.str "Srnd"),
     ("lv", Json.mkObj
       [("kind", Json.str "LvVar"), ("ty", ty),
        ("pv", Json.mkObj [("kind", Json.str "PVloc"), ("name", Json.str "x")])]),
     ("distr", Json.mkObj
       [("kind", Json.str "Eop"), ("path", Json.str distrPath),
        ("ty", Json.mkObj
          [("kind", Json.str "Tconstr"), ("path", Json.str "Top.Distr.distr"),
           ("args", Json.arr #[ty])])])]

-- The shape decodes at a finite code.
#guard (match decodeStmt ecPrelude (jSample jBool "Top.DBool.dbool") with
        | .ok (.sample .bool "x" _) => true
        | _ => false)

-- The same shape at a non-finite code is rejected: the sampler is uniform on
-- its carrier.
#guard (match decodeStmt ((ecPrelude.withIntType "Top.Int.int").withUniformDistr
              "Top.DInt.dint")
            (jSample (jTyConstr "Top.Int.int") "Top.DInt.dint") with
        | .error _ => true
        | _ => false)

/-! ### Distribution expressions

Each rejection below is paired with the shape that does decode, so no rejection
check passes because its input was malformed for an unrelated reason. -/

/-- The distribution type node `'a distr` over the carrier type node `ty`. -/
private def jDistrTy (ty : Json) : Json :=
  Json.mkObj [("kind", Json.str "Tconstr"),
              ("path", Json.str "Top.Distr.distr"), ("args", Json.arr #[ty])]

/-- A nullary distribution operator over the carrier type node `ty`. -/
private def jDistrOp (ty : Json) (p : String) : Json :=
  Json.mkObj [("kind", Json.str "Eop"), ("path", Json.str p),
              ("ty", jDistrTy ty), ("targs", Json.arr #[])]

/-- An application of the distribution operator `p` to `args`, at the carrier
type node `ty`. -/
private def jDistrApp (ty : Json) (p : String) (args : Array Json) : Json :=
  Json.mkObj
    [("kind", Json.str "Eapp"), ("ty", jDistrTy ty),
     ("f", Json.mkObj [("kind", Json.str "Eop"), ("path", Json.str p),
                       ("ty", jDistrTy ty), ("targs", Json.arr #[])]),
     ("args", Json.arr args)]

/-- A binder `x : ty`, as the exporter writes one. -/
private def jBinder (x : String) (ty : Json) : Json :=
  Json.mkObj [("name", Json.str x), ("stamp", Json.num 0), ("ty", ty)]

/-- A lambda over the binders `bs` with the body `body`. The lambda's own `ty`
field is a function type, which no decoder reads. -/
private def jLambda (bs : Array Json) (body : Json) : Json :=
  Json.mkObj
    [("kind", Json.str "Equant"), ("quant", Json.str "ELambda"),
     ("ty", Json.mkObj [("kind", Json.str "Tfun")]),
     ("binders", Json.arr bs), ("body", body)]

/-- A `bool`-typed local-variable read. -/
private def jLocalBool (x : String) : Json :=
  Json.mkObj [("ty", jBool), ("kind", Json.str "Evar"),
              ("pv", Json.mkObj [("kind", Json.str "PVloc"), ("name", Json.str x)])]

/-- A `bool`-typed read of the stamped identifier `x`, which is the node an
occurrence of a lambda binder is. -/
private def jElocalBool (x : String) (st : Nat) : Json :=
  Json.mkObj [("ty", jBool), ("kind", Json.str "Elocal"),
              ("name", Json.str x), ("stamp", Json.num st)]

/-- The negation of a `bool`-typed read of the node `e`. -/
private def jNotBool (e : Json) : Json :=
  Json.mkObj
    [("ty", jBool), ("kind", Json.str "Eapp"),
     ("f", Json.mkObj [("ty", jBool), ("kind", Json.str "Eop"),
                       ("path", Json.str "Top.Pervasive.[!]"),
                       ("targs", Json.arr #[])]),
     ("args", Json.arr #[e])]

/-- The negation of a `bool`-typed local-variable read. -/
private def jNotLocalBool (x : String) : Json := jNotBool (jLocalBool x)

/-- A `Srnd` node sampling the local `x` of type `ty` from the distribution node
`d`. -/
private def jSampleFrom (ty : Json) (d : Json) : Json :=
  Json.mkObj
    [("kind", Json.str "Srnd"),
     ("lv", Json.mkObj
       [("kind", Json.str "LvVar"), ("ty", ty),
        ("pv", Json.mkObj [("kind", Json.str "PVloc"), ("name", Json.str "x")])]),
     ("distr", d)]

-- `dunit y` decodes to a point mass at the variable read.
#guard (match decodeStmt ecPrelude
            (jSampleFrom jBool
              (jDistrApp jBool "Top.Distr.MUnit.dunit" #[jLocalBool "y"])) with
        | .ok (.sampleD .bool "x" (.point (.var .bool "y"))) => true
        | _ => false)

-- `dmap dbool (fun b => !b)` decodes to a pushforward of the uniform
-- distribution along the negation, at the binder's whole identity.
#guard (match decodeStmt ecPrelude
            (jSampleFrom jBool
              (jDistrApp jBool "Top.Distr.dmap"
                #[jDistrOp jBool "Top.DBool.dbool",
                  jLambda #[jBinder "b" jBool] (jNotBool (jElocalBool "b" 7))])) with
        | .ok (.sampleD .bool "x"
                 (.map (.uniform _ _) ⟨"b", some 0⟩
                   (.bnot (.var .bool ⟨"b", some 7⟩)))) => true
        | _ => false)

-- `dcond dbool (fun b => b)` decodes to the conditioning of the uniform
-- distribution on the predicate.
#guard (match decodeStmt ecPrelude
            (jSampleFrom jBool
              (jDistrApp jBool "Top.Distr.DConditional.dcond"
                #[jDistrOp jBool "Top.DBool.dbool",
                  jLambda #[jBinder "b" jBool] (jElocalBool "b" 0)])) with
        | .ok (.sampleD .bool "x"
                 (.cond (.uniform _ _) ⟨"b", some 0⟩ (.var .bool ⟨"b", some 0⟩))) => true
        | _ => false)

-- A read of the program variable `b` under a binder of the source name `b` keeps
-- the program variable's identity, which has no stamp. The `dcond` check above is
-- the same shape at a read of the binder.
#guard (match decodeStmt ecPrelude
            (jSampleFrom jBool
              (jDistrApp jBool "Top.Distr.DConditional.dcond"
                #[jDistrOp jBool "Top.DBool.dbool",
                  jLambda #[jBinder "b" jBool] (jLocalBool "b")])) with
        | .ok (.sampleD .bool "x"
                 (.cond (.uniform _ _) ⟨"b", some 0⟩ (.var .bool ⟨"b", none⟩))) => true
        | _ => false)

-- An identifier node without its uniqueness stamp is rejected, so a stamped
-- occurrence never decodes to the program variable of its name.
#guard (match decodeStmt ecPrelude
            (jSampleFrom jBool
              (jDistrApp jBool "Top.Distr.DConditional.dcond"
                #[jDistrOp jBool "Top.DBool.dbool",
                  jLambda #[jBinder "b" jBool]
                    (Json.mkObj [("ty", jBool), ("kind", Json.str "Elocal"),
                                 ("name", Json.str "b")])])) with
        | .error _ => true
        | _ => false)

-- `dbool \ (fun b => !b)` decodes to the conditioning of the uniform
-- distribution on the negated predicate, which is `dexcepted`'s own definition.
#guard (match decodeStmt ecPrelude
            (jSampleFrom jBool
              (jDistrApp jBool "Top.Dexcepted.\\"
                #[jDistrOp jBool "Top.DBool.dbool",
                  jLambda #[jBinder "b" jBool] (jNotBool (jElocalBool "b" 0))])) with
        | .ok (.sampleD .bool "x"
                 (.cond (.uniform _ _) ⟨"b", some 0⟩
                   (.bnot (.bnot (.var .bool ⟨"b", some 0⟩))))) => true
        | _ => false)

-- `dscale dbool` decodes to the rescaling of the uniform distribution.
#guard (match decodeStmt ecPrelude
            (jSampleFrom jBool
              (jDistrApp jBool "Top.Distr.dscale"
                #[jDistrOp jBool "Top.DBool.dbool"])) with
        | .ok (.sampleD .bool "x" (.scale (.uniform _ _))) => true
        | _ => false)

-- `drestrict dbool (fun b => b)` decodes to the restriction of the uniform
-- distribution to the predicate.
#guard (match decodeStmt ecPrelude
            (jSampleFrom jBool
              (jDistrApp jBool "Top.Distr.drestrict"
                #[jDistrOp jBool "Top.DBool.dbool",
                  jLambda #[jBinder "b" jBool] (jElocalBool "b" 0)])) with
        | .ok (.sampleD .bool "x"
                 (.restrict (.uniform _ _) ⟨"b", some 0⟩ (.var .bool ⟨"b", some 0⟩))) =>
          true
        | _ => false)

-- `dlet dbool (fun b => dbool)` decodes to the bind, whose second argument is a
-- distribution under the binder.
#guard (match decodeStmt ecPrelude
            (jSampleFrom jBool
              (jDistrApp jBool "Top.Distr.dlet"
                #[jDistrOp jBool "Top.DBool.dbool",
                  jLambda #[jBinder "b" jBool]
                    (jDistrOp jBool "Top.DBool.dbool")])) with
        | .ok (.sampleD .bool "x"
                 (.letD (.uniform _ _) ⟨"b", some 0⟩ (.uniform _ _))) => true
        | _ => false)

-- `dbool `*` dbool` decodes to the independent product at the two component
-- codes the pair carrier names.
#guard (match decodeStmt ecPrelude
            (jSampleFrom (jTyProd jBool jBool)
              (jDistrApp (jTyProd jBool jBool) "Top.Distr.`*`"
                #[jDistrOp jBool "Top.DBool.dbool",
                  jDistrOp jBool "Top.DBool.dbool"])) with
        | .ok (.sampleD (.prod .bool .bool) "x"
                 (.prod (.uniform _ _) (.uniform _ _))) => true
        | _ => false)

-- A distribution operator outside the ingestion's table is rejected by path.
-- `dnull` is the rejected nullary operator; `dbool`, checked above at the same
-- shape, is the accepted one.
#guard (match decodeStmt ecPrelude
            (jSampleFrom jBool (jDistrOp jBool "Top.Distr.dnull")) with
        | .error _ => true
        | _ => false)

-- `dbiased` is the rejected one-argument operator; `dscale`, checked above at the
-- same shape, is the accepted one.
#guard (match decodeStmt ecPrelude
            (jSampleFrom jBool
              (jDistrApp jBool "Top.DBool.dbiased"
                #[jDistrOp jBool "Top.DBool.dbool"])) with
        | .error _ => true
        | _ => false)

-- `dlist` is the rejected two-argument operator; `dlet`, checked above at the
-- same shape, is the accepted one.
#guard (match decodeStmt ecPrelude
            (jSampleFrom jBool
              (jDistrApp jBool "Top.DList.dlist"
                #[jDistrOp jBool "Top.DBool.dbool",
                  jLambda #[jBinder "b" jBool]
                    (jDistrOp jBool "Top.DBool.dbool")])) with
        | .error _ => true
        | _ => false)

-- `dfold` is the rejected three-argument operator.
#guard (match decodeStmt ecPrelude
            (jSampleFrom jBool
              (jDistrApp jBool "Top.Distr.dfold"
                #[jDistrOp jBool "Top.DBool.dbool",
                  jDistrOp jBool "Top.DBool.dbool",
                  jDistrOp jBool "Top.DBool.dbool"])) with
        | .error _ => true
        | _ => false)

-- The independent product at a carrier that is not a pair code is rejected: the
-- product's two factors have no codes to decode at. The pair-carrier check above
-- is the accepted shape.
#guard (match decodeStmt ecPrelude
            (jSampleFrom jBool
              (jDistrApp jBool "Top.Distr.`*`"
                #[jDistrOp jBool "Top.DBool.dbool",
                  jDistrOp jBool "Top.DBool.dbool"])) with
        | .error _ => true
        | _ => false)

-- A bind whose second argument is not a lambda is rejected; the `dlet` check
-- above is the accepted shape.
#guard (match decodeStmt ecPrelude
            (jSampleFrom jBool
              (jDistrApp jBool "Top.Distr.dlet"
                #[jDistrOp jBool "Top.DBool.dbool",
                  jDistrOp jBool "Top.DBool.dbool"])) with
        | .error _ => true
        | _ => false)

-- A function argument of two binders is rejected; the one-binder lambda of the
-- `dcond` check above is what decodes.
#guard (match decodeStmt ecPrelude
            (jSampleFrom jBool
              (jDistrApp jBool "Top.Distr.DConditional.dcond"
                #[jDistrOp jBool "Top.DBool.dbool",
                  jLambda #[jBinder "b" jBool, jBinder "c" jBool]
                    (jElocalBool "b" 0)])) with
        | .error _ => true
        | _ => false)

-- A function argument that is not a lambda is rejected, so a predicate given by
-- an operator does not decode to some predicate the AST can express.
#guard (match decodeStmt ecPrelude
            (jSampleFrom jBool
              (jDistrApp jBool "Top.Distr.DConditional.dcond"
                #[jDistrOp jBool "Top.DBool.dbool",
                  Json.mkObj [("ty", jBool), ("kind", Json.str "Eop"),
                              ("path", Json.str "Top.Pervasive.idfun"),
                              ("targs", Json.arr #[])]])) with
        | .error _ => true
        | _ => false)

-- A predicate whose binder is at another code than the distribution's carrier is
-- rejected.
#guard (match decodeStmt (ecPrelude.withFinType "Top.W.word" 3 "Top.W.+")
            (jSampleFrom jBool
              (jDistrApp jBool "Top.Distr.DConditional.dcond"
                #[jDistrOp jBool "Top.DBool.dbool",
                  jLambda #[jBinder "b" jWord] (jLocalBool "b")])) with
        | .error _ => true
        | _ => false)

-- Conditioning at a non-finite carrier is rejected, because the uniform
-- distribution under it has no image there; the same shape at `bool` decodes
-- above.
#guard (match decodeStmt ((ecPrelude.withIntType "Top.Int.int").withUniformDistr
              "Top.DInt.dint")
            (jSampleFrom (jTyConstr "Top.Int.int")
              (jDistrApp (jTyConstr "Top.Int.int") "Top.Dexcepted.\\"
                #[jDistrOp (jTyConstr "Top.Int.int") "Top.DInt.dint",
                  jLambda #[jBinder "n" (jTyConstr "Top.Int.int")]
                    (jLocalBool "b")])) with
        | .error _ => true
        | _ => false)

-- A distribution operator registered by the ingestion under another path
-- decodes, which is what `withDistrOp` is for.
#guard (match decodeStmt (ecPrelude.withDistrOp "Top.MyDistr.point" .dunit)
            (jSampleFrom jBool
              (jDistrApp jBool "Top.MyDistr.point" #[jLocalBool "y"])) with
        | .ok (.sampleD .bool "x" (.point (.var .bool "y"))) => true
        | _ => false)

/-! ### The exporter's own distribution nodes

`nonunif.expected.json` is the export of a source declaring one module per
distribution operator of the fragment. The checks below decode each of them, so
the shapes the hand-built nodes above exercise are the shapes EasyCrypt's own
exporter writes. -/

/-- The exporter's output for the distribution-operator theory, as text. -/
private def nonunifExportText : String := include_str "nonunif.expected.json"

/-- The exporter's output for the distribution-operator theory. -/
private def nonunifExport : Json :=
  match Json.parse nonunifExportText with
  | .ok j => j
  | .error _ => Json.null

-- The fixture parses.
#guard (match nonunifExport with | Json.obj _ => true | _ => false)

-- `x <$ dbool` imports as the uniform sampling arm, unchanged.
#guard (match importGame ecPrelude "Uniform" nonunifExport with
        | .ok { name := "Uniform", locals := ["x"], procs := [],
                body := [.sample .bool "x"], ret := .var .bool "x" } => true
        | _ => false)

-- `x <$ dunit true` imports as a sample from the point mass at `true`.
#guard (match importGame ecPrelude "Pointed" nonunifExport with
        | .ok { name := "Pointed", locals := ["x"], procs := [],
                body := [.sampleD .bool "x" (.point (.lit true))],
                ret := .var .bool "x" } => true
        | _ => false)

-- `x <$ dmap dbool (fun b => !b)` imports as a sample from the pushforward of the
-- uniform distribution along the negation. The binder's stamp is EasyCrypt's own
-- counter, so the check pins that the binder carries one and that the occurrence
-- in the body is the binder rather than the identifier's source name.
#guard (match importGame ecPrelude "Mapped" nonunifExport with
        | .ok { name := "Mapped", locals := ["x"], procs := [],
                body := [.sampleD .bool "x"
                           (.map (.uniform _ _) b (.bnot (.var .bool y)))],
                ret := .var .bool "x" } => b.stamp.isSome && b == y
        | _ => false)

-- `x <$ dcond dbool (fun b => b)` imports as a sample from the uniform
-- distribution conditioned on the predicate.
#guard (match importGame ecPrelude "Conditioned" nonunifExport with
        | .ok { name := "Conditioned", locals := ["x"], procs := [],
                body := [.sampleD .bool "x"
                           (.cond (.uniform _ _) b (.var .bool y))],
                ret := .var .bool "x" } => b.stamp.isSome && b == y
        | _ => false)

-- `x <$ dbool \ (fun b => !b)` imports as a sample from the uniform distribution
-- conditioned on the negated predicate.
#guard (match importGame ecPrelude "Excepted" nonunifExport with
        | .ok { name := "Excepted", locals := ["x"], procs := [],
                body := [.sampleD .bool "x"
                           (.cond (.uniform _ _) b
                             (.bnot (.bnot (.var .bool y))))],
                ret := .var .bool "x" } => b.stamp.isSome && b == y
        | _ => false)

/-! ### Integers

`ints.expected.json` is the export of a source declaring a game whose locals,
one global and return expression are integer-valued, a game whose return
expression compares under the strict order, and a module whose `main` returns an
integer. -/

/-- The exporter's output for the integer theory, as text. -/
private def intsExportText : String := include_str "ints.expected.json"

/-- The exporter's output for the integer theory. -/
private def intsExport : Json :=
  match Json.parse intsExportText with
  | .ok j => j
  | .error _ => Json.null

-- The fixture parses.
#guard (match intsExport with | Json.obj _ => true | _ => false)

-- The integer literals, the addition, the global at an `int` code and the
-- comparison all decode, at the qualified name the exporter gives the global.
#guard (match importGame ecPrelude "Ints" intsExport with
        | .ok { name := "Ints", locals := ["a", "b"], procs := [],
                body := [.assign .int "a" zero,
                         .assign .int "a" (.intAdd (.var .int "a") one),
                         .store g stored,
                         .load g' "b"],
                ret := .intLe (.var .int "b") bound } =>
          litIsInt zero 0 && litIsInt one 1 && litIsInt bound 1
            && stored.varName == some (EcVarId.ofName "a")
            && g.name == "Top.Ints./total" && g.ty == .int
            && g'.name == "Top.Ints./total" && g'.ty == .int
        | _ => false)

-- The strict order has no `EcExpr` constructor and decodes as the negation of
-- the reversed `≤`.
#guard (match importGame ecPrelude "Strict" intsExport with
        | .ok { name := "Strict", locals := ["a"], procs := [],
                body := [.assign .int "a" two],
                ret := .bnot (.intLe three (.var .int "a")) } =>
          litIsInt two 2 && litIsInt three 3
        | _ => false)

-- A procedure returning an integer is not a game, and the module it belongs to
-- declares it at that result code.
#guard (match importGame ecPrelude "Counter" intsExport with
        | .error _ => true
        | _ => false)

#guard (match importModule ecPrelude "Counter" intsExport with
        | .ok M => M.interface.sig "main" == { arg := .unit, res := .int }
        | _ => false)

/-! ### Finite maps

`maps.expected.json` is the export of a source declaring a game that builds a
map, tests membership, reads a key both with `oget` and with an explicit
default, and writes the map to a global; and a second game that reads that
global back. -/

/-- The exporter's output for the finite-map theory, as text. -/
private def mapsExportText : String := include_str "maps.expected.json"

/-- The exporter's output for the finite-map theory. -/
private def mapsExport : Json :=
  match Json.parse mapsExportText with
  | .ok j => j
  | .error _ => Json.null

-- The fixture parses.
#guard (match mapsExport with | Json.obj _ => true | _ => false)

-- `empty`, `m.[k] <- v`, `k \in m`, `oget m.[k]` and `odflt d m.[k]` each decode,
-- the last two to the same constructor at different defaults: `oget` reads the
-- canonical inhabitant of `bool`, and `odflt true` reads the source's default.
#guard (match importGame ecPrelude "Log" mapsExport with
        | .ok { name := "Log", locals := ["m", "seen", "v", "w"], procs := [],
                body := [.assign (.map .int .bool) "m" empty,
                         .assign (.map .int .bool) "m"
                           (.mapSet (.var (.map .int .bool) "m") k₁ tru),
                         .assign .bool "seen"
                           (.mapMem (.var (.map .int .bool) "m") k₂),
                         .assign .bool "v"
                           (.mapGetD (.var (.map .int .bool) "m") k₃ dOget),
                         .assign .bool "w"
                           (.mapGetD (.var (.map .int .bool) "m") k₄ dOdflt),
                         .store g stored],
                ret := .band (.var .bool "seen")
                         (.band (.var .bool "v") (.var .bool "w")) } =>
          litIsEmptyMap empty && litIsInt k₁ 1 && litIsBool tru true
            && litIsInt k₂ 1 && litIsInt k₃ 1 && litIsInt k₄ 2
            && litIsBool dOget false && litIsBool dOdflt true
            && stored.varName == some (EcVarId.ofName "m")
            && g.name == "Top.Log./log" && g.ty == .map .int .bool
        | _ => false)

-- A global at a map code is read back by `EcStmt.load`.
#guard (match importGame ecPrelude "Reload" mapsExport with
        | .ok { name := "Reload", locals := ["m"], procs := [],
                body := [.load g "m"],
                ret := .mapMem (.var (.map .int .bool) "m") k } =>
          litIsInt k 1 && g.name == "Top.Reload./cache"
            && g.ty == .map .int .bool
        | _ => false)

/-- The type node of a finite map from `int` to `bool`. -/
private def jMapIntBool : Json := jTyApp "Top.FMap.fmap" jInt jBool

/-- A map-typed local-variable read. -/
private def jLocalMap (x : String) : Json :=
  Json.mkObj [("ty", jMapIntBool), ("kind", Json.str "Evar"),
              ("pv", Json.mkObj [("kind", Json.str "PVloc"), ("name", Json.str x)])]

/-- The option type node over `bool`, which has no `EcTy` code. -/
private def jOptBool : Json :=
  Json.mkObj [("kind", Json.str "Tconstr"),
              ("path", Json.str "Top.Logic.option"), ("args", Json.arr #[jBool])]

/-- The lookup `m.[1]`, whose own type is an option. -/
private def jMapLookup : Json :=
  Json.mkObj
    [("ty", jOptBool), ("kind", Json.str "Eapp"),
     ("f", Json.mkObj [("ty", jOptBool), ("kind", Json.str "Eop"),
                       ("path", Json.str "Top.FMap._.[_]"),
                       ("targs", Json.arr #[jInt, jBool])]),
     ("args", Json.arr #[jLocalMap "m", jIntLit "1"])]

/-- An application of the operator `p` to `args`, at the type node `ty`. -/
private def jOpApp (ty : Json) (p : String) (args : Array Json) : Json :=
  Json.mkObj
    [("ty", ty), ("kind", Json.str "Eapp"),
     ("f", Json.mkObj [("ty", ty), ("kind", Json.str "Eop"),
                       ("path", Json.str p), ("targs", Json.arr #[jBool])]),
     ("args", Json.arr args)]

-- Under `oget` the lookup decodes, at the canonical inhabitant of `bool`.
#guard (match decodeExpr ecPrelude .bool
            (jOpApp jBool "Top.Logic.oget" #[jMapLookup]) with
        | .ok (.mapGetD (.var (.map .int .bool) "m") k d) =>
          litIsInt k 1 && litIsBool d false
        | _ => false)

-- The lookup on its own is rejected: its result is an option, and `EcTy` has no
-- option code.
#guard (match decodeExpr ecPrelude .bool jMapLookup with
        | .error _ => true
        | _ => false)

-- `oget` of anything other than a lookup is rejected.
#guard (match decodeExpr ecPrelude .bool
            (jOpApp jBool "Top.Logic.oget" #[jLocalBool "b"]) with
        | .error _ => true
        | _ => false)

-- The empty map decodes at a map code.
#guard (match decodeExpr ecPrelude (.map .int .bool)
            (Json.mkObj [("ty", jMapIntBool), ("kind", Json.str "Eop"),
                         ("path", Json.str "Top.FMap.empty"),
                         ("targs", Json.arr #[jInt, jBool])]) with
        | .ok e => litIsEmptyMap e
        | _ => false)

-- and is rejected at any other code, rather than coerced.
#guard (match decodeExpr ecPrelude .bool
            (Json.mkObj [("ty", jBool), ("kind", Json.str "Eop"),
                         ("path", Json.str "Top.FMap.empty"),
                         ("targs", Json.arr #[jInt, jBool])]) with
        | .error _ => true
        | _ => false)

/-! ### Bounded loops

`loops.expected.json` is the export of a source declaring two modules at the
recognised `while` idiom and eight that differ from it in one respect each. Every
rejection below is paired with the two shapes that do decode, so no rejection
check passes because its input was malformed for an unrelated reason. -/

/-- The exporter's output for the loop theory, as text. -/
private def loopsExportText : String := include_str "loops.expected.json"

/-- The exporter's output for the loop theory. -/
private def loopsExport : Json :=
  match Json.parse loopsExportText with
  | .ok j => j
  | .error _ => Json.null

-- The fixture parses.
#guard (match loopsExport with | Json.obj _ => true | _ => false)

-- `i <- 0; while (i < 3) { i <- i + 1; }` decodes to the initialisation followed
-- by three iterations of the body, the increment among them.
#guard (match importGame ecPrelude "Bounded" loopsExport with
        | .ok { name := "Bounded", locals := ["i"], procs := [],
                body := [.assign .int "i" zero,
                         .forN 3 [.assign .int "i" (.intAdd (.var .int "i") one)]],
                ret := .intLe (.var .int "i") bound } =>
          litIsInt zero 0 && litIsInt one 1 && litIsInt bound 3
        | _ => false)

-- A body that writes another variable, under a conditional, keeps its shape
-- inside the loop.
#guard (match importGame ecPrelude "Nested" loopsExport with
        | .ok { name := "Nested", locals := ["i", "acc"], procs := [],
                body := [.assign .bool "acc" fls,
                         .assign .int "i" zero,
                         .forN 2
                           [.ite (.var .bool "acc")
                              [.assign .bool "acc" fls']
                              [.assign .bool "acc" tru],
                            .assign .int "i" (.intAdd (.var .int "i") one)]],
                ret := .var .bool "acc" } =>
          litIsBool fls false && litIsBool fls' false && litIsBool tru true
            && litIsInt zero 0 && litIsInt one 1
        | _ => false)

-- A guard whose bound is a program variable is rejected: the iteration count is
-- not determined.
#guard (match importGame ecPrelude "VarBound" loopsExport with
        | .error _ => true
        | _ => false)

-- A loop whose preceding statement is not an integer assignment is rejected.
#guard (match importGame ecPrelude "NoInit" loopsExport with
        | .error _ => true
        | _ => false)

-- A loop whose preceding statement initialises another variable is rejected.
#guard (match importGame ecPrelude "WrongInit" loopsExport with
        | .error _ => true
        | _ => false)

-- A loop that opens its block is rejected: nothing precedes it.
#guard (match importGame ecPrelude "LoopFirst" loopsExport with
        | .error _ => true
        | _ => false)

-- A body whose last statement does not increment the counter is rejected.
#guard (match importGame ecPrelude "NoIncr" loopsExport with
        | .error _ => true
        | _ => false)

-- A body that writes the counter somewhere other than its last statement is
-- rejected.
#guard (match importGame ecPrelude "ExtraWrite" loopsExport with
        | .error _ => true
        | _ => false)

-- A guard under `<=` is rejected: `i <= n` runs one iteration more than `i < n`,
-- and the recognised guard is the strict one.
#guard (match importGame ecPrelude "LeGuard" loopsExport with
        | .error _ => true
        | _ => false)

-- A body containing an argument-free call is rejected: the call site names
-- neither the procedure table nor the body, so the body's writes are not
-- determined and the counter may be among them.
#guard (match importGame ecPrelude "CallInBody" loopsExport with
        | .error _ => true
        | _ => false)

/-- The signature node of a procedure: the formal list, the tupled domain and
the result type. -/
private def jSigDef (args : Array Json) (argty ret : Json) : Json :=
  Json.mkObj [("args", Json.arr args), ("argty", argty), ("ret", ret)]

/-- A formal-parameter entry, at the exporter's `{name, ty}` shape. -/
private def jFormal (nm : Json) (ty : Json) : Json :=
  Json.mkObj [("name", nm), ("ty", ty)]

-- A two-formal signature decodes to the pair domain and both binder names —
-- the shape of `f` in the exporter's `multiarg` golden.
#guard (match decodeSigDef ecPrelude
            (jSigDef #[jFormal (Json.str "x") jInt, jFormal (Json.str "y") jBool]
              (jTyProd jInt jBool) jInt) with
        | .ok (s, ns) => s == { arg := .prod .int .bool, res := .int }
            && ns == ["x", "y"]
        | _ => false)

-- A three-formal signature decodes at the right-nested domain.
#guard (match decodeSigDef ecPrelude
            (jSigDef #[jFormal (Json.str "x") jInt, jFormal (Json.str "y") jBool,
                       jFormal (Json.str "z") jInt]
              (Json.mkObj [("kind", Json.str "Ttuple"),
                           ("args", Json.arr #[jInt, jBool, jInt])]) jInt) with
        | .ok (s, ns) => s == { arg := .prod .int (.prod .bool .int), res := .int }
            && ns == ["x", "y", "z"]
        | _ => false)

-- An anonymous formal binds under its positional name.
#guard (match decodeSigDef ecPrelude
            (jSigDef #[jFormal Json.null jInt] jInt jInt) with
        | .ok (s, ns) => s == { arg := .int, res := .int }
            && ns == [anonymousParam 0]
        | _ => false)

-- A signature whose argty disagrees with its formals is rejected.
#guard (match decodeSigDef ecPrelude
            (jSigDef #[jFormal (Json.str "x") jInt, jFormal (Json.str "y") jBool]
              jInt jInt) with
        | .error m => m.startsWith "ec-import: the signature's argty"
        | _ => false)

-- A three-argument call site decodes at the right-nested pair domain, the
-- nesting the callee's signature carries.
#guard (match decodeCallArgs ecPrelude .int
            #[jIntLit "1", jLocalBool "b", jIntLit "2"] with
        | .ok ⟨s, _⟩ => s == { arg := .prod .int (.prod .bool .int), res := .int }
        | _ => false)

/-! ### Alias procedure bodies

The nodes below are the exporter's own, taken from the `crypto/assumptions`
and `encryption` envelopes: `IdealHash.init = RealHash.init` (a procedure of
another envelope module), `L.orcl = Ob.orclL` (a procedure of the enclosing
functor's parameter), `AEAD_OraclesCondProb.enc = AEAD_Oracles.enc` (three
formals), and `Bound.init = SetLog.Log(O).init` (a procedure of an applied
functor). -/

/-- The variables a tuple of variable reads is built from, in order. The type
index is quantified for the reason `EcExpr.litValue` gives. -/
private def varsOfTuple : {t : EcTy} → EcExpr t → Option (List EcVarId)
  | _, .var _ x => some [x]
  | _, .pair a b =>
    match varsOfTuple a, varsOfTuple b with
    | some xs, some ys => some (xs ++ ys)
    | _, _ => none
  | _, _ => none

/-- The `unit` type node EasyCrypt's prelude writes. -/
private def jUnit : Json := jTyConstr "Top.Pervasive.unit"

/-- A procedure node at the name `nm`, the signature node `sig` and the body
node `body`. -/
private def jProc (nm : String) (sig body : Json) : Json :=
  Json.mkObj [("name", Json.str nm), ("sig", sig), ("def", body)]

/-- An `FBalias` procedure body naming the cross-path `target`. -/
private def jFBalias (target : String) : Json :=
  Json.mkObj [("kind", Json.str "FBalias"), ("target", Json.str target)]

-- An alias to a procedure of another envelope module decodes as one forwarding
-- call at the alias's own signature, returning the call's result.
#guard (match decodeProc
            (ecPrelude.withProcSig "Top.RealHash./init"
              { arg := .unit, res := .unit })
            (jProc "init" (jSigDef #[] jUnit jUnit)
              (jFBalias "Top.RealHash./init")) with
        | .ok d =>
          d.locals == [] &&
          (match d.sp.proc.body with
           | [.callProc q s _ x] =>
             q == "Top.RealHash./init" && s == { arg := .unit, res := .unit }
               && x == aliasResultLocal
           | _ => false)
            && d.sp.proc.ret.varName == some (EcVarId.ofName aliasResultLocal)
        | _ => false)

/-- The tables the parameter-alias check reads: the two abstract types the
`Hybrid` envelope's oracle signature is written at, and the parameter `Ob` at
the module type it is declared at. -/
private def obParamTables : DecodeTables :=
  ((ecPrelude.withOpaqueType "Top.input").withOpaqueType "Top.output").withInterfaceX
    "Ob" (interfaceOfSigs
      [("orclL", { arg := .opaque "Top.input", res := .opaque "Top.output" }),
       ("orclR", { arg := .opaque "Top.input", res := .opaque "Top.output" })])

-- An alias to a procedure of the enclosing functor's parameter decodes: the
-- parameter's procedures register at the same cross-paths the target is
-- written at, and the one formal forwards.
#guard (match decodeProc obParamTables
            (jProc "orcl"
              (jSigDef #[jFormal (Json.str "m") (jTyConstr "Top.input")]
                (jTyConstr "Top.input") (jTyConstr "Top.output"))
              (jFBalias "Ob./orclL")) with
        | .ok d =>
          d.sp.proc.params == ["m"] &&
          (match d.sp.proc.body with
           | [.callProc q _ arg _] =>
             q == "Ob./orclL"
               && varsOfTuple arg == some [EcVarId.ofName "m"]
           | _ => false)
        | _ => false)

/-- The signature node of the three-formal `enc` oracle the `AEAD` envelope
declares. -/
private def jEncSig : Json :=
  jSigDef #[jFormal (Json.str "kid") jInt, jFormal (Json.str "m") (jTyConstr "Top.Msg"),
            jFormal (Json.str "a") (jTyConstr "Top.AData")]
    (Json.mkObj [("kind", Json.str "Ttuple"),
                 ("args", Json.arr #[jInt, jTyConstr "Top.Msg", jTyConstr "Top.AData"])])
    (jTyApp1 "Top.Logic.option" (jTyConstr "Top.Cph"))

/-- The tables the three-formal alias check reads: the three abstract types of
the `AEAD` envelope's oracle signature, and the target's signature. -/
private def aeadTables : DecodeTables :=
  (((ecPrelude.withOpaqueType "Top.Msg").withOpaqueType "Top.AData").withOpaqueType
    "Top.Cph").withProcSig "Top.AEAD_Oracles./enc"
      { arg := .prod .int (.prod (.opaque "Top.Msg") (.opaque "Top.AData"))
        res := .option (.opaque "Top.Cph") }

-- The forwarded argument of a three-formal alias is the formals in declaration
-- order, tupled at the right-nested domain the callee's signature carries.
#guard (match decodeProc aeadTables
            (jProc "enc" jEncSig (jFBalias "Top.AEAD_Oracles./enc")) with
        | .ok d =>
          (match d.sp.proc.body with
           | [.callProc q _ arg _] =>
             q == "Top.AEAD_Oracles./enc"
               && varsOfTuple arg
                   == some (["kid", "m", "a"].map EcVarId.ofName)
           | _ => false)
        | _ => false)

-- An alias to a procedure of an applied functor is rejected, naming the
-- application.
#guard (match decodeProc ecPrelude
            (jProc "init" (jSigDef #[] jUnit jUnit)
              (jFBalias "Top.SetLog.Log(O)./init")) with
        | .error m =>
          m.startsWith "ec-import: procedure 'init' is an alias of \
            'Top.SetLog.Log(O)./init', a procedure of the applied functor"
        | _ => false)

-- An alias to a procedure of the module the alias sits in is rejected, even
-- when that module's procedures are in the table.
#guard (match decodeProc
            { ecPrelude.withProcSig "Top.M./g" { arg := .unit, res := .unit } with
              modPath := "Top.M" }
            (jProc "f" (jSigDef #[] jUnit jUnit) (jFBalias "Top.M./g")) with
        | .error m =>
          m.startsWith "ec-import: procedure 'f' is an alias of 'Top.M./g', a \
            procedure of the module the alias sits in"
        | _ => false)

-- An alias to a cross-path outside the table is rejected rather than resolved.
#guard (match decodeProc ecPrelude
            (jProc "init" (jSigDef #[] jUnit jUnit)
              (jFBalias "Top.RealHash./init")) with
        | .error m =>
          m.startsWith "ec-import: procedure 'init' is an alias of \
            'Top.RealHash./init', whose signature is not in the ingestion's \
            signature table"
        | _ => false)

-- An alias whose target resolves at another signature is rejected: the two
-- name different procedures.
#guard (match decodeProc
            (ecPrelude.withProcSig "Top.RealHash./init"
              { arg := .unit, res := .bool })
            (jProc "init" (jSigDef #[] jUnit jUnit)
              (jFBalias "Top.RealHash./init")) with
        | .error m =>
          m.startsWith "ec-import: procedure 'init' is an alias of \
            'Top.RealHash./init', which resolves at the signature"
        | _ => false)

-- A body of any other kind is still rejected by kind.
#guard (match decodeProc ecPrelude
            (jProc "f" (jSigDef #[] jUnit jUnit)
              (Json.mkObj [("kind", Json.str "FBabs")])) with
        | .error m =>
          m.startsWith "ec-import: procedure 'f' has body kind 'FBabs'"
        | _ => false)

/-- The type node of a finite set of booleans. -/
private def jFsetBool : Json := jTyApp1 "Top.FSet.fset" jBool

/-- A local-variable read at the type node `ty`. -/
private def jLocalAt (ty : Json) (x : String) : Json :=
  Json.mkObj [("ty", ty), ("kind", Json.str "Evar"),
              ("pv", Json.mkObj [("kind", Json.str "PVloc"), ("name", Json.str x)])]

/-- The empty finite set, as the nullary `fset0` operator at the type node
`ty`. -/
private def jFset0 (ty : Json) : Json :=
  Json.mkObj [("ty", ty), ("kind", Json.str "Eop"),
              ("path", Json.str "Top.FSet.fset0"), ("targs", Json.arr #[])]

-- The empty finite set decodes as the empty-set literal at the fset code.
#guard (match decodeExpr ecPrelude (.fset .bool) (jFset0 jFsetBool) with
        | .ok e =>
          (match e.litValue with
           | some s => s == EcTy.fsetEmpty (a := .bool)
           | none => false)
        | _ => false)

-- and is rejected at a code that is not a finite set.
#guard (match decodeExpr ecPrelude .bool (jFset0 jBool) with
        | .error _ => true
        | _ => false)

-- `fset1` decodes as the singleton at the fset code.
#guard (match decodeExpr ecPrelude (.fset .bool)
            (jOpApp jFsetBool "Top.FSet.fset1" #[jLocalBool "x"]) with
        | .ok (.fsetSingle e) => e.varName == some "x"
        | _ => false)

-- `` `|` `` decodes as the union of its two set arguments.
#guard (match decodeExpr ecPrelude (.fset .bool)
            (jOpApp jFsetBool "Top.FSet.`|`"
              #[jOpApp jFsetBool "Top.FSet.fset1" #[jLocalBool "x"],
                jFset0 jFsetBool]) with
        | .ok (.fsetUnion (.fsetSingle e) s) =>
          e.varName == some "x" && (match s.litValue with
            | some v => v == EcTy.fsetEmpty (a := .bool)
            | none => false)
        | _ => false)

-- `mem` reads its element code off the set argument's own type.
#guard (match decodeExpr ecPrelude .bool
            (jOpApp jBool "Top.FSet.mem"
              #[jLocalAt jFsetBool "s", jLocalBool "x"]) with
        | .ok (.fsetMem s e) =>
          s.varName == some (EcVarId.ofName "s")
            && e.varName == some (EcVarId.ofName "x")
        | _ => false)

-- Finiteness propagates through the set code: a set of booleans is a finite
-- code, a set of integers is not.
#guard (EcTy.fset .bool).isFin == true
#guard (EcTy.fset .int).isFin == false

/-- A tuple-lvalue component binding the local `x` at the type node `ty`. -/
private def jLvItem (x : String) (ty : Json) : Json :=
  Json.mkObj [("pv", Json.mkObj [("kind", Json.str "PVloc"),
                                 ("name", Json.str x)]),
              ("ty", ty)]

/-- A destructuring assignment `(…) <- rhs`, at the exporter's `Sasgn` shape
with an `LvTuple` lvalue. -/
private def jSasgnTuple (items : Array Json) (rhs : Json) : Json :=
  Json.mkObj [("kind", Json.str "Sasgn"),
              ("lv", Json.mkObj [("kind", Json.str "LvTuple"),
                                 ("items", Json.arr items)]),
              ("rhs", rhs)]

-- A two-component tuple lvalue decodes as the destructuring assignment at the
-- components' pair type.
#guard (match decodeItem ecPrelude
            (jSasgnTuple #[jLvItem "x" jInt, jLvItem "y" jBool]
              (jLocalAt (jTyProd jInt jBool) "p")) with
        | .ok (.stmt (.assignTuple (.prod .int .bool) ["x", "y"] e)) =>
          e.varName == some (EcVarId.ofName "p")
        | _ => false)

-- A three-component tuple lvalue decodes at the right-nested product.
#guard (match decodeItem ecPrelude
            (jSasgnTuple #[jLvItem "x" jInt, jLvItem "y" jBool, jLvItem "z" jInt]
              (jLocalAt (Json.mkObj [("kind", Json.str "Ttuple"),
                           ("args", Json.arr #[jInt, jBool, jInt])]) "p")) with
        | .ok (.stmt (.assignTuple (.prod .int (.prod .bool .int))
            ["x", "y", "z"] _)) => true
        | _ => false)

-- A tuple lvalue with a global component is rejected, naming the component.
#guard (match decodeItem ecPrelude
            (jSasgnTuple
              #[jLvItem "x" jInt,
                Json.mkObj [("pv", Json.mkObj [("kind", Json.str "PVglob"),
                              ("xpath", Json.str "Top.M./g")]),
                            ("ty", jBool)]]
              (jLocalAt (jTyProd jInt jBool) "p")) with
        | .error m =>
          m.startsWith "ec-import: tuple lvalue component of kind 'PVglob'"
        | _ => false)

-- The composed shape `(pk, sk) <@ S./kg()`: the call's result destructures at
-- the components' pair type.
#guard (match decodeItem ecPrelude
            (Json.mkObj [("kind", Json.str "Scall"), ("proc", Json.str "S./kg"),
                         ("args", Json.arr #[]),
                         ("lv", Json.mkObj [("kind", Json.str "LvTuple"),
                           ("items", Json.arr #[jLvItem "pk" jInt,
                                                jLvItem "sk" jBool])])]) with
        | .ok (.stmt (.callProcTuple "S./kg" s _ ["pk", "sk"])) =>
          s == { arg := .unit, res := .prod .int .bool }
        | _ => false)

-- A parameter interface registers its procedures at cross-paths.
#guard (match List.lookup "RO./init"
            ((ecPrelude.withInterfaceX "RO"
              (interfaceOfSigs [("init", { arg := .unit, res := .unit })])).procSigs) with
        | some s => s == { arg := .unit, res := .unit }
        | none => false)

-- A result-discarding call at a registered cross-path resolves its signature
-- from the table and binds the result to the anonymous local.
#guard (match decodeItem
            (ecPrelude.withProcSig "RO./init" { arg := .unit, res := .unit })
            (Json.mkObj [("kind", Json.str "Scall"),
                         ("proc", Json.str "RO./init"),
                         ("args", Json.arr #[]), ("lv", Json.null)]) with
        | .ok (.stmt (.callProc "RO./init" s _ x)) =>
          s == { arg := .unit, res := .unit } && x == anonymousLocal
        | _ => false)

-- and stays rejected at a cross-path outside the table.
#guard (match decodeItem ecPrelude
            (Json.mkObj [("kind", Json.str "Scall"),
                         ("proc", Json.str "RO./init"),
                         ("args", Json.arr #[]), ("lv", Json.null)]) with
        | .error m => m.startsWith "ec-import: call to 'RO./init' discards"
        | _ => false)

/-- The type node of a list of integers. -/
private def jListInt : Json := jTyApp1 "Top.List.list" jInt

/-- A nullary operator node at the path `p` and the type node `ty`. -/
private def jNullOp (p : String) (ty : Json) : Json :=
  Json.mkObj [("ty", ty), ("kind", Json.str "Eop"),
              ("path", Json.str p), ("targs", Json.arr #[])]

-- The empty list decodes as the empty-list literal at the list code,
#guard (match decodeExpr ecPrelude (.list .int)
            (jNullOp "Top.List.[]" jListInt) with
        | .ok e =>
          (match e.litValue with
           | some l => l == EcTy.listEmpty (a := .int)
           | none => false)
        | _ => false)

-- and is rejected at a code that is not a list.
#guard (match decodeExpr ecPrelude .int (jNullOp "Top.List.[]" jInt) with
        | .error _ => true
        | _ => false)

-- `None` decodes as the absent option value at the option code.
#guard (match decodeExpr ecPrelude (.option .bool)
            (jNullOp "Top.Logic.None" (jTyApp1 "Top.Logic.option" jBool)) with
        | .ok e =>
          (match e.litValue with
           | some v => v == EcTy.noneVal (a := .bool)
           | none => false)
        | _ => false)

-- `witness` decodes as the canonical inhabitant of the context's code.
#guard (match decodeExpr ecPrelude .int
            (jNullOp "Top.Pervasive.witness" jInt) with
        | .ok e => litIsInt e 0
        | _ => false)

-- `Some` decodes at the option code.
#guard (match decodeExpr ecPrelude (.option .bool)
            (jOpApp (jTyApp1 "Top.Logic.option" jBool) "Top.Logic.Some"
              #[jLocalBool "x"]) with
        | .ok (.someE e) => e.varName == some (EcVarId.ofName "x")
        | _ => false)

-- The list literal `1 :: []` decodes as cons of the literal onto the empty
-- list.
#guard (match decodeExpr ecPrelude (.list .int)
            (jOpApp jListInt "Top.List.::"
              #[jIntLit "1", jNullOp "Top.List.[]" jListInt]) with
        | .ok (.listCons e l) =>
          litIsInt e 1 && (match l.litValue with
            | some v => v == EcTy.listEmpty (a := .int)
            | none => false)
        | _ => false)

-- `rcons`, `size`, `mem` and `nth` decode over the list code.
#guard (match decodeExpr ecPrelude (.list .int)
            (jOpApp jListInt "Top.List.rcons"
              #[jLocalAt jListInt "l", jIntLit "2"]) with
        | .ok (.listRcons l e) =>
          l.varName == some (EcVarId.ofName "l") && litIsInt e 2
        | _ => false)
#guard (match decodeExpr ecPrelude .int
            (jOpApp jInt "Top.List.size" #[jLocalAt jListInt "l"]) with
        | .ok (.listSize l) => l.varName == some (EcVarId.ofName "l")
        | _ => false)
#guard (match decodeExpr ecPrelude .bool
            (jOpApp jBool "Top.List.mem"
              #[jLocalAt jListInt "l", jIntLit "3"]) with
        | .ok (.listMem l e) =>
          l.varName == some (EcVarId.ofName "l") && litIsInt e 3
        | _ => false)
#guard (match decodeExpr ecPrelude .int
            (jOpApp jInt "Top.List.nth"
              #[jIntLit "0", jLocalAt jListInt "l", jIntLit "1"]) with
        | .ok (.listNth d l i) =>
          litIsInt d 0 && l.varName == some (EcVarId.ofName "l") && litIsInt i 1
        | _ => false)

/-- The type node of a distribution over booleans. -/
private def jDistrBool : Json := jTyApp1 "Top.Distr.distr" jBool

-- The distribution type constructor decodes at the `distr` code, which is
-- outside `hasEq` and outside `isFin`.
#guard (match decodeTy ecPrelude jDistrBool with
        | .ok (.distr .bool) => true
        | _ => false)
#guard (EcTy.distr .bool).hasEq == false
#guard (EcTy.distr .bool).isFin == false

-- A type node at EasyCrypt's declaration of the type decodes at the same code
-- as one at the alias: the node below is `distributions/DBool.ec`'s spelling of
-- `bool distr`.
#guard (match decodeTy ecPrelude (jTyApp1 "Top.Pervasive.distr" jBool) with
        | .ok (.distr .bool) => true
        | _ => false)

-- A signature with a distribution-typed formal decodes: the oracle that
-- receives the distribution it samples from.
#guard (match decodeSigDef ecPrelude
            (jSigDef #[jFormal (Json.str "d") jDistrBool] jDistrBool jBool) with
        | .ok (s, ns) => s == { arg := .distr .bool, res := .bool } && ns == ["d"]
        | _ => false)

-- Equality at a distribution code is rejected: no decidable equality.
#guard (match decodeExpr ecPrelude .bool
            (jOpApp jBool "Top.Pervasive.="
              #[jLocalAt jDistrBool "d", jLocalAt jDistrBool "e"]) with
        | .error m => m.startsWith "ec-import: equality at the type"
        | _ => false)

-- The three codes whose operations compare values reject a key, element or
-- membership type without decidable equality, which is what makes the
-- comparing arms of `evalExpr` total on every decoded expression.
#guard (match decodeTy ecPrelude (jTyApp "Top.FMap.fmap" jDistrBool jBool) with
        | .error m =>
          m.startsWith "ec-import: finite-map type constructor 'Top.FMap.fmap' \
            at the key type"
        | _ => false)
#guard (match decodeTy ecPrelude (jTyApp1 "Top.FSet.fset" jDistrBool) with
        | .error m =>
          m.startsWith "ec-import: finite-set type constructor 'Top.FSet.fset' \
            at the element type"
        | _ => false)
#guard (match decodeExpr ecPrelude .bool
            (jOpApp jBool "Top.List.mem"
              #[jLocalAt (jTyApp1 "Top.List.list" jDistrBool) "l",
                jLocalAt jDistrBool "d"]) with
        | .error m => m.startsWith "ec-import: 'Top.List.mem' at the element type"
        | _ => false)

-- A distribution-valued finite map is still expressible: only the key type
-- needs comparing.
#guard (match decodeTy ecPrelude (jTyApp "Top.FMap.fmap" jInt jDistrBool) with
        | .ok (.map .int (.distr .bool)) => true
        | _ => false)

-- A module variable at a distribution code is rejected: the heap holds
-- countable values.
#guard (match decodeStructure ecPrelude 0
            (Json.mkObj
              [("kind", Json.str "Th_module"), ("name", Json.str "M"),
               ("path", Json.str "Top.M"),
               ("module", Json.mkObj
                 [("name", Json.str "M"), ("params", Json.arr #[]),
                  ("body", Json.mkObj
                    [("kind", Json.str "ME_Structure"),
                     ("modules", Json.arr #[]),
                     ("vars", Json.arr
                       #[Json.mkObj [("name", Json.str "dv"),
                                     ("ty", jDistrBool)]]),
                     ("procs", Json.arr #[])]),
                  ("sig", Json.arr #[])])]) with
        | .error m => m.startsWith "ec-import: module variable 'dv' at the type"
        | _ => false)

-- `x <$ d` from a distribution-typed local decodes as sampling from the
-- expression's value.
#guard (match decodeStmt ecPrelude
            (jSampleFrom jBool (jLocalAt jDistrBool "d")) with
        | .ok (.sampleD .bool "x" (.ofExpr e)) =>
          e.varName == some (EcVarId.ofName "d")
        | _ => false)

/-- Tables with two integer globals, for the hoisting checks. -/
private def hoistTables : DecodeTables :=
  (ecPrelude.withGlobal { name := "Top.M./g", id := 0, ty := .int }).withGlobal
    { name := "Top.M./h", id := 1, ty := .int }

/-- A global read at the type node `ty`, as the exporter writes one in
expression position. -/
private def jGlobReadAt (ty : Json) (q : String) : Json :=
  Json.mkObj [("ty", ty), ("kind", Json.str "Evar"),
              ("pv", Json.mkObj [("kind", Json.str "PVglob"),
                                 ("xpath", Json.str q)])]

/-- The assignment `x <- rhs` to a local at the type node `ty`. -/
private def jAssignLoc (x : String) (ty : Json) (rhs : Json) : Json :=
  Json.mkObj [("kind", Json.str "Sasgn"),
              ("lv", Json.mkObj [("kind", Json.str "LvVar"), ("ty", ty),
                ("pv", Json.mkObj [("kind", Json.str "PVloc"),
                                   ("name", Json.str x)])]),
              ("rhs", rhs)]

/-- The assignment `M.g <- rhs` to a global at the type node `ty`. -/
private def jAssignGlob (q : String) (ty : Json) (rhs : Json) : Json :=
  Json.mkObj [("kind", Json.str "Sasgn"),
              ("lv", Json.mkObj [("kind", Json.str "LvVar"), ("ty", ty),
                ("pv", Json.mkObj [("kind", Json.str "PVglob"),
                                   ("xpath", Json.str q)])]),
              ("rhs", rhs)]

-- One global read inside an expression hoists: a load into the hoisted local
-- precedes the assignment, whose expression reads the local.
#guard (match decodeStmts hoistTables
            [jAssignLoc "x" jInt
              (jOpApp jInt "Top.CoreInt.add"
                #[jGlobReadAt jInt "Top.M./g", jIntLit "1"])] with
        | .ok [.load g y, .assign .int "x" e] =>
          g.name == "Top.M./g" && y == hoistedGlobal "Top.M./g"
            && (match e with
                | .intAdd (.var .int v) e1 =>
                  v == EcVarId.ofName (hoistedGlobal "Top.M./g") && litIsInt e1 1
                | _ => false)
        | _ => false)

-- Two distinct globals load in first-occurrence order,
#guard (match decodeStmts hoistTables
            [jAssignLoc "x" jInt (jOpApp jInt "Top.CoreInt.add"
              #[jGlobReadAt jInt "Top.M./g", jGlobReadAt jInt "Top.M./h"])] with
        | .ok [.load g1 _, .load g2 _, .assign .int "x" _] =>
          g1.name == "Top.M./g" && g2.name == "Top.M./h"
        | _ => false)

-- and the flipped expression flips the load order: the order is determined by
-- the expression, not by the table.
#guard (match decodeStmts hoistTables
            [jAssignLoc "x" jInt (jOpApp jInt "Top.CoreInt.add"
              #[jGlobReadAt jInt "Top.M./h", jGlobReadAt jInt "Top.M./g"])] with
        | .ok [.load g1 _, .load g2 _, .assign .int "x" _] =>
          g1.name == "Top.M./h" && g2.name == "Top.M./g"
        | _ => false)

-- The same global read twice loads once.
#guard (match decodeStmts hoistTables
            [jAssignLoc "x" jInt (jOpApp jInt "Top.CoreInt.add"
              #[jGlobReadAt jInt "Top.M./g", jGlobReadAt jInt "Top.M./g"])] with
        | .ok [.load _ _, .assign .int "x" _] => true
        | _ => false)

-- The counter idiom `M.g <- M.g + 1`: the load takes the pre-write snapshot
-- and the store writes the incremented value.
#guard (match decodeStmts hoistTables
            [jAssignGlob "Top.M./g" jInt (jOpApp jInt "Top.CoreInt.add"
              #[jGlobReadAt jInt "Top.M./g", jIntLit "1"])] with
        | .ok [.load g1 _, .store g2 _] =>
          g1.name == "Top.M./g" && g2.name == "Top.M./g"
        | _ => false)

-- A whole-expression global read stays the plain load it always was: the
-- hoisting fires only inside a compound expression.
#guard (match decodeStmts hoistTables
            [jAssignLoc "x" jInt (jGlobReadAt jInt "Top.M./g")] with
        | .ok [.load g "x"] => g.name == "Top.M./g"
        | _ => false)

end Golden

end CatCrypt.Crypto.EasyCryptImport

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
| `Ttuple []` / `Ttuple [a, b]` | `EcTy.unit` / `EcTy.prod` |
| `Evar` at `PVloc`, `Elocal` | `EcExpr.var` |
| `Eint` at a `fin` code or at `int` | `EcExpr.lit` |
| `Eop p`, `p` in `constPaths` | `EcExpr.lit` |
| `Eop p`, `p` in `emptyMapPaths`, at a `map` code | `EcExpr.lit []` |
| `Eapp` of `bnot`/`band`/`bxor`/`beq`/`finAdd` | the matching `EcExpr` node |
| `Eapp` of `bor`/`bimp` | the de Morgan image over `bnot`/`band` |
| `Eapp` of integer `+` / `≤` | `EcExpr.intAdd` / `.intLe` |
| `Eapp` of integer `<` | `EcExpr.bnot` of the reversed `.intLe` |
| `Eapp` of `_.[_<-_]` / `dom` | `EcExpr.mapSet` / `.mapMem` |
| `Eapp` of `oget` / `odflt` to `_.[_]` | `EcExpr.mapGetD`, at the value type's canonical inhabitant / at the given default |
| `Etuple [a, b]`, `Eproj` at index 0 / 1 | `EcExpr.pair`, `EcExpr.fst` / `.snd` |
| `Sasgn` to `PVloc` | `EcStmt.assign` |
| `Sasgn` to `PVloc` of an `Evar` at `PVglob` | `EcStmt.load` |
| `Sasgn` to `PVglob` | `EcStmt.store` |
| `Srnd` from a declared-uniform nullary operator | `EcStmt.sample` |
| `Srnd` from `dunit` / `dmap` / `dcond` / `(\)` / `dlet` / `` `*` `` / `dscale` / `drestrict` | `EcStmt.sampleD` at the matching `EcDistr` |
| `Equant` of one `ELambda` binder, as a distribution operator's function argument | the binder and body of `EcDistr.map` / `.cond` / `.letD` / `.restrict` |
| `Sif` | `EcStmt.ite` |
| `Swhile` of the bounded idiom, after its initialisation | `EcStmt.forN` |
| `Scall` without an lvalue, to the enclosing module | `EcStmt.call` |
| `Scall` with an lvalue | `EcStmt.callProc` |
| procedure with an `FBdef` body | `EcProcAt` |
| `Th_module` of `ME_Structure` without parameters | `EcModule`, and `EcGame` through `decodeGame` |
| `Th_module` of `ME_Structure` with one parameter | `EcFunctor` through `decodeFunctor` |
| `Th_module` of `ME_Structure` with any number of parameters | `EcFunctorN` through `decodeFunctorN` (`FunctorN.lean`) |
| a module type's `sig`, without parameters | `EcInterface` through `decodeModSig` |

Boolean literals arrive as nullary operators (`Eop` at `Top.Pervasive.true`), and
application is curried with an argument list, so an operator's arity is checked
against the list length. Operator, type-constructor and distribution paths are
dispatch keys held by the ingestion, in `DecodeTables`: `ecPrelude` holds the
paths of EasyCrypt's boolean, unit and integer prelude, of its finite maps, and
of the distribution operators of the fragment, and
`DecodeTables.withFinType` / `.withIntType` / `.withMapType` / `.withEmptyMap` /
`.withUniformDistr` / `.withDistrOp` / `.withGlobal` extend it. A path outside the
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
* The finite-map lookup `m.[k]` on its own: it returns an option, and `EcTy` has
  no option code, so it decodes only under `oget` or `odflt`.
* A module whose body is an `ME_Alias` — one defined as an application of another
  module — rejected by body kind: the alias names the applied module by path and
  no body sits behind it.
* An identifier exported as a name with a uniqueness stamp: dropping the stamp
  makes two distinct binders of the same source name alias, so the object form
  of an identifier is rejected rather than truncated, and a stamped identifier
  node without a `stamp` field is a decode error rather than a program variable
  of that name.
* A call whose result is discarded and whose target is outside the enclosing
  module: the schema carries no result type at such a call site, so the
  signature `EcStmt.callProc` needs cannot be reconstructed.
* The distribution operators outside `distrOpPaths` — `dnull`, `dbiased`,
  `dbin`, `duniform` over a list, `dlist`, `dfun`, `dopt`, `dfold`, `dinter` —
  each rejected by path.
* `Eif`, `Elet`, `Ematch`, `Smatch`, `Sraise`, `Sabstract`, `LvTuple`,
  `FBalias`, `FBabs`, `Tfun`, nested modules, module parameters, tuples of arity
  above two, and procedure definitions with more than one formal parameter: each
  is rejected with a message naming the construct. `Equant` is rejected in
  expression position, and decodes only as a distribution operator's one-binder
  function argument.
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
def schemaVersion : Nat := 5

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

/-- The ingestion's dispatch tables: the EasyCrypt paths this decoder
recognises, and the module context it decodes in. Every lookup that misses is a
decode error. -/
structure DecodeTables where
  /-- Nullary type constructors and the `EcTy` code each denotes. -/
  tyPaths : List (String × EcTy)
  /-- Binary type constructors that denote the finite map at their two type
  arguments. -/
  mapTyPaths : List String
  /-- Nullary operators that denote a literal. -/
  constPaths : List (String × EcVal)
  /-- Nullary operators that denote the empty finite map. -/
  emptyMapPaths : List String
  /-- Operators of the accepted fragment. -/
  opPaths : List (String × EcOpKind)
  /-- Nullary operators that denote the uniform distribution on their carrier. -/
  distrPaths : List String
  /-- Distribution operators of the accepted fragment. -/
  distrOpPaths : List (String × EcDistrOpKind)
  /-- Type constructors of distributions, `'a distr`. -/
  distrTyPaths : List String
  /-- Module-scoped globals, keyed by the qualified name the exporter uses. -/
  globals : List (String × EcGlobal)
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
  constPaths :=
    [("Top.Pervasive.true", ⟨.bool, true⟩),
     ("Top.Pervasive.false", ⟨.bool, false⟩),
     ("Top.Pervasive.tt", ⟨.unit, ()⟩)]
  emptyMapPaths := ["Top.FMap.empty"]
  opPaths :=
    [("Top.Pervasive.[!]", .bnot),
     ("Top.Pervasive./\\", .band),
     ("Top.Pervasive.\\/", .bor),
     ("Top.Pervasive.=>", .bimp),
     ("Top.Logic.^", .bxor),
     ("Top.Pervasive.=", .beq),
     ("Top.CoreInt.add", .intAdd),
     ("Top.CoreInt.le", .intLe),
     ("Top.CoreInt.lt", .intLt),
     ("Top.FMap._.[_<-_]", .mapSet),
     ("Top.FMap._.[_]", .mapLookup),
     ("Top.FMap.dom", .mapMem),
     ("Top.Logic.oget", .mapOget),
     ("Top.Logic.odflt", .mapOdflt)]
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
  distrTyPaths := ["Top.Distr.distr"]
  globals := []
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

/-- Extend the tables with a finite-map type constructor at the type path
`tyPath`. An EasyCrypt `fmap` is a binary type constructor, and its two type
arguments are the key and value codes `decodeTy` reads off the node. -/
def DecodeTables.withMapType (T : DecodeTables) (tyPath : String) : DecodeTables :=
  { T with mapTyPaths := tyPath :: T.mapTyPaths }

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
            fail s!"unknown type path '{p}': the ingestion's type table has no \
              entry, so the type has no EcTy code"
        else if T.mapTyPaths.contains p then
          match args.toList.attach with
          | [⟨kJ, _⟩, ⟨vJ, _⟩] =>
            match decodeTy T kJ with
            | .error e => .error e
            | .ok k =>
              match decodeTy T vJ with
              | .error e => .error e
              | .ok v => .ok (.map k v)
          | _ =>
            fail s!"finite-map type constructor '{p}' applied to {args.size} \
              arguments, expected 2"
        else
          fail s!"parameterised type constructor '{p}': EcTy's only parameterised \
            code is the finite map, and the ingestion's map-type table has no \
            entry for the path"
  | .ok "Ttuple" =>
    match _harr : getArr j "args" with
    | .error e => .error e
    | .ok arr =>
      match arr.toList.attach.mapM (fun ⟨a, _⟩ => decodeTy T a) with
      | .error e => .error e
      | .ok ts =>
        match ts with
        | [] => .ok .unit
        | [a, b] => .ok (.prod a b)
        | _ =>
          fail s!"tuple type of arity {ts.length}: EcTy has unit and binary \
            products only"
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
    fail s!"tuple lvalue in {j.compress}: every EcStmt assignment writes a \
      single variable"
  | k => fail s!"unsupported lvalue kind '{k}' in {j.compress}"

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

/-- Decode a call's argument at the signature the call site determines, together
with that signature. Arguments are tupled up to arity two. -/
def decodeCallArgs (T : DecodeTables) (res : EcTy) (arr : Array Json) :
    Except String ((s : EcSig) × EcExpr s.arg) := do
  match arr.toList with
  | [] => .ok ⟨{ arg := .unit, res := res }, .lit ()⟩
  | [a] =>
    let u ← decodeTyField T a "ty"
    let ae ← decodeExpr T u a
    .ok ⟨{ arg := u, res := res }, ae⟩
  | [a, b] =>
    let u ← decodeTyField T a "ty"
    let v ← decodeTyField T b "ty"
    let ae ← decodeExpr T u a
    let be ← decodeExpr T v b
    .ok ⟨{ arg := .prod u v, res := res }, .pair ae be⟩
  | _ =>
    fail s!"call with {arr.size} arguments: EcSig has one argument type, and \
      arguments are tupled up to arity two"

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
  /-- A while loop of the recognised shape: the counter, the bound the guard
  compares it with, and the body, whose last statement increments the counter. -/
  | loop (counter : String) (bound : Int) (body : List EcStmt)

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
  | .stmt s :: rest =>
    match resolveLoops rest with
    | .error e => .error e
    | .ok rest' => .ok (s :: rest')
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
              match decodeExpr T t rhsJ with
              | .error e => .error e
              | .ok e => .ok (.stmt (.assign t x e))
          | .glob g =>
            match decodeExpr T g.ty rhsJ with
            | .error e => .error e
            | .ok e => .ok (.stmt (.store g e))
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
      match decodeExpr T .bool condJ with
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
                  | .ok els => .ok (.stmt (.ite c thn els))
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
        match getObj j "lv" with
        | .error e => .error e
        | .ok Json.null =>
          if argsA.isEmpty && T.modPath ≠ "" && q.startsWith T.modPath then
            .ok (.stmt (.call (lastComponent q)))
          else
            fail s!"call to '{q}' discards its result in {j.compress}: the \
              schema carries no result type at the call site, so only an \
              argument-free call to the enclosing module '{T.modPath}' has an \
              image, as EcStmt.call"
        | .ok lvJ =>
          match decodeLv T lvJ with
          | .error e => .error e
          | .ok (.glob g) =>
            fail s!"call result assigned to the global '{g.name}': \
              EcStmt.callProc writes a local variable"
          | .ok (.loc x t) =>
            match decodeCallArgs T t argsA with
            | .error e => .error e
            | .ok ⟨s, arg⟩ => .ok (.stmt (.callProc q s arg x))
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

/-- The name a call binds a discarded result to, and the formal parameter name of
a procedure that takes none. EasyCrypt has no variable of this name, so the
binding cannot capture a source variable. -/
def anonymousLocal : String := "_"

/-- The signature and body an undeclared procedure name is sent to. A name
outside a module's interface is undeclared, and the module's meaning does not
depend on either. -/
def undeclaredProc : SigProc :=
  { sig := { arg := .unit, res := .unit }
    proc := { param := anonymousLocal, body := [], ret := .lit () } }

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

/-- Decode a procedure signature and the name of its formal parameter. The
argument type is the signature's `argty`, which is EasyCrypt's tupled argument
type; `args` names the formal parameters. -/
def decodeSigDef (T : DecodeTables) (j : Json) : Except String (EcSig × String) := do
  let arg ← decodeTyField T j "argty"
  let res ← decodeTyField T j "ret"
  let args ← getArr j "args"
  match args.toList with
  | [] => .ok ({ arg := arg, res := res }, anonymousLocal)
  | [a] =>
    let nm ← match a.getObjVal? "name" with
      | .ok Json.null => .ok anonymousLocal
      | .ok _ => getIdent a "name"
      | .error _ => fail s!"formal parameter without a name field in {a.compress}"
    .ok ({ arg := arg, res := res }, nm)
  | _ =>
    fail s!"procedure of {args.size} formal parameters: EcProcAt binds a single \
      parameter name, and the schema does not say how a tupled argument \
      destructures into them"

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

/-- Decode a procedure. -/
def decodeProc (T : DecodeTables) (j : Json) : Except String DecodedProc := do
  let name ← getStr j "name"
  let sigJ ← getObj j "sig"
  let (s, param) ← decodeSigDef T sigJ
  let defJ ← getObj j "def"
  let bk ← getStr defJ "kind"
  if bk ≠ "FBdef" then
    fail s!"procedure '{name}' has body kind '{bk}': only an FBdef body has an \
      EcProcAt image"
  else
    let localsA ← getArr defJ "locals"
    let locals ← localsA.toList.mapM (fun v => getIdent v "name")
    let bodyA ← getArr defJ "body"
    let body ← decodeStmts T bodyA.toList
    let retJ ← getObj defJ "ret"
    let ret ← decodeRet T s.res retJ
    .ok { name := name, locals := locals
          sp := { sig := s, proc := { param := param, body := body, ret := ret } } }

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
      fail s!"module '{name}' has {modsA.size} nested modules, which the AST \
        does not nest"
    else
      let varsA ← getArr bodyJ "vars"
      let gs ← (varsA.toList.zip (List.range varsA.size)).mapM
        (fun (v, i) => do
          let nm ← getIdent v "name"
          let t ← decodeTyField T v "ty"
          .ok ({ name := xqualify mpath nm, id := baseId + i, ty := t } : EcGlobal))
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

/-- Decode a module signature — the `sig` of a `Th_modtype` item, and the `sig`
of a module type wherever one occurs — as an interface: the procedure names it
declares and their signatures. A module type has no bodies, so this is the whole
of what a module of that type offers. A parameterised module signature is
rejected: its procedures' signatures depend on the parameter, which the interface
has no place for. -/
def decodeModSig (T : DecodeTables) (j : Json) : Except String EcInterface := do
  let params ← getArr j "params"
  if params.size ≠ 0 then
    fail s!"module signature of {params.size} parameter(s): EcInterface declares \
      the procedures of an unparameterised module type"
  else
    let procsA ← getArr j "procs"
    let decls ← procsA.toList.mapM (decodeSigDecl T)
    .ok (interfaceOfSigs decls)

/-- Decode the interface of a `Th_modtype` item. -/
def decodeModTypeInterface (T : DecodeTables) (j : Json) : Except String EcInterface := do
  let k ← getStr j "kind"
  if k ≠ "Th_modtype" then
    fail s!"item of kind '{k}' read as a module type"
  else
    let sigJ ← getObj j "sig"
    decodeModSig T sigJ

/-- Decode the interface a module type node requires of a module: the `sig` the
exporter resolves for it, with the node's own arguments already substituted in. -/
def decodeModTypeSig (T : DecodeTables) (j : Json) : Except String EcInterface := do
  let k ← getStr j "kind"
  if k ≠ "ModuleType" then
    fail s!"node of kind '{k}' read as a module type"
  else
    let sigJ ← getObj j "sig"
    decodeModSig T sigJ

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
      let S ← decodeStructureBody T baseId name mpath modJ
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
                | { param := _, body := [.callProc "Top.OTPArg./enc" _ _ "r"],
                    ret := _ } => true
                | _ => false)
        | _ => false)

-- The body of `enc` is the sample, then the conditional whose branches assign
-- `c` — the `Sif` image — and its formal parameter is the source name `m`.
#guard (match importModule ecPrelude "OTPArg" otpExport with
        | .ok M =>
          (match M.procs "enc" with
           | { param := "m",
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

end Golden

end CatCrypt.Crypto.EasyCryptImport

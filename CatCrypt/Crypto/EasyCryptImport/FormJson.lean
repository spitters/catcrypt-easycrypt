/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.EasyCryptImport.Json
import CatCrypt.Crypto.EasyCryptImport.Form

/-!
# EasyCrypt import: JSON ingestion of statements

`Json.lean` decodes the exporter's *programs*; this module decodes its
*statements*. The exporter serialises `EcCoreFol.form`, EasyCrypt's formula type,
and the functions here turn that serialisation into the `EcTerm`, `EcProb` and
`EcForm` values of `Form.lean`, so an imported lemma arrives as a statement
rather than as a rendered string.

The decoding discipline is the one `Json.lean` sets: every decoder is a `def`
recursing on the `jsonSize` measure, no field has a default, and a node the AST
cannot express is an `Except` error naming the construct rather than a value that
merely typechecks.

## Binders carry stamps

A formula binds logical variables, memories, probability parameters and modules,
and the exporter gives every binder an identifier with a uniqueness stamp.
`FormTables` maps stamps to what the AST needs: `locals` sends a logical
variable's stamp to its source name, and `mems` sends a memory's stamp to an
`EcMemRef`. A judgement node binds its own memories — `FequivF`'s two sides to
`EcSide.left` and `EcSide.right`, a unary judgement's and a probability event's
memory to `EcSide.cur` — so `res` and a global read at one of them decode to the
side the enclosing judgement gives them. An occurrence whose stamp is unbound is
an error, and binding a source name that another live stamp already carries is an
error too, because the AST names a variable by its source name and two binders
sharing one name would alias.

## An abstract operator is a parameter of the statement

A theory-level `op f : T.` without a definition is a parameter, not a value the
ingestion knows: `DecodeTables.absOpPaths` (`Json.lean`) holds the declarations of
the theory a statement comes from, and a read of one decodes to `EcTerm.opApp` at
the signature the declaration gives it. A declaration of `n` arguments is read at
a signature whose argument code is those arguments' codes as a right-nested
product, so an application of it decodes its arguments at their own codes and
nests them the same way (`EcTerm.nestArgs`); the count comes from the application
and the codes from the declaration, and an application the declared argument code
does not accept is rejected naming both codes. `decodeAxiom` produces the statement with
those reads free; closing it over them is `EcForm.assembleParams` (`Form.lean`),
which binds one `EcForm.allOp` per read operator and leaves `EcForm.opsOf` of the
result empty. A path in no table is an error, so a read cannot default to a value.

## A concrete operator definition is read where it is read

A theory-level `op f a b = e.` is a definition, not a parameter, and
`DecodeTables.defOpPaths` holds it. `decodeTerm` decodes a read of one as the
definition's body under one `EcTerm.letIn` per parameter, at the read site. The
body is not a sub-node of the application that reads it, so the recursion is
measured on the pair of the definitions still available and the node's size,
ordered lexicographically: the body is decoded against the tables with that
definition dropped, which is what makes the first component fall. An operator
therefore cannot be reached from inside its own definition, mutually or
otherwise, and the bound on a chain of reads is the length of the table rather
than a number anyone chose. Each parameter is bound under its source name and its
uniqueness stamp, so a definition's parameter can neither be refused for the name
of a binder live at the read site nor capture it; each argument is decoded at its
own type and compared with the code the declaration gives; and the body's decode
is reported as a failure of the operator, naming it.

Two body shapes have no image at the term layer: a quantified formula, which
`EcTerm` has no binder for, and an application of a definition written over type
parameters, whose path the term layer's operator tables do not carry. An
application of a definition at one of those bodies is decoded by `decodeForm`
instead, at the same discipline — the arguments are terms, the parameters are
bound at the read site, the body is decoded against the tables with that
definition dropped — with `EcForm.letF` in place of `EcTerm.letIn`. `defBodyIsForm`
is the syntactic test that picks the route, and it holds of those two shapes
only, so a definition the term layer reads is still read there.

## A definition over type parameters expands at the read site

A theory-level `op f ['a] x = e.` has no codes until a read site gives its type
parameters values, and `DecodeTables.polyOpPaths` holds the declaration as the
exporter wrote it. `decodeForm` decodes an application of one as the definition's
body: the type arguments the node carries are decoded and entered as the codes of
the type parameters (`DecodeTables.tyVarCodes`), and the value arguments replace
the parameters in the body syntactically, since the argument at a function-typed
parameter may be a lambda, which has no term image. The expansion is the formula
decoder's because these bodies are quantified — `associative f` is
`forall x y z, f x (f y z) = f (f x y) z`. The formula decoder expands
definitions of both kinds, so its recursion is measured on the definitions of
each still available together with the node's size, ordered lexicographically.

## A type parameter is read at a reserved type path

A statement written `lemma l ['a] : φ` declares type parameters, and a type
position of `φ` naming one carries a `Tvar` node. `EcTy` is a closed universe of
codes, so a type variable names no code. What it gets is a reserved type path,
`#tyvar.` before its source name: `substTyParams` rewrites its occurrences to the
nullary type constructor at that path, and `FormTables.withTyParam` enters the
path in the ingestion's type table at the code the parameter is read at, so a
`Tvar` resolves the way every other type does. Occurrences resolve by name, since
the export writes a type parameter as a bare name while a `Tvar` node carries a
name and a stamp; a name carrying two stamps in one statement, or an occurrence of
a name the statement does not declare, is rejected.

`decodeAxiomAt` takes the codes explicitly. `decodeAxiom` reads each parameter at
the opaque code of its own reserved path, so the statement it produces is the
source statement at one abstract type per parameter — a consequence of the
source's, not the whole of it. The quantified reading is `EcPolyForm` together
with `FormToProp.importedPropPoly`, which binds the codes outside everything else.

## A lemma is stated under its theory's imported axioms

The realizations an EasyCrypt lemma speaks about are the ones its theory's axioms
admit. `decodeLemmaAt` reads an `axiom_kind: Lemma` item at its path, collects
the `axiom_kind: Axiom` items of the scopes enclosing it (`scopeAxiomItems`),
decodes each, and assembles `∀ params, ax₁ → … → statement`
(`EcForm.assembleStatement`). An `axiom_kind: Axiom` item is refused as a goal,
and an axiom of the scope that does not decode rejects the lemma naming that
axiom.

## Signatures come from the export

`EcForm.hoare`, `EcForm.bdHoare`, `EcForm.equiv` and `EcProb.pr` carry the
signature of the procedure they name, and the serialised judgement carries only
the procedure's path. `FormTables.procSigs` holds the signature of each exported
procedure, keyed by the path the exporter writes at a judgement or probability
site; `procSigsOfStructure` builds it from a decoded module. A path outside the
table is an error.

## Node table

| JSON node | AST image |
|---|---|
| `Flocal` at a bound stamp | `EcTerm.var`, and `EcProb.pvar` at `real` |
| `Fop p`, `p` in `constPaths` | `EcTerm.lit`, and `EcForm.tru` / `.fls` at the booleans |
| `Fop p`, `p` in `absOpPaths` | `EcTerm.opApp` at the declared signature |
| `Fop p`, `p` in `defOpPaths` with parameters | the definition's body under one `EcTerm.lam` per parameter |
| `Fapp` of `Fop p`, `p` in `absOpPaths` | `EcTerm.opApp` at the declared signature, applied to the arguments as the right-nested pair |
| `Fapp` of `Fop p`, `p` in `polyOpPaths` | the definition's body, at the type arguments the node carries and with the value arguments substituted |
| `Fapp` of `Fop p`, `p` in `defOpPaths` at a body `decodeTerm` has no image for | the definition's body as a formula, under one `EcForm.letF` per parameter |
| `Fapp` of a head that is no `Fop`, in term position | `EcTerm.app`, one per argument, at the arrow codes the head's type gives |
| `Fapp` of `is_lossless` to a distribution-typed term | `EcForm.isLossless` |
| `Fpvar` of `PVloc res` | `EcTerm.res` at the memory's side |
| `Fpvar` of `PVglob` | `EcTerm.glob` |
| `Fapp` of a boolean operator | the matching `EcTerm` node, or the matching `EcForm` connective |
| `Fapp` of `=` at a type code | `EcTerm.beq` / `EcForm.eqT` |
| `Fapp` of integer `+` / `<=` | `EcTerm.intAdd` / `.intLe` |
| `Fapp` of integer `<` | `EcTerm.bnot` of the reversed `.intLe` |
| `Fapp` of `dom` / `::` / `size` / list `mem` / set `mem` | `EcTerm.mapMem` / `.listCons` / `.listSize` / `.listMem` / `.fsetMem` |
| `Fapp` of `_.[_]` / `_.[_<-_]` | `EcTerm.mapFind` at the option code / `.mapSet` |
| `Fapp` of `support` / `omap` | `EcTerm.support` / `.optionMap` |
| `Fapp` of `++` | `EcTerm.listCat` |
| `Fapp` of `` `*` `` / `\` | `EcTerm.distrProd` / `.distrExcept` |
| `Fapp` of `=`, `<=`, `<` at `real` | `EcForm.probCmp` |
| `Ftuple`, `Fproj` | `EcTerm.pair`, `.fst` / `.snd` |
| `Fif`, `Flet` of an `LSymbol` | `EcTerm.ite` / `EcForm.ifF`, `EcTerm.letIn` / `EcForm.letF` |
| `Fapp` of `=` between two `Fglob` | `EcForm.memEqOn` / `.memEqOnMod` |
| `Fquant` of `GTty` / `GTmem` / `GTmodty` | `EcForm.allTy` / `.exTy`, `.allMem` / `.exMem`, `.allMod` / `.allModOn`, `.allModRestr` / `.allModRestrOn` or `.allModRestrOf` / `.allModRestrOfOn` |
| `Fquant` of `GTty` at `real` | `EcForm.allProb` |
| `Fquant` of `GTty` in term position at `bool` | `EcTerm.forallB` / `.existsB` |
| `FhoareF`, `FbdHoareF`, `FequivF` | `EcForm.hoare`, `.bdHoare`, `.equiv` |
| `FbdHoareF` over an abstract module's procedure | `EcForm.lossless` |
| `Fpr` | `EcProb.pr` |
| `Fapp` of real `+`, `*` | `EcProb.add`, `.mul` |
| `Fapp` of `\|·\|` to a difference | `EcProb.absDiff` |
| `Fapp` of `mu` to a distribution and a predicate | `EcProb.mu` |
| `Fapp` of `from_int` to a non-negative `Fint` | `EcProb.const` |
| `Fint` at the `int` code | `EcTerm.lit` |

## Nodes with no image

Each is rejected with a message naming the construct and the reason, matching the
list `Form.lean` gives:

* the statement judgements `FhoareS`, `FbdHoareS`, `FequivS`, whose assertions
  range over procedure locals;
* `FeHoareF` and `FeHoareS`, the expectation-Hoare judgements;
* `FeagerF`, the eager judgement;
* `Fmatch`;
* `Fglob` in value position, and as a formula on its own: a footprint-restricted
  memory is not a value of an `EcTy`, and a footprint is not a proposition. An
  equality of two `Fglob` reads is in the fragment, as a footprint comparison;
* integer multiplication, negation and division in a term: `EcTerm` carries
  addition and the order comparison, and no other integer operator, so an
  application of one is rejected by path;
* any real term outside the probability fragment — in particular a quotient, a
  signed negation, and a signed difference of two probabilities;
* `Fpvar` of a `PVloc` other than `res`, the procedure-local read at a memory;
* `Fquant` of a lambda, and an existential over a module type;
* a module restriction that names individual procedures, or that lists what the
  module may touch rather than what it may not: the emitted hypothesis is stated
  against a module's footprint;
* a bounded Hoare judgement over an abstract module's procedure other than
  `islossless`: the module has no body to reason against;
* a read of an operator whose declaration does not register — a defined operator,
  a polymorphic one (`Json.lean`'s `decodeThOperatorAbstract`) — which reports
  the unknown-path error of its read site;
* an application of a declared operator whose arguments do not nest into the
  declared argument code, which names the declared code and the code the
  arguments nest into;
* a `Th_axiom` with type parameters;
* an `axiom_kind: Lemma` item one of whose scope's imported axioms does not
  decode, which reports that axiom's own error under the lemma's path;
* an `Unsupported` node, which the exporter emits for a construct outside its own
  coverage.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.EasyCryptImport

open Lean (Json)
open Hax.JsonSize
open scoped ENNReal

/-! ## Chained decreases -/

/-- Two nested field lookups strictly decrease the `jsonSize` measure. -/
theorem getObj_getObj_decreases {j v w : Json} {k₁ k₂ : String}
    (h₁ : getObj j k₁ = .ok v) (h₂ : getObj v k₂ = .ok w) : jsonSize w < jsonSize j :=
  Nat.lt_trans (getObj_decreases h₂) (getObj_decreases h₁)

/-! ## Dispatch paths for the statement layer -/

/-- The EasyCrypt paths the statement layer dispatches on beyond the program
fragment's tables: the type of reals, the real operators a probability expression
is built from, propositional equivalence, and the operators the term layer reads
ahead of the operator tables. -/
structure FormPaths where
  /-- The path of EasyCrypt's `real` type. -/
  realTy : String
  /-- The injection of an integer into the reals. -/
  realFromInt : String
  /-- Real addition. -/
  realAdd : String
  /-- Real multiplication. -/
  realMul : String
  /-- Real negation. -/
  realOpp : String
  /-- Real reciprocal, which is how a fractional bound is written. -/
  realInv : String
  /-- Real absolute value. -/
  realAbs : String
  /-- The non-strict order on the reals. -/
  realLe : String
  /-- The strict order on the reals. -/
  realLt : String
  /-- Propositional equivalence. -/
  iffOp : String
  /-- The predicate asserting that a distribution has total mass one. -/
  losslessOp : String
  /-- Membership in a distribution's support, EasyCrypt's `support`, at every
  spelling the export writes it under. `Distr.ec` roots its own declarations at
  `Top`, so a client that reads the theory qualified writes `Top.Distr.support`
  and one that reads it unqualified writes `Top.support`. -/
  supportOps : List String
  /-- The image of an option under a function, EasyCrypt's `omap`, at every
  spelling the export writes it under. -/
  optionMapOps : List String
  /-- The pushforward of a distribution along a function, EasyCrypt's `dmap`, at
  every spelling the export writes it under. -/
  distrMapOps : List String
  /-- The bind of a distribution with a distribution-valued function,
  EasyCrypt's `dlet`, at every spelling the export writes it under. -/
  distrLetOps : List String
  /-- The values a predicate holds of, EasyCrypt's `to_seq`, at every spelling
  the export writes it under. -/
  toSeqOps : List String
  /-- Catenation of two lists, EasyCrypt's `++`, at every spelling the export
  writes it under. -/
  listCatOps : List String
  /-- The independent product of two distributions, EasyCrypt's `` `*` ``, at
  every spelling the export writes it under. -/
  distrProdOps : List String
  /-- A distribution conditioned on avoiding a predicate, EasyCrypt's `\`, at
  every spelling the export writes it under. -/
  distrExceptOps : List String
  /-- Whether a key is bound in a finite map, EasyCrypt's `dom`, at the
  spellings the program fragment's operator table does not carry. `FMap.ec`
  roots its own declarations at `Top`, so its own statements write `Top.dom`
  where a client writes `Top.FMap.dom`. -/
  mapDomOps : List String
  /-- The binding of a key in a finite map, EasyCrypt's `m.[k]`, at the
  spellings the program fragment's operator table does not carry. -/
  mapLookupOps : List String
  /-- Whether a type's carrier is finite, EasyCrypt's `finite_type`, at every
  spelling the export writes it under. This operator is nullary and takes its
  type by type argument. -/
  finiteTypeOps : List String
  /-- The predicate every value satisfies, EasyCrypt's `predT`, at every
  spelling the export writes it under. This operator is read unapplied, as the
  predicate argument of an enumeration or a measure. -/
  predTOps : List String
  /-- The probability that a sample satisfies a predicate, EasyCrypt's `mu`, at
  every spelling the export writes it under. `Pervasive.ec` roots its own
  declarations at `Top`, so a client reads it at `Top.Pervasive.mu` and the
  declaring theory's own statements at `Top.mu`. -/
  muOps : List String
  /-- The name EasyCrypt gives the result of a judgement. -/
  resName : String

/-- The paths of EasyCrypt's real prelude and of `<=>`. -/
def ecFormPaths : FormPaths where
  realTy := "Top.Pervasive.real"
  realFromInt := "Top.CoreReal.from_int"
  realAdd := "Top.CoreReal.add"
  realMul := "Top.CoreReal.mul"
  realOpp := "Top.CoreReal.opp"
  realInv := "Top.CoreReal.inv"
  realAbs := "Top.Real.`|_|"
  realLe := "Top.CoreReal.le"
  realLt := "Top.CoreReal.lt"
  iffOp := "Top.Pervasive.<=>"
  losslessOp := "Top.Distr.is_lossless"
  supportOps := ["Top.Distr.support", "Top.support"]
  optionMapOps := ["Top.Logic.omap", "Top.omap"]
  distrMapOps := ["Top.Distr.dmap", "Top.dmap"]
  distrLetOps := ["Top.Distr.dlet", "Top.dlet"]
  toSeqOps := ["Top.Finite.to_seq", "Top.to_seq"]
  listCatOps := ["Top.List.++", "Top.++"]
  distrProdOps := ["Top.Distr.`*`", "Top.`*`"]
  distrExceptOps := ["Top.Dexcepted.\\", "Top.\\"]
  mapDomOps := ["Top.dom"]
  mapLookupOps := ["Top._.[_]"]
  finiteTypeOps := ["Top.Finite.finite_type", "Top.finite_type"]
  predTOps := ["Top.Logic.predT", "Top.predT"]
  muOps := ["Top.Pervasive.mu", "Top.mu"]
  resName := "res"

/-- The tables a statement decodes against: the program fragment's dispatch
tables, the statement layer's paths, the signature of each exported procedure,
the interface of each exported module type, and the binders in scope. -/
structure FormTables where
  /-- The program fragment's dispatch tables. -/
  tables : DecodeTables
  /-- The statement layer's dispatch paths. -/
  paths : FormPaths
  /-- The signature of each procedure, keyed by the path a judgement names it
  by. -/
  procSigs : List (String × EcSig)
  /-- The interface of each module type, keyed by its path. -/
  modTypes : List (String × EcInterface)
  /-- The `var` declarations of each module, keyed by its path. A module named by
  a restriction is looked up here for the footprint the restriction is stated
  against. -/
  modGlobals : List (String × List EcGlobal)
  /-- The interface of each module binder in scope, keyed by the binder's source
  name. A judgement over a procedure of an abstract module reads its signature
  here, since the module has no exported body. -/
  modBinders : List (String × EcInterface)
  /-- The source name each module binder's stamp carries. A `glob A` read names
  its module by identifier, and the stamp is what tells one binder from
  another. -/
  modBinderStamps : List (Nat × String)
  /-- The memory each bound memory identifier's stamp denotes. -/
  mems : List (Nat × EcMemRef)
  /-- The source name each bound logical variable's stamp carries. -/
  locals : List (Nat × String)
  /-- The theory items a statement's scope is read from: the item list of the
  envelope it comes from, whose `Th_theory` items hold the inner scopes. A lemma
  is stated under the imported axioms of the scopes enclosing it, which
  `scopeAxiomItems` finds here. -/
  scopeItems : List Json
  /-- The first heap location id no module has been given. Distinct modules hold
  distinct state, so each is decoded at a range disjoint from every other's, and
  this is where the next range starts. A scope inside a theory continues from the
  enclosing scope's value rather than restarting. -/
  nextLoc : Nat := 0

/-- The tables for a statement about the modules of one export, with no binder in
scope. -/
def formTables (T : DecodeTables) (procSigs : List (String × EcSig))
    (modTypes : List (String × EcInterface) := [])
    (modGlobals : List (String × List EcGlobal) := [])
    (scopeItems : List Json := []) : FormTables where
  tables := T
  paths := ecFormPaths
  procSigs := procSigs
  modTypes := modTypes
  modGlobals := modGlobals
  modBinders := []
  modBinderStamps := []
  mems := []
  locals := []
  scopeItems := scopeItems

/-! ## Binder environments -/

/-- Bind a memory identifier's stamp to the memory it denotes. -/
def FormTables.bindMemStamp (F : FormTables) (st : Nat) (r : EcMemRef) : FormTables :=
  { F with mems := (st, r) :: F.mems }

/-- Bind a quantified memory, checking that no other live binder carries its
source name. -/
def FormTables.bindMemName (F : FormTables) (st : Nat) (nm : String) :
    Except String FormTables :=
  if F.mems.any (fun p => decide (p.2 = EcMemRef.named nm) && p.1 != st) then
    fail s!"the memory '{nm}' is bound by two different binders: a memory read \
      without its stamp aliases them"
  else
    .ok (F.bindMemStamp st (.named nm))

/-- Bind a logical variable, checking that no other live binder carries its
source name. -/
def FormTables.bindLocal (F : FormTables) (st : Nat) (nm : String) :
    Except String FormTables :=
  if F.locals.any (fun p => p.2 == nm && p.1 != st) then
    fail s!"the logical variable '{nm}' is bound by two different binders: a \
      variable read without its stamp aliases them"
  else
    .ok { F with locals := (st, nm) :: F.locals }

/-- The name a binder is read under when its source name alone would alias
another binder: its source name and its uniqueness stamp. -/
def freshLocalName (nm : String) (st : Nat) : String := s!"{nm}_{st}"

/-- The name the logical variable `nm` at `stamp` is bound under: its source name
when no other live binder carries that name, and `freshLocalName` otherwise. -/
def FormTables.localBindName (F : FormTables) (st : Nat) (nm : String) : String :=
  if F.locals.any (fun p => p.2 == nm && p.1 != st) then freshLocalName nm st else nm

/-- Bind a module binder's source name to the interface it ranges over, and its
stamp to that name. -/
def FormTables.bindModBinder (F : FormTables) (st : Nat) (nm : String)
    (I : EcInterface) : FormTables :=
  { F with modBinders := (nm, I) :: F.modBinders,
           modBinderStamps := (st, nm) :: F.modBinderStamps }

/-- The interface and procedure name a cross-path denotes, when its module path
is a module binder in scope. This is how a judgement over `A.f` finds a
signature: an abstract module has no exported body, so its procedures are not in
`procSigs`. -/
def abstractProcOf (F : FormTables) (q : String) : Option (EcInterface × String) :=
  F.modBinders.findSome? (fun p =>
    let pfx := xqualify p.1 ""
    if q.startsWith pfx then
      let nm := (q.drop pfx.length).toString
      if p.2.names.contains nm then some (p.2, nm) else none
    else none)

/-- The memory the identifier at the field `k` denotes. -/
def memRefOf (F : FormTables) (j : Json) (k : String) : Except String EcMemRef := do
  let mj ← getObj j k
  let nm ← getStr mj "name"
  let st ← getNat mj "stamp"
  match List.lookup st F.mems with
  | some r => .ok r
  | none =>
    fail s!"the memory '{nm}' (stamp {st}) is bound by no enclosing quantifier or \
      judgement"

/-- The stamp of the memory identifier at the field `k`. -/
def memStampOf (j : Json) (k : String) : Except String Nat := do
  let mj ← getObj j k
  getNat mj "stamp"

/-- The source name of a bound logical variable. -/
def localNameOf (F : FormTables) (j : Json) : Except String String := do
  let nm ← getStr j "name"
  let st ← getNat j "stamp"
  match List.lookup st F.locals with
  | some nm' => .ok nm'
  | none =>
    fail s!"the logical variable '{nm}' (stamp {st}) is bound by no enclosing \
      quantifier or let"

/-- The signature of the procedure a judgement or probability node names, read
off the exported modules' signatures or, for a procedure of a module binder in
scope, off the interface that binder ranges over. -/
def procSigOf (F : FormTables) (q : String) : Except String EcSig :=
  match List.lookup q F.procSigs with
  | some s => .ok s
  | none =>
    match abstractProcOf F q with
    | some (I, p) => .ok (I.sig p)
    | none =>
      -- A judgement naming a procedure of a module expression resolves at the
      -- head, for the reason `callHeadPath` records: a procedure's signature is
      -- declared by its module's type and not by the modules a functor is
      -- applied to. Which module the expression is stays the caller's to supply,
      -- through `FormEnv.functorImages`.
      let h := callHeadPath q
      match if h == q then none else List.lookup h F.procSigs with
      | some s => .ok s
      | none =>
        match if h == q then none else abstractProcOf F h with
        | some (I, p) => .ok (I.sig p)
        | none =>
          fail s!"the procedure '{q}' is not in the ingestion's signature table \
            and names no procedure of a module binder in scope, at its own path \
            or at its head, so the signature its judgement carries cannot be \
            reconstructed"

/-! ## Module restrictions

An exported restriction is a `use_restr` over procedure paths and over module
paths: a negative set of what the module may not touch, and an optional positive
set of what it may. Only the negative module set has an image, so the other three
components are rejected rather than dropped.

An element of that set is a concrete module, whose footprint is its `var`
declarations; a module binder in scope, whose footprint is the one its own
quantifier binds; or a functor applied to such modules, whose footprint is the
head's together with the arguments'. An element the reader resolves to none of
the three is rejected, since a footprint guessed wider than the source's makes
the hypothesis it states a stronger one. -/

/-- The elements of the negative set of an exported `use_restr`, and an error if
its positive set is present. -/
def restrNeg (j : Json) (k : String) : Except String (List String) := do
  let u ← getObj j k
  let pos ← getObj u "pos"
  match pos with
  | .null =>
    let a ← getArr u "neg"
    a.toList.mapM (fun x =>
      match x with
      | .str s => .ok s
      | _ => fail s!"the restriction element {x.compress} is not a path")
  | _ =>
    fail s!"the positive restriction '{k}' in {u.compress}: a restriction that \
      lists what a module may touch has no image, since the emitted hypothesis \
      states what it may not"

/-- Split a character list at its top-level commas, dropping the separators. -/
private def splitTopCommas : List Char → Nat → List Char → List (List Char)
  | [], _, acc => [acc.reverse]
  | ',' :: rest, 0, acc => acc.reverse :: splitTopCommas rest 0 []
  | c :: rest, d, acc =>
      splitTopCommas rest (if c = '(' then d + 1 else if c = ')' then d - 1 else d)
        (c :: acc)

/-- The head and the arguments of a module application: `Top.Count(O)` is
`("Top.Count", ["O"])`, and a path carrying no application group is itself with
no arguments. -/
def splitModApp (q : String) : String × List String :=
  let cs := q.toList
  match cs.findIdx? (· = '(') with
  | none => (q, [])
  | some i =>
    if cs.getLast? = some ')' then
      let inner := (cs.drop (i + 1)).dropLast
      (String.ofList (cs.take i),
        (splitTopCommas inner 0 []).map (fun p => String.ofList (p.filter (· ≠ ' ')))
          |>.filter (· ≠ ""))
    else (q, [])

#guard splitModApp "Top.Count(O)" == ("Top.Count", ["O"])
#guard splitModApp "Top.F(A, B)" == ("Top.F", ["A", "B"])
#guard splitModApp "Top.Sample" == ("Top.Sample", [])
#guard splitModApp "Top.F(G(A), B)" == ("Top.F", ["G(A)", "B"])

/-- The footprint a module path with no application names: the module binder in
scope it is, or the `var` declarations the ingestion's table holds for it. The
binder table is consulted first, since EasyCrypt qualifies every path of a
concrete module and a bare name in a restriction is a binder. `whole` is the
restriction element the path comes from, which is the path itself unless the
element applies a functor. -/
def restrLeaf (F : FormTables) (whole m : String) : Except String EcModRestr :=
  if (List.lookup m F.modBinders).isSome then
    .ok { globals := [], binders := [m] }
  else
    match List.lookup m F.modGlobals with
    | some gs => .ok { globals := gs, binders := [] }
    | none =>
      if m == whole then
        fail s!"the restricting module '{m}' is neither a module binder in scope \
          nor a module of the ingestion's module-globals table, so the footprint \
          it names is unknown"
      else
        fail s!"the restricting module '{whole}' names '{m}', which is neither a \
          module binder in scope nor a module of the ingestion's module-globals \
          table, so the footprint the application names is unknown"

/-- The footprint one element of a restriction's negative module set names. An
applied functor names the footprint of its head together with those of its
arguments, which is what `glob F(A)` covers in EasyCrypt. -/
def restrTarget (F : FormTables) (m : String) : Except String EcModRestr := do
  let (h, args) := splitModApp m
  let hd ← restrLeaf F m h
  let rs ← args.mapM (restrLeaf F m)
  .ok (rs.foldl EcModRestr.append hd)

/-- The modules an exported module restriction names, or `none` when the
restriction is empty. -/
def restrModules (F : FormTables) (g : Json) : Except String (Option EcModRestr) := do
  let r ← getObj g "restr"
  let xs ← restrNeg r "xpaths"
  let ms ← restrNeg r "mpaths"
  if xs ≠ [] then
    fail s!"the procedure-level restriction {xs} in {r.compress}: the emitted \
      hypothesis is stated against a module's footprint, and a restriction \
      naming individual procedures has no footprint"
  else if ms = [] then
    .ok none
  else
    let rs ← ms.mapM (restrTarget F)
    .ok (some (rs.foldl EcModRestr.append EcModRestr.empty))

/-- The footprint an exported module restriction names, when every module it
names is a concrete module of the ingestion's table: the `var` declarations of
each, or `none` when the restriction is empty. -/
def restrGlobals (F : FormTables) (g : Json) : Except String (Option (List EcGlobal)) := do
  match ← restrModules F g with
  | none => .ok none
  | some r =>
    if r.binders.isEmpty then .ok (some r.globals)
    else
      fail s!"the restriction against the module binders {r.binders}: their \
        footprints are bound variables, and this reader gives a footprint of \
        declared globals"

/-- The `use_restr` node excluding the modules `ms` and nothing else, at the
exporter's shape. -/
private def jUseRestr (ms : List String) : Json :=
  Json.mkObj
    [("mpaths", Json.mkObj
        [("neg", Json.arr (ms.map Json.str).toArray), ("pos", Json.null)]),
     ("xpaths", Json.mkObj [("neg", Json.arr #[]), ("pos", Json.null)])]

/-- A node carrying the restriction that excludes the modules `ms`. -/
private def jRestrOf (ms : List String) : Json :=
  Json.mkObj [("restr", jUseRestr ms)]

/-- An interface declaring no procedure, for the checks below. -/
private def chkRestrInterface : EcInterface where
  names := []
  sig := fun _ => ⟨.unit, .unit⟩

/-- The tables the restriction checks read: the module binder `A` in scope, the
concrete module `Top.M` declaring one global, and the parameter-free functor
`Top.F` declaring none. -/
private def chkRestrTables : FormTables :=
  { formTables ecPrelude [] with
      modTypes := [("Top.I", chkRestrInterface)],
      modBinders := [("A", chkRestrInterface)],
      modGlobals := [("Top.M", [{ name := "Top.M./g", id := 7, ty := .bool }]),
                     ("Top.F", [])] }

-- A restriction against a module of the ingestion's table names its declared
-- globals.
#guard (match restrModules chkRestrTables (jRestrOf ["Top.M"]) with
        | .ok (some r) => r.globals.map (·.id) == [7] && r.binders == []
        | _ => false)

-- A restriction against a module binder in scope names the binder, whose
-- footprint the binder's own quantifier binds.
#guard (match restrModules chkRestrTables (jRestrOf ["A"]) with
        | .ok (some r) => r.globals.isEmpty && r.binders == ["A"]
        | _ => false)

-- An applied functor names the footprint of its head together with those of its
-- arguments.
#guard (match restrModules chkRestrTables (jRestrOf ["Top.F(A)"]) with
        | .ok (some r) => r.globals.isEmpty && r.binders == ["A"]
        | _ => false)

-- A restriction naming a concrete module and a binder names both.
#guard (match restrModules chkRestrTables (jRestrOf ["Top.M", "A"]) with
        | .ok (some r) => r.globals.map (·.id) == [7] && r.binders == ["A"]
        | _ => false)

-- A path that is neither a binder in scope nor a module of the table is
-- rejected, and the message says which it is not.
#guard (match restrModules chkRestrTables (jRestrOf ["Top.Absent"]) with
        | .error m =>
          m.startsWith "ec-import: the restricting module 'Top.Absent' is neither \
            a module binder in scope"
        | _ => false)

-- An application whose head is neither is rejected at the head, which the
-- message names alongside the element it comes from.
#guard (match restrModules chkRestrTables (jRestrOf ["Top.Absent(A)"]) with
        | .error m => (m.splitOn "names 'Top.Absent'").length == 2
        | _ => false)

-- The empty restriction names no footprint.
#guard (match restrModules chkRestrTables (jRestrOf []) with
        | .ok none => true
        | _ => false)

-- The globals reader agrees with it on a restriction naming only concrete
-- modules, and rejects one naming a binder, whose footprint is not a list of
-- declarations.
#guard (match restrGlobals chkRestrTables (jRestrOf ["Top.M"]) with
        | .ok (some gs) => gs.map (·.id) == [7]
        | _ => false)

#guard (restrGlobals chkRestrTables (jRestrOf ["A"])).toOption.isNone

/-! ## Footprint comparisons

`={glob M}` is an equality whose two sides are `glob M` read at the two memories.
For a concrete `M` the typechecker expands it before the export, into one
equality per declared `var`, so what reaches a `Fglob` node is a module
identifier: the binder of an abstract module. The two shapes have separate
targets — the declared globals of a module the ingestion knows, and the footprint
carried by a binder in scope. -/

/-- The module identifier a node names, when the node is a `glob M` read. -/
def globIdentOf (j : Json) : Option (String × Nat) :=
  match getStr j "kind" with
  | .ok "Fglob" =>
    match getObj j "module" with
    | .ok m =>
      match getStr m "name", getNat m "stamp" with
      | .ok nm, .ok st => some (nm, st)
      | _, _ => none
    | .error _ => none
  | _ => none

/-- The two operands of an equality, when both are `glob M` reads. -/
def globEqPair (args : Array Json) : Option (Json × Json) :=
  match args.toList with
  | [x, y] => if (globIdentOf x).isSome && (globIdentOf y).isSome then some (x, y) else none
  | _ => none

/-- The footprint comparison an equality of two `glob M` reads denotes:
agreement, at the two memories the operands are read in, on the footprint of the
module both name. -/
def decodeGlobEq (F : FormTables) (x y : Json) : Except String EcForm := do
  let mx ← getObj x "module"
  let nx ← getStr mx "name"
  let sx ← getNat mx "stamp"
  let my ← getObj y "module"
  let ny ← getStr my "name"
  let sy ← getNat my "stamp"
  if sx ≠ sy then
    fail s!"the comparison of 'glob {nx}' with 'glob {ny}': EcForm compares one \
      module's footprint at two memories, and these name two modules"
  else
    let m₁ ← memRefOf F x "mem"
    let m₂ ← memRefOf F y "mem"
    match List.lookup sx F.modBinderStamps with
    | some nm => .ok (.memEqOnMod nm m₁ m₂)
    | none =>
      match List.lookup nx F.modGlobals with
      | some gs => .ok (.memEqOn gs m₁ m₂)
      | none =>
        fail s!"'glob {nx}' (stamp {sx}) names neither a module binder in scope \
          nor a module of the ingestion's module-globals table, so the footprint \
          it compares is unknown"

/-- The path of the type constructor the field `k` names, when that field holds a
nullary type constructor. -/
def tyConstrPath (j : Json) (k : String) : Option String :=
  match j.getObjVal? k with
  | .ok tj =>
    match tj.getObjValAs? String "kind" with
    | .ok "Tconstr" =>
      match tj.getObjValAs? String "path" with
      | .ok p => some p
      | .error _ => none
    | _ => none
  | .error _ => none

/-- The path of the head operator of an application. -/
def appHeadPath (j : Json) : Except String String := do
  let fJ ← getObj j "f"
  match ← getStr fJ "kind" with
  | "Fop" => getStr fJ "path"
  | k =>
    fail s!"application of a head of kind '{k}' in {j.compress}: the head of a \
      formula-position application is an operator; a function applied to an \
      argument decodes in term position"

/-- The path of the first type argument of an applied operator, when that
argument is a nullary type constructor. -/
def appHeadTarg (j : Json) : Option String :=
  match j.getObjVal? "f" with
  | .ok fJ =>
    match fJ.getObjVal? "targs" with
    | .ok (.arr a) =>
      match a.toList with
      | t :: _ =>
        match t.getObjValAs? String "kind", t.getObjValAs? String "path" with
        | .ok "Tconstr", .ok p => some p
        | _, _ => none
      | [] => none
    | _ => none
  | .error _ => none

/-- The type arguments a read site gives an applied operator, as the exporter's
type nodes. -/
def appHeadTargs (j : Json) : List Json :=
  match j.getObjVal? "f" with
  | .ok fJ =>
    match fJ.getObjVal? "targs" with
    | .ok (.arr a) => a.toList
    | _ => []
  | .error _ => []

/-- The type arguments a nullary operator read gives the operator, as the
exporter's type nodes. -/
def nullaryTargs (j : Json) : List Json :=
  match j.getObjVal? "targs" with
  | .ok (.arr a) => a.toList
  | _ => []

/-- Whether a node is an application of the operator `p`. -/
def isAppOf (p : String) (j : Json) : Bool :=
  match j.getObjValAs? String "kind" with
  | .ok "Fapp" =>
    match appHeadPath j with
    | .ok q => q == p
    | .error _ => false
  | _ => false

/-- Whether a node is an application of one of the operators `ps`. -/
def isAppOfAny (ps : List String) (j : Json) : Bool :=
  ps.any (fun p => isAppOf p j)

/-- Transport a term along an equality of type codes. -/
def EcTerm.castTy {a b : EcTy} (h : a = b) (e : EcTerm a) : EcTerm b :=
  cast (congrArg EcTerm h) e

/-! ## The definitions a read still has left

A read of a concrete operator declaration decodes to the operator's definition,
and the definition is decoded in turn, so `decodeTerm` recurses into a node that
is not a sub-node of the one it started from. What decreases instead is the table
of definitions: the body is decoded against the table with that operator dropped,
so an operator cannot be reached from inside its own definition and a chain of
definitions is as long as the table. The measure `decodeTerm` recurses on is the
pair of that table's length and the node's size, ordered lexicographically; the
lemma below is the decrease of the first component. -/

/-- The tables with the definition of `path` dropped. -/
def FormTables.withoutDefOp (F : FormTables) (path : String) : FormTables :=
  { F with tables :=
      { F.tables with
        defOpPaths := F.tables.defOpPaths.filter (fun e => e.1 != path) } }

/-- Binding a logical variable leaves the dispatch tables alone, which is what
lets a recursion measured on them descend under a binder. -/
theorem bindLocal_tables {F F' : FormTables} {st : Nat} {nm : String}
    (h : F.bindLocal st nm = .ok F') : F'.tables = F.tables := by
  unfold FormTables.bindLocal at h
  split at h
  · simp [fail] at h
  · injection h with h
    subst h
    rfl

/-- Dropping an entry a lookup finds shortens the list. -/
theorem length_filter_ne_lt_of_lookup {β : Type} (l : List (String × β)) (p : String)
    (h : (List.lookup p l).isSome) :
    (l.filter (fun e => e.1 != p)).length < l.length := by
  induction l with
  | nil => simp at h
  | cons a as ih =>
    rw [List.filter_cons]
    by_cases hp : p = a.1
    · rw [if_neg (by simp [hp])]
      exact Nat.lt_succ_of_le (List.length_filter_le _ _)
    · rw [if_pos (by simp [Ne.symm hp])]
      have hb : (p == a.1) = false := by simpa using hp
      have hlk : (List.lookup p as).isSome := by
        simpa [List.lookup, hb] using h
      simpa using Nat.succ_lt_succ (ih hlk)

/-- The definitions left after the one at `path` is dropped are fewer. -/
theorem withoutDefOp_length_lt (F : FormTables) (path : String)
    (h : (List.lookup path F.tables.defOpPaths).isSome) :
    (F.withoutDefOp path).tables.defOpPaths.length
      < F.tables.defOpPaths.length :=
  length_filter_ne_lt_of_lookup _ _ h

/-- The decrease in the shape a lookup at a read site produces it. -/
theorem withoutDefOp_length_lt_of_eq (F : FormTables) (path : String) {d : EcOpDefn}
    (h : List.lookup path F.tables.defOpPaths = some d) :
    (F.withoutDefOp path).tables.defOpPaths.length
      < F.tables.defOpPaths.length :=
  withoutDefOp_length_lt F path (by rw [h]; rfl)

/-! ## Reading a concrete operator definition

A theory-level `op f a b = e.` is a definition the source fixes, and
`DecodeTables.defOpPaths` (`Json.lean`) holds it as an `EcOpDefn`: the parameters
at their declared codes, the result code, and the body node. A read of one
decodes to the body with the parameters bound to the arguments, which is what
`EcTerm.letIn` expresses.

The body is decoded where the read is, so the decode walks only the definitions
the statement actually reaches, and a statement whose own nodes leave the
fragment first fails there with no body looked at.

What makes this the shape to keep is not what it decodes — it decodes the same
statements a rewriting of the whole node before the decode would. It is the
termination argument. `decodeTerm` recurses on the pair of the definitions still
available and the node's size, ordered lexicographically, and the body is decoded
against the tables with that definition dropped, so the length of the table
bounds a chain of reads. A definition that reads itself, mutually or otherwise,
cannot be built, rather than being caught: `decodeThOperatorConcrete`'s check that
a defining form does not name its own path (`mentionsPath`, `Json.lean`) is a
better error message for a case that is already impossible here, and the decode
rests on the measure rather than on the corpus being acyclic.

**Names.** `EcTerm.letIn` binds by source name and `FormTables.bindLocal` refuses
a source name another live binder carries, so a definition whose parameter is
named `a`, read inside a statement quantifying its own `a`, would be refused;
binding it without that check would instead capture the statement's own `a`
silently. Each parameter is bound under its source name and its uniqueness stamp
(`opParamName`), and its occurrences in the body carry that stamp, so they resolve
to the renamed binder.

**Types.** Each argument is decoded at its own `ty` and the resulting codes are
compared with the codes the declaration gives the parameters, so an argument the
declaration does not accept is named rather than bound.

**Provenance.** The body's decode is reported as a failure of the operator,
naming it, since the node it fails at is one the statement does not contain. -/

/-- The name a definition's parameter is bound under: its source name and its
uniqueness stamp. -/
def opParamName (x : EcVarId) : String :=
  match x.stamp with
  | some s => freshLocalName x.name s
  | none => x.name

/-- The tables with each of a definition's parameters bound as a logical
variable, under the name `opParamName` gives it. -/
def bindOpParams (F : FormTables) (path : String) :
    List (EcVarId × EcTy) → Except String FormTables
  | [] => .ok F
  | (x, _) :: rest =>
    match x.stamp with
    | none =>
      fail s!"the operator '{path}' is defined with a parameter '{x.name}' that \
        carries no uniqueness stamp, so its occurrences in the body cannot be \
        resolved"
    | some st =>
      match F.bindLocal st (opParamName x) with
      | .error e => .error e
      | .ok F' => bindOpParams F' path rest

/-- Binding a definition's parameters leaves the dispatch tables alone. -/
theorem bindOpParams_tables {path : String} :
    ∀ {ps : List (EcVarId × EcTy)} {F F' : FormTables},
      bindOpParams F path ps = .ok F' → F'.tables = F.tables
  | [], F, F', h => by
      unfold bindOpParams at h; injection h with h; exact congrArg _ h.symm
  | (x, _) :: rest, F, F', h => by
      unfold bindOpParams at h
      split at h
      · simp [fail] at h
      · rename_i st _
        split at h
        · simp at h
        · rename_i F₁ hbl
          exact (bindOpParams_tables h).trans (bindLocal_tables hbl)

/-- The term `body` under one `letIn` per bound parameter, the first parameter
outermost. -/
def wrapOpLets {t : EcTy} :
    List (String × (u : EcTy) × EcTerm u) → EcTerm t → EcTerm t
  | [], e => e
  | (nm, ⟨_, v⟩) :: rest, e => .letIn nm v (wrapOpLets rest e)

/-- The formula `body` under one `letF` per bound parameter, the first parameter
outermost. -/
def wrapOpLetsF :
    List (String × (u : EcTy) × EcTerm u) → EcForm → EcForm
  | [], f => f
  | (nm, ⟨_, v⟩) :: rest, f => .letF nm v (wrapOpLetsF rest f)

/-- The judgement node kinds, which are formulas and never terms or
probabilities. -/
def judgementKinds : List String :=
  ["FhoareF", "FhoareS", "FbdHoareF", "FbdHoareS", "FeHoareF", "FeHoareS",
   "FequivF", "FequivS", "FeagerF"]

/-- The term `f` applied to the arguments `xs` in order, at the arrow codes `f`'s
own code gives. A head whose code is no arrow, and an argument whose code is not
the domain the head expects, are each rejected with a message naming the two
codes.

The exporter writes a curried application with all of its arguments in one node,
so this walks the list and peels one arrow per argument; a head applied to fewer
arguments than its code has arrows lands at the remaining arrow code, which the
read site then has to expect. -/
def applyArgs : ((t : EcTy) × EcTerm t) → List ((u : EcTy) × EcTerm u) →
    Except String ((r : EcTy) × EcTerm r)
  | f, [] => .ok f
  | ⟨.arrow a b, f⟩, ⟨u, x⟩ :: rest =>
      if h : u = a then
        applyArgs ⟨b, EcTerm.app f (EcTerm.castTy h x)⟩ rest
      else
        fail s!"a function of domain {repr a} is applied to an argument of type \
          {repr u}"
  | ⟨t, _⟩, _ :: _ =>
    fail s!"a value of type {repr t} is applied to an argument: only an arrow \
      code is applied"

/-! ## The binders of a quantified term

An EasyCrypt proposition is a value of `bool`, so a quantifier stands wherever a
boolean term does. `bindTermBinders` reads the binder list of such a node: every
binder ranges over the values of a type code, and a memory or module binder is
refused, since neither is a value of an `EcTy`.

The result is the `locals` the body is decoded under rather than the extended
tables, so that the dispatch tables of the extended environment are the caller's
own by construction — which is what lets the recursion measured on them descend
under the binders. -/

/-- The logical variables the binders of a quantified term bind, and the code
and the name of each binder in source order.

A binder is bound under `FormTables.localBindName`, so a binder whose source name
another live binder already carries is read under a freshened name, exactly as a
formula quantifier's binder is. -/
def bindTermBinders : FormTables → List Json →
    Except String (List (Nat × String) × List (EcTy × String))
  | F, [] => .ok (F.locals, [])
  | F, b :: bs =>
    match getStr b "name", getNat b "stamp", getObj b "gty" with
    | .ok nm, .ok st, .ok g =>
      match getStr g "kind" with
      | .error e => .error e
      | .ok "GTty" =>
        match decodeTyField F.tables g "ty" with
        | .error e => .error e
        | .ok u =>
          let x := F.localBindName st nm
          match F.bindLocal st x with
          | .error e => .error e
          | .ok F' =>
            match bindTermBinders F' bs with
            | .error e => .error e
            | .ok (ls, xs) => .ok (ls, (u, x) :: xs)
      | .ok k =>
        fail s!"the binder '{nm}' of sort '{k}' in a quantified term: a term \
          quantifier ranges over the values of a type code"
    | _, _, _ =>
      fail s!"a quantifier binder without a name, a stamp and a sort in \
        {b.compress}"

/-- The term `body` under one quantifier per binder, the first binder
outermost. -/
def wrapQuantTerm (universal : Bool) :
    List (EcTy × String) → EcTerm .bool → EcTerm .bool
  | [], e => e
  | (u, x) :: rest, e =>
    let inner := wrapQuantTerm universal rest e
    if universal then .forallB u x inner else .existsB u x inner

/-! ## Terms

A term decodes at the type code the context expects, and the node's own `ty`
field must agree with it, exactly as an expression does in `Json.lean`. `EcTerm`
contains no formula, so this decoder stands outside the mutual recursion
below.

An `Fapp` whose head is an `Fop` is an operator application, and the operator
routes below decode it. An `Fapp` whose head is a lambda has no image, since
`EcTerm` has no lambda. Any other head is a function applied to arguments: the
head decodes at its own type node, which is an arrow code, and `applyArgs` peels
one arrow per argument. That head is typically an `Flocal` an enclosing
`EcForm.allTy` bound at a function type. -/

/-- Decode a formula node in term position, at the type code `t`. -/
def decodeTerm (F : FormTables) (t : EcTy) (j : Json) : Except String (EcTerm t) :=
  match getStr j "kind" with
  | .error e => .error e
  | .ok kind =>
    if kind = "Fglob" then
      fail s!"'glob M' in value position in {j.compress}: a memory restricted to \
        a module's footprint is not a value of an EcTy"
    else if kind = "Fmatch" then
      fail s!"match term in {j.compress}: EcTy has no sum or inductive codes, so \
        there is nothing to match on"
    else if kind = "Fquant" then
      -- A lambda over a single binder is `EcTerm.lam`, which is what the source
      -- supplies for the function argument of a list combinator.
      match getStr j "quant" with
      | .ok "Llambda" =>
        match t with
        | .arrow a b =>
          match getArr j "binders" with
          | .error e => .error e
          | .ok bs =>
            match bs.toList with
            | [bd] =>
              match getNat bd "stamp", getStr bd "name" with
              | .ok st, .ok nm =>
                match _hbl : F.bindLocal st nm with
                | .error e => .error e
                | .ok F' =>
                  match _hlb : getObj j "body" with
                  | .error e => .error e
                  | .ok body =>
                    match decodeTerm F' b body with
                    | .error e => .error e
                    | .ok e => .ok (.lam a (F.localBindName st nm) e)
              | _, _ =>
                fail s!"a lambda binder without a stamp and a name in {j.compress}"
            | bds =>
              fail s!"a lambda over {bds.length} binders in {j.compress}: the term \
                layer builds a function one binder at a time"
        | _ =>
          fail s!"a lambda in {j.compress} where the context expects \
            {repr t}, which is not an arrow code"
      -- `forall` and `exists` at `bool` are propositions EasyCrypt writes where
      -- a value is expected, and `EcTerm.forallB` / `.existsB` are their images.
      -- The binders are bound in one pass and the body is decoded once under
      -- all of them, so the decoder makes a single recursive call.
      | .ok q =>
        if q == "Lforall" || q == "Lexists" then
          match t with
          | .bool =>
            match getArr j "binders" with
            | .error e => .error e
            | .ok bs =>
              match _hqb : bindTermBinders F bs.toList with
              | .error e => .error e
              | .ok (ls, xs) =>
                match _hqbody : getObj j "body" with
                | .error e => .error e
                | .ok body =>
                  match decodeTerm { F with locals := ls } .bool body with
                  | .error e => .error e
                  | .ok be => .ok (wrapQuantTerm (q == "Lforall") xs be)
          | _ =>
            fail s!"a quantified term in {j.compress} where the context expects \
              {repr t}: an EasyCrypt quantifier is a proposition, which is a \
              value of bool"
        else
          fail s!"the quantifier '{q}' in term position in {j.compress}: EcTerm \
            has no binder of that sort"
      | .error e => .error e
    else if kind = "Fpr" then
      fail s!"probability in term position in {j.compress}: a probability is an \
        EcProb, not an EcTerm"
    else if judgementKinds.contains kind then
      fail s!"the judgement '{kind}' in term position in {j.compress}: a \
        judgement is an EcForm, not an EcTerm"
    else if kind = "Unsupported" then fail (unsupportedMsg j)
    else
      match checkNodeTy F.tables t j with
      | .error e => .error e
      | .ok () =>
        if kind = "Fint" then
          match t with
          | .int =>
            match getStr j "value" with
            | .error e => .error e
            | .ok s =>
              match s.toInt? with
              | none => fail s!"integer term '{s}' is not a decimal integer"
              | some v => .ok (.lit v)
          | _ =>
            fail s!"integer term at type {repr t} in {j.compress}: an integer \
              literal has an EcTerm image at the int code only"
        else if kind = "Flocal" then
          match localNameOf F j with
          | .error e => .error e
          | .ok x => .ok (.var t x)
        else if kind = "Fop" then
          match getStr j "path" with
          | .error e => .error e
          | .ok p =>
            -- The canonical nullary values, at the codes that have one. These are
            -- the tables the expression layer reads at an `Eop`, so the two
            -- layers give the same path the same value.
            if F.tables.emptyMapPaths.contains p then
              match t with
              | .map _ _ => .ok (.lit [])
              | _ =>
                fail s!"the empty finite map '{p}' at type {repr t}: only a map \
                  code has one"
            else if F.tables.emptyFsetPaths.contains p then
              match t with
              | .fset a => .ok (.lit (EcTy.fsetEmpty (a := a)))
              | _ =>
                fail s!"the empty finite set '{p}' at type {repr t}: only an \
                  fset code has one"
            else if F.tables.emptyListPaths.contains p then
              match t with
              | .list a => .ok (.lit (EcTy.listEmpty (a := a)))
              | _ =>
                fail s!"the empty list '{p}' at type {repr t}: only a list code \
                  has one"
            else if F.tables.nonePaths.contains p then
              match t with
              | .option a => .ok (.lit (EcTy.noneVal (a := a)))
              | _ =>
                fail s!"'{p}' at type {repr t}: only an option code has an \
                  absent value"
            else if F.tables.witnessPaths.contains p then
              .ok (.lit default)
            -- `finite_type` and `predT` are nullary reads whose meaning comes
            -- from `Finite.ec` and `Logic.ec` rather than from a table entry:
            -- the first takes its type by type argument, the second is the
            -- constant-true predicate and is read where a predicate is passed.
            else if F.paths.finiteTypeOps.contains p then
              match t, nullaryTargs j with
              | .bool, [aJ] =>
                match decodeTy F.tables aJ with
                | .error e => .error e
                | .ok a => .ok (.finiteType a)
              | .bool, ts =>
                fail s!"'{p}' read with {ts.length} type argument(s) in \
                  {j.compress}: finiteness is asserted of one carrier"
              | _, _ =>
                fail s!"'{p}' at type {repr t}: whether a carrier is enumerated \
                  by a list is a boolean"
            else if F.paths.predTOps.contains p then
              match t with
              | .arrow a .bool =>
                .ok (.lam a (p ++ "#1") (.lit (t := .bool) true))
              | _ =>
                fail s!"'{p}' at type {repr t}: the predicate every value \
                  satisfies is a function into bool"
            else
            match List.lookup p F.tables.constPaths with
            | none =>
              -- An abstract operator declared by the theory the statement comes
              -- from is a parameter of the statement, read at the signature its
              -- declaration gives it. Only a nullary declaration registers, so
              -- the argument is the unit literal.
              match List.lookup p F.tables.absOpPaths with
              | some s =>
                if harg : s.arg = EcTy.unit then
                  if hres : s.res = t then
                    .ok (EcTerm.castTy hres
                      (.opApp p s (EcTerm.castTy harg.symm (.lit (t := .unit) ()))))
                  else
                    fail s!"the abstract operator '{p}' is declared at result \
                      type {repr s.res}, context expects {repr t}"
                else
                  -- An abstract operator read with no argument is being passed
                  -- as a function, which is how `iterop` and the `big` family
                  -- take their operator. `opApp` takes its arguments as a
                  -- right-nested product, so the reading is one lambda per
                  -- argument over an application at the product of them. The
                  -- binder names carry a `#`, which no source identifier holds,
                  -- so neither can capture a variable the statement binds.
                  let n1 := p ++ "#1"
                  let n2 := p ++ "#2"
                  let n3 := p ++ "#3"
                  match t with
                  | .arrow a (.arrow b (.arrow c r)) =>
                    if h1 : s.arg = EcTy.prod a (.prod b c) then
                      if h2 : s.res = r then
                        .ok (.lam a n1 (.lam b n2 (.lam c n3
                          (EcTerm.castTy h2 (.opApp p s
                            (EcTerm.castTy h1.symm
                              (.pair (.var a n1)
                                (.pair (.var b n2) (.var c n3)))))))))
                      else
                        fail s!"the abstract operator '{p}' is declared at result \
                          type {repr s.res} and read as a function returning \
                          {repr r}"
                    else
                      fail s!"the abstract operator '{p}' is declared at argument \
                        type {repr s.arg} and read as a function of three \
                        arguments nesting as {repr (EcTy.prod a (EcTy.prod b c))}"
                  | .arrow a (.arrow b c) =>
                    if h1 : s.arg = EcTy.prod a b then
                      if h2 : s.res = c then
                        .ok (.lam a n1 (.lam b n2
                          (EcTerm.castTy h2 (.opApp p s
                            (EcTerm.castTy h1.symm
                              (.pair (.var a n1) (.var b n2)))))))
                      else
                        fail s!"the abstract operator '{p}' is declared at result \
                          type {repr s.res} and read as a function returning \
                          {repr c}"
                    else if h1 : s.arg = a then
                      if h2 : s.res = EcTy.arrow b c then
                        .ok (.lam a n1 (EcTerm.castTy h2 (.opApp p s
                          (EcTerm.castTy h1.symm (.var a n1)))))
                      else
                        fail s!"the abstract operator '{p}' is declared at result \
                          type {repr s.res} and read as a function returning \
                          {repr (EcTy.arrow b c)}"
                    else
                      fail s!"the abstract operator '{p}' is declared at argument \
                        type {repr s.arg} and read as a function of {repr a} and \
                        {repr b}"
                  | .arrow a b =>
                    if h1 : s.arg = a then
                      if h2 : s.res = b then
                        .ok (.lam a n1 (EcTerm.castTy h2 (.opApp p s
                          (EcTerm.castTy h1.symm (.var a n1)))))
                      else
                        fail s!"the abstract operator '{p}' is declared at result \
                          type {repr s.res} and read as a function returning \
                          {repr b}"
                    else
                      fail s!"the abstract operator '{p}' is declared at argument \
                        type {repr s.arg} and read as a function of {repr a}"
                  | _ =>
                    fail s!"the abstract operator '{p}' is declared at argument \
                      type {repr s.arg} and read with no argument"
              | none =>
                -- A concrete declaration of the theory the statement comes from
                -- is a definition, read as the term it abbreviates. The body is
                -- decoded against the tables with this definition dropped.
                --
                -- A definition read with no argument is being passed as a
                -- function, and `EcTy.arrow` is the code it is read at: the
                -- reading is one lambda per parameter over the body, with each
                -- parameter bound to the lambda's own variable. The binder names
                -- carry a `#`, which no source identifier holds, so neither can
                -- capture a variable the statement binds.
                match _hdc : List.lookup p F.tables.defOpPaths with
                | some d =>
                  let n1 := p ++ "#1"
                  let n2 := p ++ "#2"
                  match d.params, t with
                  | [], t' =>
                    match decodeTerm (F.withoutDefOp p) t' d.body with
                    | .ok e => .ok e
                    | .error m =>
                      fail s!"the operator '{p}' is defined by a term that does \
                        not decode: {m}"
                  | [(x, u)], .arrow a c =>
                    if hu : u = a then
                      if hres : d.res = c then
                        match _hb1 : bindOpParams (F.withoutDefOp p) p d.params with
                        | .error e => .error e
                        | .ok F' =>
                          match decodeTerm F' d.res d.body with
                          | .error m =>
                            fail s!"the operator '{p}' is defined by a term that \
                              does not decode: {m}"
                          | .ok be =>
                            .ok (.lam a n1
                              (wrapOpLets
                                [(opParamName x,
                                  ⟨u, EcTerm.castTy hu.symm (.var a n1)⟩)]
                                (EcTerm.castTy hres be)))
                      else
                        fail s!"the operator '{p}' is defined at result type \
                          {repr d.res} and read as a function returning {repr c}"
                    else
                      fail s!"the operator '{p}' is defined at parameter type \
                        {repr u} and read as a function of {repr a}"
                  | [(x, u), (y, w)], .arrow a (.arrow b c) =>
                    if hu : u = a then
                      if hw : w = b then
                        if hres : d.res = c then
                          match _hb2 : bindOpParams (F.withoutDefOp p) p d.params with
                          | .error e => .error e
                          | .ok F' =>
                            match decodeTerm F' d.res d.body with
                            | .error m =>
                              fail s!"the operator '{p}' is defined by a term \
                                that does not decode: {m}"
                            | .ok be =>
                              .ok (.lam a n1 (.lam b n2
                                (wrapOpLets
                                  [(opParamName x,
                                    ⟨u, EcTerm.castTy hu.symm (.var a n1)⟩),
                                   (opParamName y,
                                    ⟨w, EcTerm.castTy hw.symm (.var b n2)⟩)]
                                  (EcTerm.castTy hres be))))
                        else
                          fail s!"the operator '{p}' is defined at result type \
                            {repr d.res} and read as a function returning \
                            {repr c}"
                      else
                        fail s!"the operator '{p}' is defined at second \
                          parameter type {repr w} and read as a function of \
                          {repr b}"
                    else
                      fail s!"the operator '{p}' is defined at parameter type \
                        {repr u} and read as a function of {repr a}"
                  | ps, _ =>
                    fail s!"the operator '{p}' is defined with {ps.length} \
                      parameter(s) and read at type {repr t}, which is not an \
                      arrow code of that many arguments"
                | none =>
                  fail s!"unknown nullary operator path '{p}' in {j.compress}: the \
                    ingestion's constant table has no entry and no operator \
                    declaration registers the path, so the operator has no \
                    EcTerm image"
            | some v =>
              if h : v.ty = t then .ok (.lit (v.transport h))
              else
                fail s!"constant '{p}' has type {repr v.ty}, context expects \
                  {repr t}"
        else if kind = "Fpvar" then
          match getObj j "pv" with
          | .error e => .error e
          | .ok pvJ =>
            match getStr pvJ "kind" with
            | .error e => .error e
            | .ok "PVloc" =>
              match getStr pvJ "name" with
              | .error e => .error e
              | .ok x =>
                if x = F.paths.resName then
                  match memRefOf F j "mem" with
                  | .error e => .error e
                  | .ok (.side s) => .ok (.res t s)
                  | .ok (.named m) =>
                    fail s!"'res' read at the quantified memory '{m}': the \
                      result is bound by a judgement, not by a memory quantifier"
                else
                  fail s!"the procedure-local program variable '{x}' read at a \
                    memory in {j.compress}: a local is not heap state, so it has \
                    no EcTerm image"
            | .ok "PVglob" =>
              match getStr pvJ "xpath" with
              | .error e => .error e
              | .ok q =>
                match List.lookup q F.tables.globals with
                | none =>
                  fail s!"read of the unknown global '{q}': the ingestion's \
                    global table has no location for it"
                | some g =>
                  match memRefOf F j "mem" with
                  | .error e => .error e
                  | .ok m =>
                    if h : g.ty = t then .ok (EcTerm.castTy h (.glob g m))
                    else
                      fail s!"global '{q}' is declared at type {repr g.ty} and \
                        read at {repr t}"
            | .ok k => fail s!"unknown program-variable kind '{k}' in {pvJ.compress}"
        else if kind = "Ftuple" then
          match t with
          | .prod a b =>
            match _htup : getArr j "args" with
            | .error e => .error e
            | .ok arr =>
              -- A tuple of more than two components is the right-nested pair its
              -- code already is: `decodeTy` nests an n-ary `Ttuple` as
              -- `t₁ × (t₂ × … × tₙ)`, so the components decode against the
              -- code's own spine.
              match arr.toList.attach with
              | [⟨x, _⟩, ⟨y, _⟩] =>
                match decodeTerm F a x with
                | .error e => .error e
                | .ok xe =>
                  match decodeTerm F b y with
                  | .error e => .error e
                  | .ok ye => .ok (.pair xe ye)
              | [⟨x, _⟩, ⟨y, _⟩, ⟨z, _⟩] =>
                match b with
                | .prod b1 b2 =>
                  match decodeTerm F a x with
                  | .error e => .error e
                  | .ok xe =>
                    match decodeTerm F b1 y with
                    | .error e => .error e
                    | .ok ye =>
                      match decodeTerm F b2 z with
                      | .error e => .error e
                      | .ok ze => .ok (.pair xe (.pair ye ze))
                | _ =>
                  fail s!"tuple of 3 components at the code {repr t}, whose \
                    second component is not itself a product"
              | [⟨x, _⟩, ⟨y, _⟩, ⟨z, _⟩, ⟨w, _⟩] =>
                match b with
                | .prod b1 (.prod b2 b3) =>
                  match decodeTerm F a x with
                  | .error e => .error e
                  | .ok xe =>
                    match decodeTerm F b1 y with
                    | .error e => .error e
                    | .ok ye =>
                      match decodeTerm F b2 z with
                      | .error e => .error e
                      | .ok ze =>
                        match decodeTerm F b3 w with
                        | .error e => .error e
                        | .ok we => .ok (.pair xe (.pair ye (.pair ze we)))
                | _ =>
                  fail s!"tuple of 4 components at the code {repr t}, whose \
                    spine is not three nested products"
              | _ =>
                fail s!"tuple of {arr.size} components: the decoder nests two, \
                  three and four against the code's own spine"
          | _ => fail s!"tuple at type {repr t}: only a prod code has one"
        else if kind = "Fproj" then
          match _htgt : getObj j "target" with
          | .error e => .error e
          | .ok tgtJ =>
            match decodeTyField F.tables tgtJ "ty" with
            | .error e => .error e
            | .ok pty =>
              match getNat j "index" with
              | .error e => .error e
              | .ok idx =>
                match pty with
                | .prod a b =>
                  match decodeTerm F (.prod a b) tgtJ with
                  | .error e => .error e
                  | .ok pe =>
                    match idx with
                    | 0 =>
                      if h : a = t then .ok (EcTerm.castTy h (.fst pe))
                      else
                        fail s!"first projection has type {repr a}, context \
                          expects {repr t}"
                    | 1 =>
                      if h : b = t then .ok (EcTerm.castTy h (.snd pe))
                      else
                        fail s!"second projection has type {repr b}, context \
                          expects {repr t}"
                    | _ => fail s!"projection index {idx} on a binary product"
                | _ =>
                  fail s!"projection target has type {repr pty}, which is not a \
                    product"
        else if kind = "Fif" then
          match _htc : getObj j "cond" with
          | .error e => .error e
          | .ok cJ =>
            match _htt : getObj j "then" with
            | .error e => .error e
            | .ok tJ =>
              match _hte : getObj j "else" with
              | .error e => .error e
              | .ok eJ =>
                match decodeTerm F .bool cJ with
                | .error e => .error e
                | .ok ce =>
                  match decodeTerm F t tJ with
                  | .error e => .error e
                  | .ok te =>
                    match decodeTerm F t eJ with
                    | .error e => .error e
                    | .ok ee => .ok (.ite ce te ee)
        else if kind = "Flet" then
          match getObj j "pat" with
          | .error e => .error e
          | .ok patJ =>
            match getStr patJ "kind" with
            | .error e => .error e
            | .ok "LSymbol" =>
              match getObj patJ "binder" with
              | .error e => .error e
              | .ok bJ =>
                match getStr bJ "name" with
                | .error e => .error e
                | .ok nm =>
                  match getNat bJ "stamp" with
                  | .error e => .error e
                  | .ok st =>
                    match decodeTyField F.tables bJ "ty" with
                    | .error e => .error e
                    | .ok t' =>
                      match _htbl : F.bindLocal st nm with
                      | .error e => .error e
                      | .ok F' =>
                        match _htv : getObj j "value" with
                        | .error e => .error e
                        | .ok vJ =>
                          match _htb : getObj j "body" with
                          | .error e => .error e
                          | .ok bodyJ =>
                            match decodeTerm F t' vJ with
                            | .error e => .error e
                            | .ok ve =>
                              match decodeTerm F' t bodyJ with
                              | .error e => .error e
                              | .ok be => .ok (.letIn nm ve be)
            | .ok "LTuple" =>
              fail s!"tuple let pattern in {j.compress}: EcTerm.letIn binds a \
                single variable"
            | .ok k => fail s!"unsupported let pattern kind '{k}' in {patJ.compress}"
        -- `support d x` and `omap f o` are read ahead of the operator tables:
        -- each path also carries an operator declaration whose body is outside
        -- the fragment, and the primitive image is the one to take. The element
        -- code comes off the argument's own type field, which the result — a
        -- boolean for `support`, the image option for `omap` — does not fix.
        else if isAppOfAny F.paths.supportOps j then
          match appHeadPath j, t with
          | .error e, _ => .error e
          | .ok p, .bool =>
            match _hsup : getArr j "args" with
            | .error e => .error e
            | .ok arr =>
              match arr.toList.attach with
              | [⟨dJ, _⟩, ⟨xJ, _⟩] =>
                match decodeTyField F.tables dJ "ty" with
                | .error e => .error e
                | .ok (.distr a) =>
                  match decodeTerm F (.distr a) dJ with
                  | .error e => .error e
                  | .ok de =>
                    match decodeTerm F a xJ with
                    | .error e => .error e
                    | .ok xe => .ok (.support de xe)
                | .ok u =>
                  fail s!"'{p}' is applied to a value of type {repr u}, which \
                    is not a distribution"
              | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
          | .ok p, _ =>
            fail s!"'{p}' at type {repr t}: membership in a distribution's \
              support is a boolean"
        else if isAppOfAny F.paths.optionMapOps j then
          match appHeadPath j, t with
          | .error e, _ => .error e
          | .ok p, .option b =>
            match _homap : getArr j "args" with
            | .error e => .error e
            | .ok arr =>
              match arr.toList.attach with
              | [⟨fJ, _⟩, ⟨oJ, _⟩] =>
                match decodeTyField F.tables oJ "ty" with
                | .error e => .error e
                | .ok (.option a) =>
                  match decodeTerm F (.arrow a b) fJ with
                  | .error e => .error e
                  | .ok fe =>
                    match decodeTerm F (.option a) oJ with
                    | .error e => .error e
                    | .ok oe => .ok (.optionMap fe oe)
                | .ok u =>
                  fail s!"'{p}' is applied to a value of type {repr u}, which \
                    is not an option"
              | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
          | .ok p, _ =>
            fail s!"'{p}' at type {repr t}: the image of an option is an option"
        -- `dmap`, `dlet` and `to_seq` are read ahead of the operator tables for
        -- the same reason as `support`: each also carries an operator
        -- declaration whose body is outside the fragment. The source code of a
        -- distribution argument comes off that argument's own type field, which
        -- the result code does not fix; `to_seq`'s element code does come off
        -- the result, which is a list at it.
        else if isAppOfAny F.paths.distrMapOps j then
          match appHeadPath j, t with
          | .error e, _ => .error e
          | .ok p, .distr b =>
            match _hdm : getArr j "args" with
            | .error e => .error e
            | .ok arr =>
              match arr.toList.attach with
              | [⟨dJ, _⟩, ⟨fJ, _⟩] =>
                match decodeTyField F.tables dJ "ty" with
                | .error e => .error e
                | .ok (.distr a) =>
                  match decodeTerm F (.distr a) dJ with
                  | .error e => .error e
                  | .ok de =>
                    match decodeTerm F (.arrow a b) fJ with
                    | .error e => .error e
                    | .ok fe => .ok (.distrMap de fe)
                | .ok u =>
                  fail s!"'{p}' is applied to a value of type {repr u}, which \
                    is not a distribution"
              | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
          | .ok p, _ =>
            fail s!"'{p}' at type {repr t}: the pushforward of a distribution \
              along a function is a distribution"
        else if isAppOfAny F.paths.distrLetOps j then
          match appHeadPath j, t with
          | .error e, _ => .error e
          | .ok p, .distr b =>
            match _hdl : getArr j "args" with
            | .error e => .error e
            | .ok arr =>
              match arr.toList.attach with
              | [⟨dJ, _⟩, ⟨fJ, _⟩] =>
                match decodeTyField F.tables dJ "ty" with
                | .error e => .error e
                | .ok (.distr a) =>
                  match decodeTerm F (.distr a) dJ with
                  | .error e => .error e
                  | .ok de =>
                    match decodeTerm F (.arrow a (.distr b)) fJ with
                    | .error e => .error e
                    | .ok fe => .ok (.distrLet de fe)
                | .ok u =>
                  fail s!"'{p}' is applied to a value of type {repr u}, which \
                    is not a distribution"
              | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
          | .ok p, _ =>
            fail s!"'{p}' at type {repr t}: the bind of a distribution with a \
              distribution-valued function is a distribution"
        else if isAppOfAny F.paths.toSeqOps j then
          match appHeadPath j, t with
          | .error e, _ => .error e
          | .ok p, .list a =>
            match _hts : getArr j "args" with
            | .error e => .error e
            | .ok arr =>
              match arr.toList.attach with
              | [⟨pJ, _⟩] =>
                match decodeTerm F (.arrow a .bool) pJ with
                | .error e => .error e
                | .ok pe => .ok (.toSeq pe)
              | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 1"
          | .ok p, _ =>
            fail s!"'{p}' at type {repr t}: the values a predicate holds of are \
              a list"
        -- List catenation, the independent product of two distributions and a
        -- distribution conditioned on avoiding a predicate are read ahead of the
        -- operator tables for the reason `support` is: each also carries an
        -- operator declaration whose body is outside the fragment.
        else if isAppOfAny F.paths.listCatOps j then
          match appHeadPath j, t with
          | .error e, _ => .error e
          | .ok p, .list a =>
            match _hcat : getArr j "args" with
            | .error e => .error e
            | .ok arr =>
              match arr.toList.attach with
              | [⟨xJ, _⟩, ⟨yJ, _⟩] =>
                match decodeTerm F (.list a) xJ with
                | .error e => .error e
                | .ok xe =>
                  match decodeTerm F (.list a) yJ with
                  | .error e => .error e
                  | .ok ye => .ok (.listCat xe ye)
              | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
          | .ok p, _ =>
            fail s!"'{p}' at type {repr t}: the catenation of two lists is a \
              list"
        else if isAppOfAny F.paths.distrProdOps j then
          match appHeadPath j, t with
          | .error e, _ => .error e
          | .ok p, .distr (.prod a b) =>
            match _hdpr : getArr j "args" with
            | .error e => .error e
            | .ok arr =>
              match arr.toList.attach with
              | [⟨xJ, _⟩, ⟨yJ, _⟩] =>
                match decodeTerm F (.distr a) xJ with
                | .error e => .error e
                | .ok xe =>
                  match decodeTerm F (.distr b) yJ with
                  | .error e => .error e
                  | .ok ye => .ok (.distrProd xe ye)
              | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
          | .ok p, _ =>
            fail s!"'{p}' at type {repr t}: the independent product of two \
              distributions is a distribution over pairs"
        else if isAppOfAny F.paths.distrExceptOps j then
          match appHeadPath j, t with
          | .error e, _ => .error e
          | .ok p, .distr a =>
            match _hdex : getArr j "args" with
            | .error e => .error e
            | .ok arr =>
              match arr.toList.attach with
              | [⟨dJ, _⟩, ⟨pJ, _⟩] =>
                match decodeTerm F (.distr a) dJ with
                | .error e => .error e
                | .ok de =>
                  match decodeTerm F (.arrow a .bool) pJ with
                  | .error e => .error e
                  | .ok pe => .ok (.distrExcept de pe)
              | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
          | .ok p, _ =>
            fail s!"'{p}' at type {repr t}: a distribution conditioned on \
              avoiding a predicate is a distribution"
        -- `dom` and `m.[k]` at the spellings `FMap.ec`'s own statements write
        -- them under. The key code comes off the map argument's own type field;
        -- `dom` read at one argument is the predicate its definition
        -- `dom m = fun x => m.[x] <> None` gives, as a lambda over the key.
        else if isAppOfAny F.paths.mapDomOps j then
          match appHeadPath j, t with
          | .error e, _ => .error e
          | .ok p, .bool =>
            match _hdom2 : getArr j "args" with
            | .error e => .error e
            | .ok arr =>
              match arr.toList.attach with
              | [⟨mJ, _⟩, ⟨kJ, _⟩] =>
                match decodeTyField F.tables mJ "ty" with
                | .error e => .error e
                | .ok (.map a b) =>
                  match decodeTerm F (.map a b) mJ with
                  | .error e => .error e
                  | .ok me =>
                    match decodeTerm F a kJ with
                    | .error e => .error e
                    | .ok ke => .ok (.mapMem me ke)
                | .ok u =>
                  fail s!"'{p}' is applied to a value of type {repr u}, which \
                    is not a finite map"
              | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
          | .ok p, .arrow a .bool =>
            match _hdom1 : getArr j "args" with
            | .error e => .error e
            | .ok arr =>
              match arr.toList.attach with
              | [⟨mJ, _⟩] =>
                match decodeTyField F.tables mJ "ty" with
                | .error e => .error e
                | .ok (.map a' b) =>
                  if hk : a' = a then
                    match decodeTerm F (.map a' b) mJ with
                    | .error e => .error e
                    | .ok me =>
                      .ok (.lam a (p ++ "#1")
                        (.mapMem me
                          (EcTerm.castTy hk.symm (.var a (p ++ "#1")))))
                  else
                    fail s!"'{p}' reads a map keyed by {repr a'}, context \
                      expects a predicate on {repr a}"
                | .ok u =>
                  fail s!"'{p}' is applied to a value of type {repr u}, which \
                    is not a finite map"
              | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 1"
          | .ok p, _ =>
            fail s!"'{p}' at type {repr t}: whether a key is bound in a finite \
              map is a boolean"
        else if isAppOfAny F.paths.mapLookupOps j then
          match appHeadPath j, t with
          | .error e, _ => .error e
          | .ok p, .option b =>
            match _hlk : getArr j "args" with
            | .error e => .error e
            | .ok arr =>
              match arr.toList.attach with
              | [⟨mJ, _⟩, ⟨kJ, _⟩] =>
                match decodeTyField F.tables mJ "ty" with
                | .error e => .error e
                | .ok (.map a b') =>
                  if hb : b' = b then
                    match decodeTerm F (.map a b') mJ with
                    | .error e => .error e
                    | .ok me =>
                      match decodeTerm F a kJ with
                      | .error e => .error e
                      | .ok ke =>
                        .ok (EcTerm.castTy (congrArg EcTy.option hb)
                          (.mapFind me ke))
                  else
                    fail s!"'{p}' reads a map of values of type {repr b'}, \
                      context expects an option of {repr b}"
                | .ok u =>
                  fail s!"'{p}' is applied to a value of type {repr u}, which \
                    is not a finite map"
              | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
          | .ok p, _ =>
            fail s!"'{p}' at type {repr t}: the binding of a key in a finite \
              map is an option"
        else if kind = "Fapp" then
          match _hfh : getObj j "f" with
          | .error e => .error e
          | .ok fJ =>
            match getStr fJ "kind" with
            | .error e => .error e
            | .ok "Fop" =>
              match getStr fJ "path" with
              | .error e => .error e
              | .ok p =>
                match List.lookup p F.tables.opPaths with
                | none =>
                  -- An abstract operator declared by the theory the statement
                  -- comes from is a parameter of the statement, applied at the
                  -- signature its declaration gives it. The argument count comes
                  -- from the application and the argument codes from the
                  -- declaration, so an argument list whose types do not nest
                  -- into the declared argument code is a mismatch between the
                  -- two and is named as one.
                  match List.lookup p F.tables.absOpPaths with
                  | some s =>
                    if hres : s.res = t then
                      match _hoa : getArr j "args" with
                      | .error e => .error e
                      | .ok arr =>
                        match arr.toList.attach.mapM (fun ⟨x, _⟩ =>
                            match decodeTyField F.tables x "ty" with
                            | .error e => Except.error e
                            | .ok u =>
                              match decodeTerm F u x with
                              | .error e => Except.error e
                              | .ok xe => Except.ok (Sigma.mk u xe)) with
                        | .error e => .error e
                        | .ok [] =>
                          fail s!"the abstract operator '{p}' is applied to no \
                            arguments in {j.compress}"
                        | .ok (a :: rest) =>
                          let n := EcTerm.nestArgs a rest
                          if harg : n.1 = s.arg then
                            .ok (EcTerm.castTy hres
                              (.opApp p s (EcTerm.castTy harg n.2)))
                          else
                            fail s!"the abstract operator '{p}' is declared at \
                              argument type {repr s.arg} and applied to \
                              {arr.size} arguments, whose types nest as \
                              {repr n.1}"
                    else
                      -- Read at an arrow spine ending in the declared result,
                      -- the operator is partially applied: the arguments written
                      -- here, and a lambda for each one still missing. The two
                      -- together nest into the declared argument code, which is
                      -- the right-nested product of every argument.
                      match t with
                      | .arrow b2 (.arrow b3 (.arrow b4 r)) =>
                        if hr : r = s.res then
                          match _hpa : getArr j "args" with
                          | .error e => .error e
                          | .ok arr =>
                            match arr.toList.attach.mapM (fun ⟨x, _⟩ =>
                                match decodeTyField F.tables x "ty" with
                                | .error e => Except.error e
                                | .ok u =>
                                  match decodeTerm F u x with
                                  | .error e => Except.error e
                                  | .ok xe => Except.ok (Sigma.mk u xe)) with
                            | .error e => .error e
                            | .ok [] =>
                              fail s!"the abstract operator '{p}' is applied to \
                                no arguments in {j.compress}"
                            | .ok (a :: rest) =>
                              let m2 := p ++ "#e2"
                              let m3 := p ++ "#e3"
                              let m4 := p ++ "#e4"
                              let full := EcTerm.nestArgs a
                                (rest ++ [⟨b2, .var b2 m2⟩, ⟨b3, .var b3 m3⟩,
                                          ⟨b4, .var b4 m4⟩])
                              if harg : full.1 = s.arg then
                                .ok (.lam b2 m2 (.lam b3 m3 (.lam b4 m4
                                  (EcTerm.castTy hr.symm
                                    (.opApp p s (EcTerm.castTy harg full.2))))))
                              else
                                fail s!"the abstract operator '{p}' is declared \
                                  at argument type {repr s.arg} and read applied \
                                  to {arr.size} arguments awaiting three, whose \
                                  types nest as {repr full.1}"
                        else
                          fail s!"the abstract operator '{p}' is declared at \
                            result type {repr s.res}, context expects {repr t}"
                      | _ =>
                        fail s!"the abstract operator '{p}' is declared at result \
                          type {repr s.res}, context expects {repr t}"
                  | none =>
                    -- A concrete declaration is a definition, and its read is
                    -- the body under one binder per parameter. The arguments are
                    -- decoded at the read site and the body against the tables
                    -- with this definition dropped, so a chain of reads is as
                    -- long as the table and no shorter measure is needed.
                    match _hda : List.lookup p F.tables.defOpPaths with
                    | none =>
                      fail s!"unknown operator path '{p}' applied in {j.compress}: \
                        the ingestion's operator table has no entry and no \
                        operator declaration registers the path, so the \
                        application has no EcTerm image"
                    | some d =>
                      if hres : d.res = t then
                        match _hdr : getArr j "args" with
                        | .error e => .error e
                        | .ok arr =>
                          match arr.toList.attach.mapM (fun ⟨x, _⟩ =>
                              match decodeTyField F.tables x "ty" with
                              | .error e => Except.error e
                              | .ok u =>
                                match decodeTerm F u x with
                                | .error e => Except.error e
                                | .ok xe => Except.ok (Sigma.mk u xe)) with
                          | .error e => .error e
                          | .ok vs =>
                            if vs.map Sigma.fst = d.params.map Prod.snd then
                              match _hbp : bindOpParams (F.withoutDefOp p) p d.params with
                              | .error e => .error e
                              | .ok F' =>
                                match decodeTerm F' d.res d.body with
                                | .error m =>
                                  fail s!"the operator '{p}' is defined by a \
                                    term that does not decode: {m}"
                                | .ok be =>
                                  .ok (EcTerm.castTy hres
                                    (wrapOpLets
                                      ((d.params.map (fun q => opParamName q.1)).zip vs)
                                      be))
                            else
                              fail s!"the operator '{p}' is defined at argument \
                                types {repr (d.params.map Prod.snd)} and applied \
                                to arguments of types \
                                {repr (vs.map Sigma.fst)}"
                        else
                          fail s!"the operator '{p}' is defined at result type \
                            {repr d.res}, context expects {repr t}"
                | some op =>
                  match _harr : getArr j "args" with
                  | .error e => .error e
                  | .ok arr =>
                    match op, t with
                    | .bnot, .bool =>
                      match arr.toList.attach with
                      | [⟨x, _⟩] =>
                        match decodeTerm F .bool x with
                        | .error e => .error e
                        | .ok xe => .ok (.bnot xe)
                      | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 1"
                    | .band, .bool =>
                      match arr.toList.attach with
                      | [⟨x, _⟩, ⟨y, _⟩] =>
                        match decodeTerm F .bool x with
                        | .error e => .error e
                        | .ok xe =>
                          match decodeTerm F .bool y with
                          | .error e => .error e
                          | .ok ye => .ok (.band xe ye)
                      | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
                    | .bxor, .bool =>
                      match arr.toList.attach with
                      | [⟨x, _⟩, ⟨y, _⟩] =>
                        match decodeTerm F .bool x with
                        | .error e => .error e
                        | .ok xe =>
                          match decodeTerm F .bool y with
                          | .error e => .error e
                          | .ok ye => .ok (.bxor xe ye)
                      | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
                    | .bor, .bool =>
                      match arr.toList.attach with
                      | [⟨x, _⟩, ⟨y, _⟩] =>
                        match decodeTerm F .bool x with
                        | .error e => .error e
                        | .ok xe =>
                          match decodeTerm F .bool y with
                          | .error e => .error e
                          | .ok ye => .ok (.bnot (.band (.bnot xe) (.bnot ye)))
                      | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
                    | .bimp, .bool =>
                      match arr.toList.attach with
                      | [⟨x, _⟩, ⟨y, _⟩] =>
                        match decodeTerm F .bool x with
                        | .error e => .error e
                        | .ok xe =>
                          match decodeTerm F .bool y with
                          | .error e => .error e
                          | .ok ye => .ok (.bnot (.band xe (.bnot ye)))
                      | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
                    | .beq, .bool =>
                      match arr.toList.attach with
                      | [⟨x, _⟩, ⟨y, _⟩] =>
                        match decodeTyField F.tables x "ty" with
                        | .error e => .error e
                        | .ok u =>
                          match decodeTerm F u x with
                          | .error e => .error e
                          | .ok xe =>
                            match decodeTerm F u y with
                            | .error e => .error e
                            | .ok ye => .ok (.beq xe ye)
                      | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
                    | .finAdd, .fin n hn =>
                      match arr.toList.attach with
                      | [⟨x, _⟩, ⟨y, _⟩] =>
                        match decodeTerm F (.fin n hn) x with
                        | .error e => .error e
                        | .ok xe =>
                          match decodeTerm F (.fin n hn) y with
                          | .error e => .error e
                          | .ok ye => .ok (.finAdd xe ye)
                      | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
                    | .intAdd, .int =>
                      match arr.toList.attach with
                      | [⟨x, _⟩, ⟨y, _⟩] =>
                        match decodeTerm F .int x with
                        | .error e => .error e
                        | .ok xe =>
                          match decodeTerm F .int y with
                          | .error e => .error e
                          | .ok ye => .ok (.intAdd xe ye)
                      | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
                    | .intMul, .int =>
                      match arr.toList.attach with
                      | [⟨x, _⟩, ⟨y, _⟩] =>
                        match decodeTerm F .int x with
                        | .error e => .error e
                        | .ok xe =>
                          match decodeTerm F .int y with
                          | .error e => .error e
                          | .ok ye => .ok (.intMul xe ye)
                      | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
                    | .intOpp, .int =>
                      match arr.toList.attach with
                      | [⟨x, _⟩] =>
                        match decodeTerm F .int x with
                        | .error e => .error e
                        | .ok xe => .ok (.intOpp xe)
                      | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 1"
                    | .intEdivz, .prod .int .int =>
                      match arr.toList.attach with
                      | [⟨x, _⟩, ⟨y, _⟩] =>
                        match decodeTerm F .int x with
                        | .error e => .error e
                        | .ok xe =>
                          match decodeTerm F .int y with
                          | .error e => .error e
                          | .ok ye => .ok (.intEdivz xe ye)
                      | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
                    | .intAbsz, .int =>
                      match arr.toList.attach with
                      | [⟨x, _⟩] =>
                        match decodeTerm F .int x with
                        | .error e => .error e
                        | .ok xe => .ok (.intAbsz xe)
                      | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 1"
                    | .intGcd, .int =>
                      match arr.toList.attach with
                      | [⟨x, _⟩, ⟨y, _⟩] =>
                        match decodeTerm F .int x with
                        | .error e => .error e
                        | .ok xe =>
                          match decodeTerm F .int y with
                          | .error e => .error e
                          | .ok ye => .ok (.intGcd xe ye)
                      | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
                    | .intLe, .bool =>
                      match arr.toList.attach with
                      | [⟨x, _⟩, ⟨y, _⟩] =>
                        match decodeTerm F .int x with
                        | .error e => .error e
                        | .ok xe =>
                          match decodeTerm F .int y with
                          | .error e => .error e
                          | .ok ye => .ok (.intLe xe ye)
                      | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
                    | .intMin, .int =>
                      -- The same reading the expression layer gives `min`, at
                      -- the same definition from `Int.ec`. Registering the path
                      -- in `opPaths` stops `defOpPaths` unfolding the source's
                      -- definition here, so this arm has to reproduce it or the
                      -- term layer would lose what it already reads.
                      match arr.toList.attach with
                      | [⟨x, _⟩, ⟨y, _⟩] =>
                        match decodeTerm F .int x with
                        | .error e => .error e
                        | .ok xe =>
                          match decodeTerm F .int y with
                          | .error e => .error e
                          | .ok ye => .ok (.ite (.bnot (.intLe ye xe)) xe ye)
                      | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
                    | .intMax, .int =>
                      match arr.toList.attach with
                      | [⟨x, _⟩, ⟨y, _⟩] =>
                        match decodeTerm F .int x with
                        | .error e => .error e
                        | .ok xe =>
                          match decodeTerm F .int y with
                          | .error e => .error e
                          | .ok ye => .ok (.ite (.bnot (.intLe ye xe)) ye xe)
                      | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
                    | .intLt, .bool =>
                      match arr.toList.attach with
                      | [⟨x, _⟩, ⟨y, _⟩] =>
                        match decodeTerm F .int x with
                        | .error e => .error e
                        | .ok xe =>
                          match decodeTerm F .int y with
                          | .error e => .error e
                          | .ok ye => .ok (.bnot (.intLe ye xe))
                      | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
                    | .mapMem, .bool =>
                      match arr.toList.attach with
                      | [⟨mJ, _⟩, ⟨kJ, _⟩] =>
                        match decodeTyField F.tables mJ "ty" with
                        | .error e => .error e
                        | .ok (.map a b) =>
                          match decodeTerm F (.map a b) mJ with
                          | .error e => .error e
                          | .ok me =>
                            match decodeTerm F a kJ with
                            | .error e => .error e
                            | .ok ke => .ok (.mapMem me ke)
                        | .ok u =>
                          fail s!"'{p}' is applied to a value of type {repr u}, \
                            which is not a finite map"
                      | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
                    -- `m.[k]` reads the key code off the map argument, which the
                    -- result — the value code as an option — does not fix, and
                    -- the value code from the result, which the two have to
                    -- agree on.
                    | .mapLookup, .option b =>
                      match arr.toList.attach with
                      | [⟨mJ, _⟩, ⟨kJ, _⟩] =>
                        match decodeTyField F.tables mJ "ty" with
                        | .error e => .error e
                        | .ok (.map a b') =>
                          if hb : b' = b then
                            match decodeTerm F (.map a b') mJ with
                            | .error e => .error e
                            | .ok me =>
                              match decodeTerm F a kJ with
                              | .error e => .error e
                              | .ok ke =>
                                .ok (EcTerm.castTy (congrArg EcTy.option hb)
                                  (.mapFind me ke))
                          else
                            fail s!"'{p}' reads a map of values of type \
                              {repr b'}, context expects an option of \
                              {repr b}"
                        | .ok u =>
                          fail s!"'{p}' is applied to a value of type {repr u}, \
                            which is not a finite map"
                      | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
                    -- `m.[k <- v]` returns a map, so the result code fixes both
                    -- the key and the value code.
                    | .mapSet, .map a b =>
                      match arr.toList.attach with
                      | [⟨mJ, _⟩, ⟨kJ, _⟩, ⟨vJ, _⟩] =>
                        match decodeTerm F (.map a b) mJ with
                        | .error e => .error e
                        | .ok me =>
                          match decodeTerm F a kJ with
                          | .error e => .error e
                          | .ok ke =>
                            match decodeTerm F b vJ with
                            | .error e => .error e
                            | .ok ve => .ok (.mapSet me ke ve)
                      | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 3"
                    | .listCons, .list a =>
                      match arr.toList.attach with
                      | [⟨xJ, _⟩, ⟨lJ, _⟩] =>
                        match decodeTerm F a xJ with
                        | .error e => .error e
                        | .ok xe =>
                          match decodeTerm F (.list a) lJ with
                          | .error e => .error e
                          | .ok le => .ok (.listCons xe le)
                      | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
                    | .listSize, .int =>
                      match arr.toList.attach with
                      | [⟨lJ, _⟩] =>
                        match decodeTyField F.tables lJ "ty" with
                        | .error e => .error e
                        | .ok (.list a) =>
                          match decodeTerm F (.list a) lJ with
                          | .error e => .error e
                          | .ok le => .ok (.listSize le)
                        | .ok u =>
                          fail s!"'{p}' is applied to a value of type {repr u}, \
                            which is not a list"
                      | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 1"
                    -- The combinators take their function argument first and the
                    -- list second, and the element code is read off the list
                    -- argument's own type field rather than the result's, which
                    -- for `all`, `has` and `count` does not mention it.
                    -- `choiceb P x0` has the type of its default, so the result
                    -- code fixes the predicate's argument code and no type field
                    -- has to be read.
                    -- `Logic.ec` writes `pred1 c x = (x = c)`, so a full read is
                    -- an equality and a read at one argument is the predicate
                    -- that equality gives, as a lambda over the other side.
                    | .pred1, .bool =>
                      match arr.toList.attach with
                      | [⟨cJ, _⟩, ⟨xJ, _⟩] =>
                        match decodeTyField F.tables cJ "ty" with
                        | .error e => .error e
                        | .ok a =>
                          match decodeTerm F a cJ with
                          | .error e => .error e
                          | .ok ce =>
                            match decodeTerm F a xJ with
                            | .error e => .error e
                            | .ok xe => .ok (.beq xe ce)
                      | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
                    | .pred1, .arrow a .bool =>
                      match arr.toList.attach with
                      | [⟨cJ, _⟩] =>
                        match decodeTerm F a cJ with
                        | .error e => .error e
                        | .ok ce => .ok (.lam a (p ++ "#1")
                            (.beq (.var a (p ++ "#1")) ce))
                      | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 1"
                    -- `iter` and `iterop` return the type they iterate over, so
                    -- the result code fixes every argument's code.
                    | .iter, u =>
                      match arr.toList.attach with
                      | [⟨nJ, _⟩, ⟨fJ, _⟩, ⟨xJ, _⟩] =>
                        match decodeTerm F .int nJ with
                        | .error e => .error e
                        | .ok ne =>
                          match decodeTerm F (.arrow u u) fJ with
                          | .error e => .error e
                          | .ok fe =>
                            match decodeTerm F u xJ with
                            | .error e => .error e
                            | .ok xe => .ok (.iter ne fe xe)
                      | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 3"
                    | .iterop, u =>
                      match arr.toList.attach with
                      | [⟨nJ, _⟩, ⟨oJ, _⟩, ⟨xJ, _⟩, ⟨zJ, _⟩] =>
                        match decodeTerm F .int nJ with
                        | .error e => .error e
                        | .ok ne =>
                          match decodeTerm F (.arrow u (.arrow u u)) oJ with
                          | .error e => .error e
                          | .ok oe =>
                            match decodeTerm F u xJ with
                            | .error e => .error e
                            | .ok xe =>
                              match decodeTerm F u zJ with
                              | .error e => .error e
                              | .ok ze => .ok (.iterop ne oe xe ze)
                      | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 4"
                    | .choiceb, u =>
                      match arr.toList.attach with
                      | [⟨pJ, _⟩, ⟨dJ, _⟩] =>
                        match decodeTerm F (.arrow u .bool) pJ with
                        | .error e => .error e
                        | .ok pe =>
                          match decodeTerm F u dJ with
                          | .error e => .error e
                          | .ok de => .ok (.choiceb pe de)
                      | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
                    -- `odflt d o` and `oget o`. The option is any term, and
                    -- `oget` takes the code's canonical inhabitant as its
                    -- default, which is what EasyCrypt's own `oget` answers on
                    -- an absent value.
                    | .mapOdflt, u =>
                      match arr.toList.attach with
                      | [⟨dJ, _⟩, ⟨oJ, _⟩] =>
                        match decodeTerm F (.option u) oJ with
                        | .error e => .error e
                        | .ok oe =>
                          match decodeTerm F u dJ with
                          | .error e => .error e
                          | .ok de => .ok (.optionGetD oe de)
                      | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
                    | .mapOget, u =>
                      match arr.toList.attach with
                      | [⟨oJ, _⟩] =>
                        match decodeTerm F (.option u) oJ with
                        | .error e => .error e
                        | .ok oe => .ok (.optionGetD oe (.lit default))
                      | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 1"
                    | .someE, .option a =>
                      match arr.toList.attach with
                      | [⟨xJ, _⟩] =>
                        match decodeTerm F a xJ with
                        | .error e => .error e
                        | .ok xe => .ok (.someT xe)
                      | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 1"
                    | .listUniq, .bool =>
                      match arr.toList.attach with
                      | [⟨lJ, _⟩] =>
                        match decodeTyField F.tables lJ "ty" with
                        | .error e => .error e
                        | .ok (.list a) =>
                          if !a.hasEq then
                            fail s!"'{p}' at the element type {repr a}: the test \
                              compares elements, and that type has no decidable \
                              equality"
                          else
                            match decodeTerm F (.list a) lJ with
                            | .error e => .error e
                            | .ok le => .ok (.listUniq le)
                        | .ok u =>
                          fail s!"'{p}' is applied to a value of type {repr u}, \
                            which is not a list"
                      | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 1"
                    | .listMap, .list b =>
                      match arr.toList.attach with
                      | [⟨fJ, _⟩, ⟨lJ, _⟩] =>
                        match decodeTyField F.tables lJ "ty" with
                        | .error e => .error e
                        | .ok (.list a) =>
                          match decodeTerm F (.arrow a b) fJ with
                          | .error e => .error e
                          | .ok fe =>
                            match decodeTerm F (.list a) lJ with
                            | .error e => .error e
                            | .ok le => .ok (.listMap fe le)
                        | .ok u =>
                          fail s!"'{p}' is applied to a value of type {repr u}, \
                            which is not a list"
                      | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
                    -- `foldr f z s` returns the type `z` has, and the element
                    -- code comes off the list argument, since the result does
                    -- not mention it.
                    | .listFoldr, u =>
                      match arr.toList.attach with
                      | [⟨fJ, _⟩, ⟨zJ, _⟩, ⟨lJ, _⟩] =>
                        match decodeTyField F.tables lJ "ty" with
                        | .error e => .error e
                        | .ok (.list a) =>
                          match decodeTerm F (.arrow a (.arrow u u)) fJ with
                          | .error e => .error e
                          | .ok fe =>
                            match decodeTerm F u zJ with
                            | .error e => .error e
                            | .ok ze =>
                              match decodeTerm F (.list a) lJ with
                              | .error e => .error e
                              | .ok le => .ok (.listFoldr fe ze le)
                        | .ok w =>
                          fail s!"'{p}' folds a value of type {repr w}, which is \
                            not a list"
                      | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 3"
                    | .listFilter, .list a =>
                      match arr.toList.attach with
                      | [⟨pJ, _⟩, ⟨lJ, _⟩] =>
                        match decodeTerm F (.arrow a .bool) pJ with
                        | .error e => .error e
                        | .ok pe =>
                          match decodeTerm F (.list a) lJ with
                          | .error e => .error e
                          | .ok le => .ok (.listFilter pe le)
                      | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
                    | .listAll, .bool =>
                      match arr.toList.attach with
                      | [⟨pJ, _⟩, ⟨lJ, _⟩] =>
                        match decodeTyField F.tables lJ "ty" with
                        | .error e => .error e
                        | .ok (.list a) =>
                          match decodeTerm F (.arrow a .bool) pJ with
                          | .error e => .error e
                          | .ok pe =>
                            match decodeTerm F (.list a) lJ with
                            | .error e => .error e
                            | .ok le => .ok (.listAll pe le)
                        | .ok u =>
                          fail s!"'{p}' is applied to a value of type {repr u}, \
                            which is not a list"
                      | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
                    | .listHas, .bool =>
                      match arr.toList.attach with
                      | [⟨pJ, _⟩, ⟨lJ, _⟩] =>
                        match decodeTyField F.tables lJ "ty" with
                        | .error e => .error e
                        | .ok (.list a) =>
                          match decodeTerm F (.arrow a .bool) pJ with
                          | .error e => .error e
                          | .ok pe =>
                            match decodeTerm F (.list a) lJ with
                            | .error e => .error e
                            | .ok le => .ok (.listHas pe le)
                        | .ok u =>
                          fail s!"'{p}' is applied to a value of type {repr u}, \
                            which is not a list"
                      | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
                    | .listCount, .int =>
                      match arr.toList.attach with
                      | [⟨pJ, _⟩, ⟨lJ, _⟩] =>
                        match decodeTyField F.tables lJ "ty" with
                        | .error e => .error e
                        | .ok (.list a) =>
                          match decodeTerm F (.arrow a .bool) pJ with
                          | .error e => .error e
                          | .ok pe =>
                            match decodeTerm F (.list a) lJ with
                            | .error e => .error e
                            | .ok le => .ok (.listCount pe le)
                        | .ok u =>
                          fail s!"'{p}' is applied to a value of type {repr u}, \
                            which is not a list"
                      | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
                    | .listMem, .bool =>
                      match arr.toList.attach with
                      | [⟨lJ, _⟩, ⟨xJ, _⟩] =>
                        match decodeTyField F.tables lJ "ty" with
                        | .error e => .error e
                        | .ok (.list a) =>
                          if !a.hasEq then
                            fail s!"'{p}' at the element type {repr a}: membership \
                              compares elements, and that type has no decidable \
                              equality"
                          else
                            match decodeTerm F (.list a) lJ with
                            | .error e => .error e
                            | .ok le =>
                              match decodeTerm F a xJ with
                              | .error e => .error e
                              | .ok xe => .ok (.listMem le xe)
                        | .ok u =>
                          fail s!"'{p}' is applied to a value of type {repr u}, \
                            which is not a list"
                      | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
                    | .fsetMem, .bool =>
                      match arr.toList.attach with
                      | [⟨sJ, _⟩, ⟨xJ, _⟩] =>
                        match decodeTyField F.tables sJ "ty" with
                        | .error e => .error e
                        | .ok (.fset a) =>
                          match decodeTerm F (.fset a) sJ with
                          | .error e => .error e
                          | .ok se =>
                            match decodeTerm F a xJ with
                            | .error e => .error e
                            | .ok xe => .ok (.fsetMem se xe)
                        | .ok u =>
                          fail s!"'{p}' is applied to a value of type {repr u}, \
                            which is not a finite set"
                      | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
                    | _, _ =>
                      fail s!"operator '{p}' cannot produce a value of type {repr t}"
            | .ok "Fquant" =>
              fail s!"application of a head of kind 'Fquant' in {j.compress}: a \
                lambda has no term image, so an application of one is not a term"
            | .ok _ =>
              match decodeTyField F.tables fJ "ty" with
              | .error e => .error e
              | .ok ft =>
                match decodeTerm F ft fJ with
                | .error e => .error e
                | .ok fe =>
                  match _hha : getArr j "args" with
                  | .error e => .error e
                  | .ok arr =>
                    match arr.toList.attach.mapM (fun ⟨x, _⟩ =>
                        match decodeTyField F.tables x "ty" with
                        | .error e => Except.error e
                        | .ok u =>
                          match decodeTerm F u x with
                          | .error e => Except.error e
                          | .ok xe => Except.ok (Sigma.mk u xe)) with
                    | .error e => .error e
                    | .ok vs =>
                      match applyArgs ⟨ft, fe⟩ vs with
                      | .error e => .error e
                      | .ok r =>
                        if h : r.1 = t then .ok (EcTerm.castTy h r.2)
                        else
                          fail s!"the application in {j.compress} has type \
                            {repr r.1}, context expects {repr t}"
        else
          fail s!"unsupported formula node kind '{kind}' in term position in \
            {j.compress}"
termination_by (F.tables.defOpPaths.length, jsonSize j)
decreasing_by
  all_goals first
    | exact Prod.Lex.right _
        (getArr_decreases (by assumption) (Array.mem_toList_iff.mp ‹_ ∈ Array.toList _›))
    | exact Prod.Lex.right _ (getObj_decreases (by assumption))
    | (rw [bindLocal_tables (by assumption)]
       exact Prod.Lex.right _ (getObj_decreases (by assumption)))
    | exact Prod.Lex.left _ _ (withoutDefOp_length_lt_of_eq _ _ (by assumption))
    | (rw [bindOpParams_tables (by assumption)]
       exact Prod.Lex.left _ _ (withoutDefOp_length_lt_of_eq _ _ (by assumption)))

/-! ## Footprint comparisons over a tuple

`={glob F(A)}` for a functor image compares a footprint that mixes the two
shapes: the abstract parameter's footprint, which stays a `Fglob` because its
module is a binder, and the concrete globals the functor body owns, which the
typechecker expands into one `Fpvar` per `var`. What reaches the export is
therefore an equality of two tuples, one component per part.

Each component is compared on its own, by the decoder the component's own shape
already has — `decodeGlobEq` for a `Fglob` pair and a term equality for an
expanded global — and the image is the conjunction of the component
comparisons, in the tuple's order. This is the form the two-conjunct source
`={glob A, glob M}` produces, so the two source spellings of one precondition
have one image. -/

/-- The components of a node, when the node is a tuple. -/
def tupleArgs (j : Json) : Option (List Json) :=
  match getStr j "kind" with
  | .ok "Ftuple" =>
    match getArr j "args" with
    | .ok a => some a.toList
    | .error _ => none
  | _ => none

/-- The componentwise operands of an equality whose two sides are tuples naming a
footprint. A `glob M` read in a component is what tells such a tuple from an
equality of two data tuples, which decodes as a term equality: `glob M` has no
type code, so a tuple carrying one is no term either, and this interception takes
nothing away from the term decoder. -/
def globTupleEqPair (args : Array Json) : Option (List Json × List Json) :=
  match args.toList with
  | [x, y] =>
    match tupleArgs x, tupleArgs y with
    | some xs, some ys =>
      if xs.any (fun c => (globIdentOf c).isSome)
          || ys.any (fun c => (globIdentOf c).isSome) then
        some (xs, ys)
      else none
    | _, _ => none
  | _ => none

/-- The comparison one component of a footprint tuple denotes: the footprint
comparison of `decodeGlobEq` when both sides are `glob M` reads, and equality of
the two terms otherwise. -/
def decodeGlobTupleComp (F : FormTables) (x y : Json) : Except String EcForm :=
  match (globIdentOf x).isSome, (globIdentOf y).isSome with
  | true, true => decodeGlobEq F x y
  | false, false => do
    let t ← decodeTyField F.tables x "ty"
    let a ← decodeTerm F t x
    let b ← decodeTerm F t y
    .ok (.eqT a b)
  | _, _ =>
    fail s!"the footprint components {x.compress} and {y.compress} are compared \
      with each other: one is a 'glob M' read and the other is not, so the two \
      sides of the comparison name different footprints"

/-- The conjunction of the componentwise comparisons of a footprint tuple. -/
def decodeGlobTupleEq (F : FormTables) : List Json → List Json →
    Except String EcForm
  | [], [] =>
    fail "an empty footprint tuple: a comparison of two empty tuples names no \
      footprint"
  | [x], [y] => decodeGlobTupleComp F x y
  | x :: xs, y :: ys => do
    let a ← decodeGlobTupleComp F x y
    let b ← decodeGlobTupleEq F xs ys
    .ok (.and a b)
  | xs, ys =>
    fail s!"a footprint tuple of {xs.length} components compared with one of \
      {ys.length}: the two sides name different footprints"

/-! ## Quantifier binders

A `Fquant` node carries a list of binders and one body. `bindBinders` walks the
list, extending the tables and building the chain of quantifier nodes the body
sits under, so the formula decoder makes a single recursive call, on the body.

A binder is bound under its source name, and under `freshLocalName` when another
live binder already carries that name. The two cases arise together: an expanded
definition's binders and the binders of the statement reading it are named
independently, and a definition quantifying over `x` read inside a statement
quantifying over its own `x` would otherwise be refused by
`FormTables.bindLocal`, whose check is what keeps a read of the outer `x` from
resolving to the inner binder. The occurrences carry the binder's stamp and
`localNameOf` resolves them through `locals`, so they read the name the binder
was bound under. -/

/-- The tables extended by one binder, and the quantifier node it wraps a formula
in.

A `GTmodty` binder's interface is looked up in `F.modTypes` by the name its
`ModuleType` node carries, and read from that node's own `sig` when the name is
absent. The node carries the signature with the type's arguments substituted in,
so the second route also serves a binder at a parameterised module type, whose
declaration `decodeModTypeInterface` rejects and which therefore never enters the
table.

A `GTmodty` binder's restriction is read in the scope enclosing the binder, so a
restriction against an outer module binder resolves against that binder rather
than against the ingestion's module table. The binder is quantified together with
its footprint when the body needs it: when the body compares `glob` of it, or
restricts a nested binder against it (`EcForm.needsFootprintOf`). -/
def bindBinder (F : FormTables) (q : String) (b : Json) :
    Except String (FormTables × (EcForm → EcForm)) := do
  let nm ← getStr b "name"
  let st ← getNat b "stamp"
  let g ← getObj b "gty"
  match ← getStr g "kind" with
  | "GTty" =>
    if tyConstrPath g "ty" == some F.paths.realTy then
      if q = "Lforall" then
        let F' ← F.bindLocal st (F.localBindName st nm)
        .ok (F', fun body => .allProb (F.localBindName st nm) body)
      else
        fail s!"the real-valued binder '{nm}' under '{q}': EcForm quantifies a \
          probability parameter universally only"
    else
      let t ← decodeTyField F.tables g "ty"
      if q = "Lforall" then
        let F' ← F.bindLocal st (F.localBindName st nm)
        .ok (F', fun body => .allTy t (F.localBindName st nm) body)
      else if q = "Lexists" then
        let F' ← F.bindLocal st (F.localBindName st nm)
        .ok (F', fun body => .exTy t (F.localBindName st nm) body)
      else
        fail s!"the lambda binder '{nm}' in a formula: EcForm has no lambda"
  | "GTmem" =>
    if q = "Lforall" then
      let F' ← F.bindMemName st nm
      .ok (F', fun body => .allMem nm body)
    else if q = "Lexists" then
      let F' ← F.bindMemName st nm
      .ok (F', fun body => .exMem nm body)
    else
      fail s!"the lambda binder '{nm}' over a memory: EcForm has no lambda"
  | "GTmodty" =>
    let mtJ ← getObj g "modtype"
    let mtName ← getStr mtJ "name"
    let I ←
      match List.lookup mtName F.modTypes with
      | some I => Except.ok I
      | none =>
        (decodeModTypeSig F.tables mtJ).mapError (fun m =>
          s!"the module type '{mtName}' is not in the ingestion's module-type \
            table, and its own signature does not decode: {m}")
    if q = "Lforall" then
      let r ← restrModules F g
      let F' := F.bindModBinder st nm I
      match r with
      | none =>
        .ok (F', fun body =>
          if body.needsFootprintOf nm then .allModOn nm I body else .allMod nm I body)
      | some r =>
        .ok (F', fun body =>
          if r.binders.isEmpty then
            if body.needsFootprintOf nm then .allModRestrOn nm I r.globals body
            else .allModRestr nm I r.globals body
          else
            if body.needsFootprintOf nm then .allModRestrOfOn nm I r body
            else .allModRestrOf nm I r body)
    else
      fail s!"the module binder '{nm}' under '{q}': EcForm quantifies a module \
        universally only"
  | k => fail s!"unknown binder sort '{k}' in {g.compress}"

/-- The `GTmodty` binder `S` at the module type `Top.I`, restricted away from the
modules `ms`. -/
private def jModBinder (ms : List String) : Json :=
  Json.mkObj
    [("name", Json.str "S"), ("stamp", Json.num 1),
     ("gty", Json.mkObj
       [("kind", Json.str "GTmodty"),
        ("modtype", Json.mkObj
          [("kind", Json.str "ModuleType"), ("name", Json.str "Top.I")]),
        ("restr", jUseRestr ms)])]

/-- The quantifier a binder wraps the body `f` in. -/
private def chkBinderNode (ms : List String) (f : EcForm) : Option EcForm :=
  match bindBinder chkRestrTables "Lforall" (jModBinder ms) with
  | .ok (_, w) => some (w f)
  | .error _ => none

-- A restriction against concrete modules alone binds the module without a
-- footprint, as long as the body reads none.
#guard (match chkBinderNode ["Top.M"] .tru with
        | some (.allModRestr "S" _ gs .tru) => gs.map (·.id) == [7]
        | _ => false)

-- A restriction against a module binder in scope is carried by the binder,
-- whose footprint the quantifier reads.
#guard (match chkBinderNode ["A"] .tru with
        | some (.allModRestrOf "S" _ r .tru) => r.binders == ["A"]
        | _ => false)

-- A body that restricts a nested binder against `S` makes `S` carry its own
-- footprint, as a body comparing `glob S` does.
#guard (match chkBinderNode ["Top.M"]
            (.allModRestrOf "T" chkRestrInterface
              { globals := [], binders := ["S"] } .tru) with
        | some (.allModRestrOn "S" _ gs _) => gs.map (·.id) == [7]
        | _ => false)

#guard (match chkBinderNode ["A"]
            (.allModRestrOf "T" chkRestrInterface
              { globals := [], binders := ["S"] } .tru) with
        | some (.allModRestrOfOn "S" _ r _) => r.binders == ["A"]
        | _ => false)

-- A restriction against a module the tables do not hold rejects the binder
-- rather than giving it a footprint the source does not name.
#guard (chkBinderNode ["Top.Absent"] .tru).isNone

/-- The tables extended by every binder of a quantifier node, and the chain of
quantifier nodes its body sits under. -/
def bindBinders (F : FormTables) (q : String) : List Json →
    Except String (FormTables × (EcForm → EcForm))
  | [] => .ok (F, id)
  | b :: rest => do
    let (F₁, w₁) ← bindBinder F q b
    let (F₂, w₂) ← bindBinders F₁ q rest
    .ok (F₂, fun body => w₁ (w₂ body))

/-- Binding a quantified memory leaves the dispatch tables alone. -/
theorem bindMemName_tables {F F' : FormTables} {st : Nat} {nm : String}
    (h : F.bindMemName st nm = .ok F') : F'.tables = F.tables := by
  unfold FormTables.bindMemName at h
  split at h
  · simp [fail] at h
  · injection h with h
    subst h
    rfl

/-- Binding one quantifier binder leaves the dispatch tables alone. -/
theorem bindBinder_tables {F F' : FormTables} {q : String} {b : Json}
    {w : EcForm → EcForm} (h : bindBinder F q b = .ok (F', w)) :
    F'.tables = F.tables := by
  unfold bindBinder at h
  simp only [Bind.bind, Except.bind] at h
  repeat' split at h
  all_goals obtain ⟨h, -⟩ := h
  all_goals first
    | rfl
    | exact bindLocal_tables (by assumption)
    | exact bindMemName_tables (by assumption)

/-- Binding every binder of a quantifier node leaves the dispatch tables alone,
which is what lets a recursion measured on them descend under a quantifier. -/
theorem bindBinders_tables {q : String} :
    ∀ {bs : List Json} {F F' : FormTables} {w : EcForm → EcForm},
      bindBinders F q bs = .ok (F', w) → F'.tables = F.tables
  | [], _, _, _, h => by
      unfold bindBinders at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨h, -⟩ := h
      subst h
      rfl
  | _ :: _, _, _, _, h => by
      unfold bindBinders at h
      simp only [bind, Except.bind] at h
      split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨h, -⟩ := h
          subst h
          exact (bindBinders_tables (by assumption)).trans
            (bindBinder_tables (by assumption))

/-! ## The judgement argument

`EcForm.hoare`, `.bdHoare` and `.equiv` carry the argument the procedure is
applied to, and EasyCrypt's judgement syntax leaves it implicit: the assertions
speak about the procedure's formal parameter `arg` instead. The argument is
therefore recoverable only when the procedure takes none. -/

/-- The argument term of a judgement over the procedure `q` at signature `s`. -/
def judgementArg (q : String) (s : EcSig) : Except String (EcTerm s.arg) :=
  match s.arg with
  | .unit => .ok (.lit (t := .unit) ())
  | u =>
    fail s!"a judgement over '{q}', whose argument has type {repr u}: EasyCrypt \
      leaves a judgement's argument implicit and its assertions speak about the \
      formal parameter instead, while EcForm.hoare and EcForm.equiv carry an \
      explicit argument term"

/-- Whether a node is EasyCrypt's `true`, the trivial assertion. -/
def isTrueForm (F : FormTables) (j : Json) : Bool :=
  match j.getObjValAs? String "kind", j.getObjValAs? String "path" with
  | .ok "Fop", .ok p =>
    match List.lookup p F.tables.constPaths with
    | some v => if h : v.ty = EcTy.bool then (show Bool from v.transport h) else false
    | none => false
  | _, _ => false

/-- Whether a node is the real literal `1`. -/
def isRealOne (F : FormTables) (j : Json) : Bool :=
  match appHeadPath j with
  | .ok p =>
    p == F.paths.realFromInt &&
      (match j.getObjVal? "args" with
       | .ok (.arr a) =>
         match a.toList with
         | [n] =>
           (match n.getObjValAs? String "kind" with | .ok "Fint" => true | _ => false) &&
             (match n.getObjValAs? String "value" with | .ok "1" => true | _ => false)
         | _ => false
       | _ => false)
  | .error _ => false

/-- Whether a bounded Hoare node is EasyCrypt's `islossless`, which is notation
for `bd_hoare[q : true ==> true] = 1`. -/
def isLosslessShape (F : FormTables) (j : Json) : Bool :=
  (match j.getObjValAs? String "cmp" with | .ok "FHeq" => true | _ => false) &&
    (match j.getObjVal? "pre" with | .ok p => isTrueForm F p | .error _ => false) &&
    (match j.getObjVal? "post" with | .ok p => isTrueForm F p | .error _ => false) &&
    (match j.getObjVal? "bound" with | .ok b => isRealOne F b | .error _ => false)

/-- The comparison an EasyCrypt `hoarecmp` denotes. -/
def decodeHoareCmp (s : String) : Except String EcCmp :=
  match s with
  | "FHle" => .ok .le
  | "FHeq" => .ok .eq
  | "FHge" => .ok .ge
  | k => fail s!"unknown Hoare comparison '{k}'"

/-- The real literal a bound node carries. A bound in the fragment is a closed
constant, and `from_int` of a non-negative integer is its only shape, so the
numeral the node applies `from_int` to is the whole of the literal. -/
def decodeRealLit (F : FormTables) (j : Json) : Except String EcRealLit := do
  let p ← appHeadPath j
  if p = F.paths.realInv then
    -- `inv` of a numeral is that numeral's reciprocal, the shape a guessing
    -- game's bound is written in. Its argument is a literal of the same
    -- fragment, so the reading is the numeral it carries, under a `1`.
    match _hinv : getArr j "args" with
    | .error e => .error e
    | .ok arr =>
      match arr.toList.attach with
      | [⟨d, _hd⟩] =>
        match decodeRealLit F d with
        | .error e => .error e
        | .ok r =>
          if r.den ≠ 1 then
            fail s!"'{p}' of a bound that is itself a fraction in {j.compress}: \
              the fragment carries one division"
          else if r.num = 0 then
            fail s!"'{p}' of zero in {j.compress}: the reciprocal of zero is not \
              a bound the fragment carries"
          else .ok ⟨1, r.num⟩
      | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 1"
  else if p ≠ F.paths.realFromInt then
    fail s!"the real literal '{p}' in {j.compress}: the fragment has the \
      injection of a non-negative integer only"
  else
    let arr ← getArr j "args"
    match arr.toList with
    | [n] =>
      let k ← getStr n "kind"
      if k ≠ "Fint" then
        fail s!"'{p}' applied to a node of kind '{k}', expected an integer literal"
      else
        let v ← getStr n "value"
        match v.toNat? with
        | some m => .ok ⟨m, 1⟩
        | none =>
          fail s!"the integer literal '{v}' is not a non-negative decimal, and a \
            negative bound has no image in ℝ≥0∞"
    | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 1"
termination_by jsonSize j
decreasing_by
  exact getArr_decreases _hinv (Array.mem_toList_iff.mp ‹_ ∈ Array.toList _›)

/-! ## Reading a definition written over type parameters

A theory-level `op f ['a] (x : t) = e.` has no codes until a read site gives its
type parameters values, and `DecodeTables.polyOpPaths` (`Json.lean`) holds the
declaration as the exporter wrote it. A read of one decodes to its body at the
read site: the type arguments the node carries give the type parameters their
codes, and the value arguments replace the parameters in the body before it is
decoded.

The value arguments go in by substitution rather than by binding the parameters
to values, because the argument at a function-typed parameter — `associative`'s
is one — is written as an operator or a lambda, and a lambda has no term image.
What the body's applications name after the substitution is the argument's own
operator.

The substitution contracts where the parameter it replaces heads an application
and the argument is a lambda, since the exporter writes a partial application as
one: `right_loop inv o` reads `cancel` at `fun x => o x y`, and `cancel`'s body
applies both of its parameters, so the two meet. A lambda planted under an
application has no image, because the term layer has no lambda, and the
contracted node is the lambda's body at the arguments instead. An application the
lambda's binders do not match in number stands as it is and is reported there.

The expansion belongs to the formula decoder because these bodies are
quantified: `associative f` is defined by `forall x y z, f x (f y z) = f (f x y)
z`, and `EcForm.allTy` is where a binder has an image. The body is not a sub-node
of the application that reads it, so the recursion is measured on the definitions
of each kind still available together with the node's size, ordered
lexicographically, and the body is decoded against the tables with that
definition dropped: a definition cannot be reached from inside itself, and a
chain of reads is as long as the table. -/

/-- The tables a read of the definition over type parameters at `path` expands
against: that definition dropped, and its type parameters read at the codes `bs`
the read site's type arguments give them. -/
def FormTables.expandPolyAt (F : FormTables) (path : String)
    (bs : List (String × EcTy)) : FormTables :=
  { F with tables :=
      { F.tables with
        polyOpPaths := F.tables.polyOpPaths.filter (fun e => e.1 != path),
        tyVarCodes := bs ++ F.tables.tyVarCodes } }

/-- The definitions over type parameters left after the one at `path` is dropped
are fewer. -/
theorem expandPolyAt_length_lt_of_eq (F : FormTables) (path : String)
    (bs : List (String × EcTy)) {d : EcPolyOpDefn}
    (h : List.lookup path F.tables.polyOpPaths = some d) :
    (F.expandPolyAt path bs).tables.polyOpPaths.length
      < F.tables.polyOpPaths.length :=
  length_filter_ne_lt_of_lookup _ _ (by rw [h]; rfl)

/-- The depth the argument substitution descends to. A read below it leaves the
parameter in place, and the decoder then reports it as a variable no quantifier
binds, so an exhausted bound is a decode failure and never a silent
expansion. -/
def substDepth : Nat := 256

/-- The binder stamps and the body of a lambda node, when the node is one. -/
def lambdaStamps (j : Json) : Option (List Nat × Json) :=
  match j.getObjValAs? String "kind", j.getObjValAs? String "quant" with
  | .ok "Fquant", .ok "Llambda" =>
    match j.getObjVal? "binders", j.getObjVal? "body" with
    | .ok (.arr bs), .ok body =>
      match bs.toList.mapM (fun b => (b.getObjValAs? Nat "stamp").toOption) with
      | some sts => some (sts, body)
      | none => none
    | _, _ => none
  | _, _ => none

/-- The arguments of an application whose head is a read of the logical variable
at `stamp`, when the node is one. -/
def appArgsAtLocal (stamp : Nat) (j : Json) : Option (List Json) :=
  match j.getObjValAs? String "kind" with
  | .ok "Fapp" =>
    match j.getObjVal? "f" with
    | .ok fJ =>
      match fJ.getObjValAs? String "kind", fJ.getObjValAs? Nat "stamp" with
      | .ok "Flocal", .ok st =>
        if st == stamp then
          match j.getObjVal? "args" with
          | .ok (.arr as) => some as.toList
          | _ => none
        else none
      | _, _ => none
    | .error _ => none
  | _ => none

/-- The parts a contraction of the node `j` is built from, when `j` applies a
read of the logical variable at `stamp` to as many arguments as the lambda `repl`
binds: the lambda's binder stamps, the arguments, and the lambda's body. An
argument count the lambda's binders do not match has no contraction. -/
def betaRedexAt (stamp : Nat) (repl j : Json) :
    Option (List Nat × List Json × Json) :=
  match appArgsAtLocal stamp j, lambdaStamps repl with
  | some args, some (sts, body) =>
    if sts.length = args.length then some (sts, args, body) else none
  | _, _ => none

/-- The node with every read of the logical variable at `stamp` replaced by
`repl`, to the depth `fuel`. A read that `betaRedexAt` sees at the head of an
application is contracted instead of replaced: the node becomes the lambda's
body with each of its binders substituted by the argument at that position. -/
def substLocal : Nat → Json → Nat → Json → Json
  | _, _, 0, j => j
  | stamp, repl, fuel + 1, j =>
    match j with
    | .arr as => .arr (as.map (substLocal stamp repl fuel))
    | .obj m =>
      match j.getObjValAs? String "kind", j.getObjValAs? Nat "stamp" with
      | .ok "Flocal", .ok st => if st == stamp then repl else j
      | _, _ =>
        match betaRedexAt stamp repl j with
        | some (sts, args, body) =>
          (sts.zip (args.map (substLocal stamp repl fuel))).foldl
            (fun b q => substLocal q.1 q.2 fuel b) body
        | none =>
          Json.mkObj (m.toList.map (fun kv => (kv.1, substLocal stamp repl fuel kv.2)))
    | _ => j

/-- The stamps a definition's defining lambda binds, and the body under them.

The exporter writes `op f x y = e` as a lambda over the parameters, so a
definition of arity `n` is an `Fquant` with `quant = Llambda` binding `n`
identifiers. A definition of arity zero is its form as written. -/
def polyBodyBinders (pd : EcPolyOpDefn) : Except String (List Nat × Json) := do
  let bodyJ ← getObj pd.decl "body"
  let formJ ← getObj bodyJ "form"
  match getStr formJ "kind" with
  | .ok "Fquant" =>
    let q ← getStr formJ "quant"
    if q ≠ "Llambda" then
      fail s!"the operator '{pd.path}' has a defining form quantified by '{q}', \
        expected a lambda"
    else
      let bs ← getArr formJ "binders"
      let stamps ← bs.toList.mapM (fun b => getNat b "stamp")
      let inner ← getObj formJ "body"
      .ok (stamps, inner)
  | _ => .ok ([], formJ)

/-- The body of the definition `pd`, read at `arr`: every parameter replaced by
the argument at its position. -/
def polyBodyAt (pd : EcPolyOpDefn) (arr : Array Json) :
    Except String Json := do
  let (bs, inner) ← polyBodyBinders pd
  if bs.length ≠ arr.size then
    fail s!"the operator '{pd.path}' is defined over {bs.length} parameter(s) \
      and applied to {arr.size} argument(s): a partial application is \
      function-typed and has no EcTy code"
  else
    .ok ((bs.zip arr.toList).foldl
      (fun b q => substLocal q.1 q.2 substDepth b) inner)

/-- The codes a read site's type arguments give the type parameters of `pd`. -/
def polyTyArgs (T : DecodeTables) (pd : EcPolyOpDefn) (j : Json) :
    Except String (List (String × EcTy)) := do
  let targs := appHeadTargs j
  if targs.length ≠ pd.tyParams.length then
    fail s!"the operator '{pd.path}' is defined over {pd.tyParams.length} type \
      parameter(s) and read at {targs.length} type argument(s)"
  else
    let codes ← targs.mapM (decodeTy T)
    .ok (pd.tyParams.zip codes)

/-! ## A concrete definition whose body is a formula

`decodeTerm` reads a concrete definition at the term layer, and two body shapes
have no image there: a quantified formula, which `EcTerm` has no binder for, and
an application of a definition written over type parameters, whose path the term
layer's operator tables do not carry. A read of such a definition in formula
position is decoded by `decodeForm` instead, at the same discipline the term
layer uses — the arguments are terms, the parameters are bound at the read site,
and the body is decoded against the tables with that definition dropped — with
`EcForm.letF` in place of `EcTerm.letIn`.

`defBodyIsForm` is the test that picks the route. It is syntactic and it holds of
exactly the two shapes above, so a definition the term layer decodes today is
still decoded there. -/

/-- Whether the body of a concrete definition is a node the term decoder has no
image for: a quantified formula, or an application of a definition written over
type parameters. -/
def defBodyIsForm (T : DecodeTables) (body : Json) : Bool :=
  match body.getObjValAs? String "kind" with
  | .ok "Fquant" =>
    match body.getObjValAs? String "quant" with
    | .ok q => q == "Lforall" || q == "Lexists"
    | _ => false
  | .ok "Fapp" =>
    match appHeadPath body with
    | .ok p => (List.lookup p T.polyOpPaths).isSome
    | .error _ => false
  | _ => false

/-! ## Formulas and probabilities

The two layers are mutually recursive: a probability comparison is a formula and
the event of a `Pr[…]` node is a formula. Four auxiliaries join them so that
every recursive call descends exactly one field or one array element, which is
what the `jsonSize` measure decreases on: `decodeExnPost` reads a Hoare
postcondition, `decodeProbEvent` reads a `Pr[…]` event, and `decodeProbDiff` with
`decodeProbNeg` read the difference under an absolute value — a signed difference
of probabilities has no `EcProb`, since `ℝ≥0∞` subtraction is truncated. -/

mutual

/-- Decode a formula node. -/
def decodeForm (F : FormTables) (j : Json) : Except String EcForm :=
  match getStr j "kind" with
  | .error e => .error e
  | .ok kind =>
    if kind = "FhoareS" || kind = "FbdHoareS" || kind = "FequivS" then
      fail s!"the statement judgement '{kind}' in {j.compress}: its assertions \
        range over the local variables in scope, and locals are a valuation in \
        the lowering rather than heap state, so there is nothing for them to \
        denote; only the procedure-level judgements have an EcForm image"
    else if kind = "FeHoareF" || kind = "FeHoareS" then
      fail s!"the expectation-Hoare judgement '{kind}' in {j.compress}: its pre- \
        and postcondition are xreal-valued, and EcForm has no expectation \
        judgement"
    else if kind = "FeagerF" then
      fail s!"the eager judgement in {j.compress}: CatCrypt has no \
        eager-sampling judgement"
    else if kind = "Fmatch" then
      fail s!"match formula in {j.compress}: EcTy has no sum or inductive codes, \
        so there is nothing to match on"
    else if kind = "Fglob" then
      fail s!"'glob M' as a formula in {j.compress}: a footprint is not a \
        proposition, and the formula image of a footprint is the comparison of \
        two of them"
    else if kind = "Fint" then
      fail s!"integer literal as a formula in {j.compress}"
    else if kind = "Unsupported" then fail (unsupportedMsg j)
    else if kind = "Fquant" then
      match getStr j "quant" with
      | .error e => .error e
      | .ok q =>
        match getArr j "binders" with
        | .error e => .error e
        | .ok bs =>
          match _hbb : bindBinders F q bs.toList with
          | .error e => .error e
          | .ok (F', wrap) =>
            match _hqb : getObj j "body" with
            | .error e => .error e
            | .ok bodyJ =>
              match decodeForm F' bodyJ with
              | .error e => .error e
              | .ok body => .ok (wrap body)
    else if kind = "Fif" then
      match getObj j "cond" with
      | .error e => .error e
      | .ok cJ =>
        match _hft : getObj j "then" with
        | .error e => .error e
        | .ok tJ =>
          match _hfe : getObj j "else" with
          | .error e => .error e
          | .ok eJ =>
            match decodeTerm F .bool cJ with
            | .error e => .error e
            | .ok ce =>
              match decodeForm F tJ with
              | .error e => .error e
              | .ok tf =>
                match decodeForm F eJ with
                | .error e => .error e
                | .ok ef => .ok (.ifF ce tf ef)
    else if kind = "Flet" then
      match getObj j "pat" with
      | .error e => .error e
      | .ok patJ =>
        match getStr patJ "kind" with
        | .error e => .error e
        | .ok "LSymbol" =>
          match getObj patJ "binder" with
          | .error e => .error e
          | .ok bJ =>
            match getStr bJ "name" with
            | .error e => .error e
            | .ok nm =>
              match getNat bJ "stamp" with
              | .error e => .error e
              | .ok st =>
                match decodeTyField F.tables bJ "ty" with
                | .error e => .error e
                | .ok t' =>
                  match _hbl : F.bindLocal st nm with
                  | .error e => .error e
                  | .ok F' =>
                    match getObj j "value" with
                    | .error e => .error e
                    | .ok vJ =>
                      match _hlb : getObj j "body" with
                      | .error e => .error e
                      | .ok bodyJ =>
                        match decodeTerm F t' vJ with
                        | .error e => .error e
                        | .ok ve =>
                          match decodeForm F' bodyJ with
                          | .error e => .error e
                          | .ok bf => .ok (.letF nm ve bf)
        | .ok "LTuple" =>
          fail s!"tuple let pattern in {j.compress}: EcForm.letF binds a single \
            variable"
        | .ok k => fail s!"unsupported let pattern kind '{k}' in {patJ.compress}"
    else if kind = "FhoareF" then
      match getStr j "proc" with
      | .error e => .error e
      | .ok q =>
        match procSigOf F q with
        | .error e => .error e
        | .ok s =>
          match judgementArg q s with
          | .error e => .error e
          | .ok arg =>
            match memStampOf j "mem" with
            | .error e => .error e
            | .ok st =>
              let F' := F.bindMemStamp st (.side .cur)
              match _hhpre : getObj j "pre" with
              | .error e => .error e
              | .ok preJ =>
                match _hhpost : getObj j "post" with
                | .error e => .error e
                | .ok postJ =>
                  match decodeForm F' preJ with
                  | .error e => .error e
                  | .ok pre =>
                    match decodeExnPost F' q postJ with
                    | .error e => .error e
                    | .ok post => .ok (.hoare q s arg pre post)
    else if kind = "FbdHoareF" then
      match getStr j "proc" with
      | .error e => .error e
      | .ok q =>
        match procSigOf F q with
        | .error e => .error e
        | .ok s =>
          -- A bounded Hoare judgement over a procedure of an abstract module has
          -- no body to reason against, and the one such judgement EasyCrypt
          -- writes is `islossless`. It decodes to the dedicated node, which
          -- quantifies over the argument instead of reconstructing it.
          if (abstractProcOf F q).isSome then
            if isLosslessShape F j then .ok (.lossless q s)
            else
              fail s!"the bounded Hoare judgement over '{q}', a procedure of an \
                abstract module: the module has no body, and the only judgement \
                over one with an image is `islossless`, which is \
                `bd_hoare[q : true ==> true] = 1`"
          else
          match judgementArg q s with
          | .error e => .error e
          | .ok arg =>
            match memStampOf j "mem" with
            | .error e => .error e
            | .ok st =>
              let F' := F.bindMemStamp st (.side .cur)
              match getStr j "cmp" with
              | .error e => .error e
              | .ok cmpS =>
                match decodeHoareCmp cmpS with
                | .error e => .error e
                | .ok cmp =>
                  match getObj j "bound" with
                  | .error e => .error e
                  | .ok bdJ =>
                    match decodeRealLit F bdJ with
                    | .error e => .error e
                    | .ok bd =>
                      match _hbpre : getObj j "pre" with
                      | .error e => .error e
                      | .ok preJ =>
                        match _hbpost : getObj j "post" with
                        | .error e => .error e
                        | .ok postJ =>
                          match decodeForm F' preJ with
                          | .error e => .error e
                          | .ok pre =>
                            match decodeForm F' postJ with
                            | .error e => .error e
                            | .ok post =>
                              .ok (.bdHoare q s arg pre post cmp bd)
    else if kind = "FequivF" then
      match getStr j "proc_left" with
      | .error e => .error e
      | .ok q₁ =>
        match getStr j "proc_right" with
        | .error e => .error e
        | .ok q₂ =>
          match procSigOf F q₁ with
          | .error e => .error e
          | .ok s₁ =>
            match procSigOf F q₂ with
            | .error e => .error e
            | .ok s₂ =>
              match judgementArg q₁ s₁ with
              | .error e => .error e
              | .ok arg₁ =>
                match judgementArg q₂ s₂ with
                | .error e => .error e
                | .ok arg₂ =>
                  match memStampOf j "mem_left" with
                  | .error e => .error e
                  | .ok stl =>
                    match memStampOf j "mem_right" with
                    | .error e => .error e
                    | .ok str =>
                      let F' := (F.bindMemStamp stl (.side .left)).bindMemStamp
                        str (.side .right)
                      match _hepre : getObj j "pre" with
                      | .error e => .error e
                      | .ok preJ =>
                        match _hepost : getObj j "post" with
                        | .error e => .error e
                        | .ok postJ =>
                          match decodeForm F' preJ with
                          | .error e => .error e
                          | .ok pre =>
                            match decodeForm F' postJ with
                            | .error e => .error e
                            | .ok post =>
                              .ok (.equiv q₁ s₁ arg₁ q₂ s₂ arg₂ pre post)
    else if kind = "Fop" then
      match getStr j "path" with
      | .error e => .error e
      | .ok p =>
        match List.lookup p F.tables.constPaths with
        | some v =>
          if h : v.ty = EcTy.bool then
            .ok (if (show Bool from v.transport h) then .tru else .fls)
          else
            match decodeTerm F .bool j with
            | .error e => .error e
            | .ok b => .ok (.holds b)
        | none =>
          match decodeTerm F .bool j with
          | .error e => .error e
          | .ok b => .ok (.holds b)
    else if kind = "Fapp" then
      match appHeadPath j with
      | .error _ =>
        -- A head that is not an operator is a quantified function applied to an
        -- argument, which the term layer reads; the formula is that the boolean
        -- it denotes holds.
        match decodeTerm F .bool j with
        | .error e => .error e
        | .ok b => .ok (.holds b)
      | .ok p =>
        match _hfa : getArr j "args" with
        | .error e => .error e
        | .ok arr =>
          if p = F.paths.losslessOp then
            match arr.toList with
            | [x] =>
              match decodeTyField F.tables x "ty" with
              | .error e => .error e
              | .ok dty =>
                match dty with
                | .distr u =>
                  match decodeTerm F (.distr u) x with
                  | .error e => .error e
                  | .ok d => .ok (.isLossless d)
                | _ =>
                  fail s!"'{p}' applied to a term of type {repr dty}: total mass \
                    is asserted of a distribution"
            | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 1"
          else if p = F.paths.realLe || p = F.paths.realLt then
            match arr.toList.attach with
            | [⟨x, _⟩, ⟨y, _⟩] =>
              match decodeProb F x with
              | .error e => .error e
              | .ok a =>
                match decodeProb F y with
                | .error e => .error e
                | .ok b =>
                  .ok (.probCmp (if p = F.paths.realLe then .le else .lt) a b)
            | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
          else if p = F.paths.iffOp then
            match arr.toList.attach with
            | [⟨x, _⟩, ⟨y, _⟩] =>
              match decodeForm F x with
              | .error e => .error e
              | .ok a =>
                match decodeForm F y with
                | .error e => .error e
                | .ok b => .ok (.iff a b)
            | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
          else
            match List.lookup p F.tables.opPaths with
            | some .bnot =>
              match arr.toList.attach with
              | [⟨x, _⟩] =>
                match decodeForm F x with
                | .error e => .error e
                | .ok a => .ok (.not a)
              | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 1"
            | some .band =>
              match arr.toList.attach with
              | [⟨x, _⟩, ⟨y, _⟩] =>
                match decodeForm F x with
                | .error e => .error e
                | .ok a =>
                  match decodeForm F y with
                  | .error e => .error e
                  | .ok b => .ok (.and a b)
              | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
            | some .bor =>
              match arr.toList.attach with
              | [⟨x, _⟩, ⟨y, _⟩] =>
                match decodeForm F x with
                | .error e => .error e
                | .ok a =>
                  match decodeForm F y with
                  | .error e => .error e
                  | .ok b => .ok (.or a b)
              | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
            | some .bimp =>
              match arr.toList.attach with
              | [⟨x, _⟩, ⟨y, _⟩] =>
                match decodeForm F x with
                | .error e => .error e
                | .ok a =>
                  match decodeForm F y with
                  | .error e => .error e
                  | .ok b => .ok (.imp a b)
              | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
            | some .beq =>
              if appHeadTarg j == some F.paths.realTy then
                match arr.toList.attach with
                | [⟨x, _⟩, ⟨y, _⟩] =>
                  match decodeProb F x with
                  | .error e => .error e
                  | .ok a =>
                    match decodeProb F y with
                    | .error e => .error e
                    | .ok b => .ok (.probCmp .eq a b)
                | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
              else
                match globEqPair arr with
                | some (x, y) => decodeGlobEq F x y
                | none =>
                  match globTupleEqPair arr with
                  | some (xs, ys) => decodeGlobTupleEq F xs ys
                  | none =>
                    match decodeTerm F .bool j with
                    | .error e => .error e
                    | .ok b =>
                      match b with
                      | .beq x y => .ok (.eqT x y)
                      | _ => .ok (.holds b)
            | none =>
              -- A definition written over type parameters expands at the read
              -- site: its type arguments give the parameters codes, and its
              -- value arguments go into the body before the body is decoded.
              match _hpp : List.lookup p F.tables.polyOpPaths with
              | none =>
                -- A concrete definition whose body is a formula the term layer
                -- has no image for is read here: the arguments are decoded as
                -- terms, the parameters are bound at the read site, and the body
                -- is decoded as a formula against the tables with this
                -- definition dropped. Every other body takes the term route.
                match _hdf : List.lookup p F.tables.defOpPaths with
                | some d =>
                  if defBodyIsForm F.tables d.body then
                    match arr.toList.mapM (fun x =>
                        match decodeTyField F.tables x "ty" with
                        | .error e => Except.error e
                        | .ok u =>
                          match decodeTerm F u x with
                          | .error e => Except.error e
                          | .ok xe => Except.ok (Sigma.mk u xe)) with
                    | .error e => .error e
                    | .ok vs =>
                      if vs.map Sigma.fst = d.params.map Prod.snd then
                        match _hbf : bindOpParams (F.withoutDefOp p) p d.params with
                        | .error e => .error e
                        | .ok F' =>
                          match decodeForm F' d.body with
                          | .error m =>
                            fail s!"the operator '{p}' is defined by a form that \
                              does not decode: {m}"
                          | .ok bf =>
                            .ok (wrapOpLetsF
                              ((d.params.map (fun q => opParamName q.1)).zip vs) bf)
                      else
                        fail s!"the operator '{p}' is defined at argument types \
                          {repr (d.params.map Prod.snd)} and applied to arguments \
                          of types {repr (vs.map Sigma.fst)}"
                  else
                    match decodeTerm F .bool j with
                    | .error e => .error e
                    | .ok b => .ok (.holds b)
                | none =>
                  match decodeTerm F .bool j with
                  | .error e => .error e
                  | .ok b => .ok (.holds b)
              | some pd =>
                match polyTyArgs F.tables pd j with
                | .error e => .error e
                | .ok bs =>
                  match polyBodyAt pd arr with
                  | .error e => .error e
                  | .ok inner =>
                    match decodeForm (F.expandPolyAt p bs) inner with
                    | .error m =>
                      fail s!"the operator '{p}' is defined by a form that does \
                        not decode at the type arguments it is read with: {m}"
                    | .ok f => .ok f
            | _ =>
              match decodeTerm F .bool j with
              | .error e => .error e
              | .ok b => .ok (.holds b)
    else
      match decodeTerm F .bool j with
      | .error e => .error e
      | .ok b => .ok (.holds b)
termination_by (F.tables.defOpPaths.length, F.tables.polyOpPaths.length, jsonSize j)
decreasing_by
  all_goals first
    | exact Prod.Lex.right _ (Prod.Lex.right _ (getObj_decreases (by assumption)))
    | exact Prod.Lex.right _ (Prod.Lex.right _
        (getArr_decreases (by assumption) (Array.mem_toList_iff.mp ‹_ ∈ Array.toList _›)))
    | (rw [bindLocal_tables (by assumption)]
       exact Prod.Lex.right _ (Prod.Lex.right _ (getObj_decreases (by assumption))))
    | (rw [bindBinders_tables (by assumption)]
       exact Prod.Lex.right _ (Prod.Lex.right _ (getObj_decreases (by assumption))))
    | exact Prod.Lex.right _
        (Prod.Lex.left _ _ (expandPolyAt_length_lt_of_eq _ _ _ (by assumption)))
    | (rw [bindOpParams_tables (by assumption)]
       exact Prod.Lex.left _ _ (withoutDefOp_length_lt_of_eq _ _ (by assumption)))

/-- Decode a Hoare postcondition. It is an `exnpost`: a normal-exit formula and
one formula per exception branch, and `EcForm` has no exception
postcondition. -/
def decodeExnPost (F : FormTables) (q : String) (j : Json) : Except String EcForm :=
  match getArr j "exn" with
  | .error e => .error e
  | .ok exns =>
    if !exns.isEmpty then
      fail s!"the postcondition of the judgement over '{q}' has {exns.size} \
        exception branches, and EcForm has no exception postcondition"
    else
      match _hmain : getObj j "main" with
      | .error e => .error e
      | .ok mainJ => decodeForm F mainJ
termination_by (F.tables.defOpPaths.length, F.tables.polyOpPaths.length, jsonSize j)
decreasing_by exact Prod.Lex.right _ (Prod.Lex.right _ (getObj_decreases _hmain))

/-- Decode a real-valued formula node as a probability expression. -/
def decodeProb (F : FormTables) (j : Json) : Except String EcProb :=
  match getStr j "kind" with
  | .error e => .error e
  | .ok kind =>
    if kind = "Fpr" then
      match getStr j "proc" with
      | .error e => .error e
      | .ok q =>
        match procSigOf F q with
        | .error e => .error e
        | .ok s =>
          match memRefOf F j "mem" with
          | .error e => .error e
          | .ok m =>
            match getObj j "args" with
            | .error e => .error e
            | .ok argsJ =>
              match decodeTerm F s.arg argsJ with
              | .error e => .error e
              | .ok arg =>
                match _hev : getObj j "event" with
                | .error e => .error e
                | .ok evJ =>
                  match decodeProbEvent F evJ with
                  | .error e => .error e
                  | .ok ev => .ok (.pr q s arg m ev)
    else if kind = "Flocal" then
      match localNameOf F j with
      | .error e => .error e
      | .ok x => .ok (.pvar x)
    else if kind = "Fapp" then
      match appHeadPath j with
      | .error e => .error e
      | .ok p =>
        if p = F.paths.realFromInt then
          match decodeRealLit F j with
          | .error e => .error e
          | .ok r => .ok (.const r)
        else if p = F.paths.realOpp then
          fail s!"the negation of a probability in {j.compress}: EcProb has no \
            signed negation, because ℝ≥0∞ subtraction is truncated"
        else
          match _hpa : getArr j "args" with
          | .error e => .error e
          | .ok arr =>
            if p = F.paths.realAbs then
              match arr.toList.attach with
              | [⟨x, _⟩] => decodeProbDiff F x
              | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 1"
            else if p = F.paths.realAdd then
              match arr.toList.attach with
              | [⟨x, _⟩, ⟨y, _⟩] =>
                if isAppOf F.paths.realOpp y then
                  fail s!"the signed difference of two probabilities in \
                    {j.compress}: EcProb has absDiff and no sub, because ℝ≥0∞ \
                    subtraction is truncated and a signed difference has no \
                    faithful image"
                else
                  match decodeProb F x with
                  | .error e => .error e
                  | .ok a =>
                    match decodeProb F y with
                    | .error e => .error e
                    | .ok b => .ok (.add a b)
              | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
            else if p = F.paths.realMul then
              match arr.toList.attach with
              | [⟨x, _⟩, ⟨y, _⟩] =>
                match decodeProb F x with
                | .error e => .error e
                | .ok a =>
                  match decodeProb F y with
                  | .error e => .error e
                  | .ok b => .ok (.mul a b)
              | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
            else if p = F.paths.realInv then
              -- The reciprocal of a numeral is a constant, and that is the shape
              -- a guessing game's bound is written in. A reciprocal of anything
              -- else is not a constant and has no `EcProb.const`.
              match decodeRealLit F j with
              | .error e => .error e
              | .ok r => .ok (.const r)
            else if F.paths.muOps.contains p then
              -- `mu d P` reads the element code off its distribution argument,
              -- which the result — a real — does not fix, and the predicate at
              -- the arrow code that element gives.
              match arr.toList.attach with
              | [⟨dJ, _⟩, ⟨pJ, _⟩] =>
                match decodeTyField F.tables dJ "ty" with
                | .error e => .error e
                | .ok (.distr a) =>
                  match decodeTerm F (.distr a) dJ with
                  | .error e => .error e
                  | .ok de =>
                    match decodeTerm F (.arrow a .bool) pJ with
                    | .error e => .error e
                    | .ok pe => .ok (.mu de pe)
                | .ok u =>
                  fail s!"'{p}' is applied to a value of type {repr u}, which \
                    is not a distribution"
              | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
            else
              fail s!"the real operator '{p}' in {j.compress}: EcProb has \
                Pr[…], a constant, a parameter, a sum, a product, an absolute \
                difference and `mu`, and nothing else"
    else
      fail s!"the node kind '{kind}' in probability position in {j.compress}"
termination_by (F.tables.defOpPaths.length, F.tables.polyOpPaths.length, jsonSize j)
decreasing_by
  all_goals first
    | exact Prod.Lex.right _ (Prod.Lex.right _ (getObj_decreases _hev))
    | exact Prod.Lex.right _ (Prod.Lex.right _
        (getArr_decreases _hpa (Array.mem_toList_iff.mp ‹_ ∈ Array.toList _›)))

/-- Decode the event of a `Pr[…]` node. Its memory is the post-state the
procedure leaves, which is the judgement's own memory. -/
def decodeProbEvent (F : FormTables) (j : Json) : Except String EcForm :=
  match memStampOf j "mem" with
  | .error e => .error e
  | .ok st =>
    match _hpe : getObj j "form" with
    | .error e => .error e
    | .ok formJ => decodeForm (F.bindMemStamp st (.side .cur)) formJ
termination_by (F.tables.defOpPaths.length, F.tables.polyOpPaths.length, jsonSize j)
decreasing_by exact Prod.Lex.right _ (Prod.Lex.right _ (getObj_decreases _hpe))

/-- Decode the argument of an absolute value as the difference of two
probabilities it must be. -/
def decodeProbDiff (F : FormTables) (j : Json) : Except String EcProb :=
  match appHeadPath j with
  | .error e => .error e
  | .ok p =>
    if p ≠ F.paths.realAdd then
      fail s!"the absolute value of '{p}' in {j.compress}: the fragment's only \
        absolute value is the difference of two probabilities"
    else
      match _hda : getArr j "args" with
      | .error e => .error e
      | .ok arr =>
        match arr.toList.attach with
        | [⟨x, _⟩, ⟨y, _⟩] =>
          match decodeProb F x with
          | .error e => .error e
          | .ok a =>
            match decodeProbNeg F y with
            | .error e => .error e
            | .ok b => .ok (.absDiff a b)
        | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 2"
termination_by (F.tables.defOpPaths.length, F.tables.polyOpPaths.length, jsonSize j)
decreasing_by
  all_goals
    exact Prod.Lex.right _ (Prod.Lex.right _
      (getArr_decreases _hda (Array.mem_toList_iff.mp ‹_ ∈ Array.toList _›)))

/-- Decode the negated side of the difference under an absolute value. -/
def decodeProbNeg (F : FormTables) (j : Json) : Except String EcProb :=
  match appHeadPath j with
  | .error e => .error e
  | .ok p =>
    if p ≠ F.paths.realOpp then
      fail s!"the absolute value of a sum whose right summand is '{p}' in \
        {j.compress}: the fragment's only absolute value is the difference of \
        two probabilities"
    else
      match _hna : getArr j "args" with
      | .error e => .error e
      | .ok arr =>
        match arr.toList.attach with
        | [⟨x, _⟩] => decodeProb F x
        | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 1"
termination_by (F.tables.defOpPaths.length, F.tables.polyOpPaths.length, jsonSize j)
decreasing_by
  all_goals
    exact Prod.Lex.right _ (Prod.Lex.right _
      (getArr_decreases _hna (Array.mem_toList_iff.mp ‹_ ∈ Array.toList _›)))

end

/-! ## Type parameters

A statement the source writes `lemma l ['a] : φ` is polymorphic: its `tparams`
name the type variables `φ` may read, and every type position of `φ` naming one
carries a `Tvar` node. `EcTy` is a closed universe of codes, so a type variable
names no code of its own, and `decodeTy` reads a `Tvar` only where a read site
says what it is (`DecodeTables.tyVarCodes`). What a type parameter of a statement
gets instead is a **reserved type path**, one per parameter: the parameter's
occurrences are rewritten to the nullary type constructor at that path, and the
path is entered in the ingestion's type table at the code the parameter is read
at. A `Tvar` therefore resolves the way every other type resolves, through
`DecodeTables.tyPaths`, and the code a statement is decoded at is a parameter of
the decode rather than a table the type decoder has to grow.

Occurrences resolve **by name**. The exporter writes a type parameter as a bare
name (`EcIdent.name`) in `tparams` while a `Tvar` node carries the name and a
uniqueness stamp, so the stamp has no counterpart on the binder side to match
against; what the stamp is used for here is a consistency check, since a name
carrying two stamps in one statement would mean two binders a name-keyed
substitution would conflate. `decodeAxiomAt` rejects that, and rejects an
occurrence of a name the statement does not declare.

The reserved path is `#tyvar.` before the parameter's source name. An EasyCrypt
path is a dot-separated sequence of identifiers and no identifier starts with
`#`, so no source path collides with it. -/

/-- The type path a statement's type parameter is read at. -/
def tyParamPath (x : String) : String := "#tyvar." ++ x

/-- The code a type parameter with no assignment is read at: the opaque code of
its reserved path, which is the image of a type the source says nothing about
(`Ty.lean` fixes its carrier). A statement decoded at these codes is the source
statement at one abstract type per parameter, which is a consequence of the
source's and not the whole of it; the quantified reading is `EcPolyForm` together
with `FormToProp.importedPropPoly`. -/
def tyParamOpaque (x : String) : EcTy := .opaque (tyParamPath x)

/-- The nullary type constructor a type parameter's occurrences are rewritten
to. -/
def tyParamNode (x : String) : Json :=
  Json.mkObj [("kind", Json.str "Tconstr"), ("path", Json.str (tyParamPath x)),
    ("args", Json.arr #[])]

/-- The depth the type-parameter rewriting descends to. A `Tvar` below it is left
in place and `decodeTy` rejects it, so an exhausted bound is a decode failure and
never a silent rewriting. -/
def tyParamDepth : Nat := 256

/-- The source name and uniqueness stamp of a node, when the node is a type
variable. -/
def tyVarIdentOf (j : Json) : Option (String × Nat) :=
  match j.getObjValAs? String "kind" with
  | .ok "Tvar" =>
    match j.getObjValAs? String "name", j.getObjValAs? Nat "stamp" with
    | .ok nm, .ok st => some (nm, st)
    | _, _ => none
  | _ => none

/-- The type-variable occurrences of a node to the depth `fuel`, in occurrence
order, with repetitions. -/
def tyVarIdents : Nat → Json → List (String × Nat)
  | 0, _ => []
  | fuel + 1, j =>
    match j with
    | .arr as => (as.toList.map (tyVarIdents fuel)).flatten
    | .obj m =>
      match tyVarIdentOf j with
      | some p => [p]
      | none => (m.toList.map (fun kv => tyVarIdents fuel kv.2)).flatten
    | _ => []

/-- The node with every type-variable occurrence of a parameter of `xs` rewritten
to the nullary type constructor at the parameter's reserved path, to the depth
`fuel`. -/
def substTyParams (xs : List String) : Nat → Json → Json
  | 0, j => j
  | fuel + 1, j =>
    match j with
    | .arr as => .arr (as.map (substTyParams xs fuel))
    | .obj m =>
      match tyVarIdentOf j with
      | some (nm, _) => if xs.contains nm then tyParamNode nm else j
      | none => Json.mkObj (m.toList.map (fun kv => (kv.1, substTyParams xs fuel kv.2)))
    | _ => j

/-- Extend the tables with a statement's type parameter, read at the code `t`. -/
def FormTables.withTyParam (F : FormTables) (x : String) (t : EcTy) : FormTables :=
  { F with tables := F.tables.withAliasType (tyParamPath x) t }

/-- The name a `Th_axiom` item declares, and the type parameters it binds, in the
order the source declares them. -/
def axiomTyParams (j : Json) : Except String (String × List String) := do
  let kind ← getStr j "kind"
  if kind ≠ "Th_axiom" then
    fail s!"theory item of kind '{kind}': only Th_axiom carries a statement"
  else
    let name ← getStr j "name"
    let decl ← getObj j "decl"
    let tparams ← getArr decl "tparams"
    let xs ← tparams.toList.mapM (fun x =>
      match x with
      | .str s => .ok s
      | _ =>
        fail s!"the type parameter {x.compress} of '{name}' is not a name")
    .ok (name, xs)

/-! ## Lemmas -/

/-- Decode a `Th_axiom` item's statement at the codes `ts` its type parameters
are read at, in the order the source declares them. -/
def decodeAxiomAt (F : FormTables) (ts : List EcTy) (j : Json) : Except String EcForm := do
  let (name, xs) ← axiomTyParams j
  if ts.length ≠ xs.length then
    fail s!"the statement '{name}' has {xs.length} type parameters and \
      {ts.length} codes to read them at"
  else
    let decl ← getObj j "decl"
    let spec ← getObj decl "spec"
    let occ := tyVarIdents tyParamDepth spec
    match occ.find? (fun p => !xs.contains p.1) with
    | some p =>
      fail s!"the statement '{name}' reads the type variable '{p.1}', which is \
        not one of its type parameters"
    | none =>
      match occ.find? (fun p => occ.any (fun q => q.1 == p.1 && q.2 != p.2)) with
      | some p =>
        fail s!"the type variable '{p.1}' of '{name}' carries two uniqueness \
          stamps: a type variable read without its stamp aliases distinct \
          binders of the same source name"
      | none =>
        let F' := (xs.zip ts).foldl (fun G p => G.withTyParam p.1 p.2) F
        decodeForm F' (substTyParams xs tyParamDepth spec)

/-- Decode a `Th_axiom` item's statement, each type parameter read at the opaque
code of its reserved path. -/
def decodeAxiom (F : FormTables) (j : Json) : Except String EcForm := do
  let (_, xs) ← axiomTyParams j
  decodeAxiomAt F (xs.map tyParamOpaque) j

/-! ### The imported axioms a lemma is stated under

An EasyCrypt proof of a lemma runs in the environment of the theory holding the
lemma and of every theory enclosing it, so the imported form of an
`axiom_kind: Lemma` item is its statement under the `axiom_kind: Axiom` items of
those scopes. The scope is read off the path: the exporter fully qualifies every
path, so the items of the theory at `Top.A.B` are the paths `Top.A.B.x`, and an
axiom at `q` is in scope for a statement at `p` exactly when `q`'s scope is a
prefix of `p`'s.

The scope is the enclosing theory **and its ancestors**, not the enclosing theory
alone. In `crypto__DigitalSignaturesROM.eca` the theory
`Top.StatelessROM.UUFKOAROM.UUFKOA` holds the lemma `dmsg_ll` and declares no
axiom of its own, while the axiom that lemma is proved from — `is_lossless dmsg`
— is declared one scope out, in `Top.StatelessROM.UUFKOAROM`. Reading the
enclosing theory alone drops it, and a goal missing a premise is a stronger claim
than the source's.

An axiom of the scope that does not decode rejects the lemma, naming the axiom.
Dropping it produces a goal stronger than the source lemma, and nothing
downstream distinguishes that goal from the source's own statement; the only
`EcForm` standing for an unknown premise is `EcForm.tru`, which is the same
drop. -/

/-- The `Th_axiom` items of one envelope item, in declaration order: the item
itself, or, for a `Th_theory` item, the statements among its items, theory-inner
theories included. An inner item's path is already fully qualified, so the
collection is flat. -/
def thAxiomItems (j : Json) : List Json :=
  match getStr j "kind" with
  | .ok "Th_axiom" => [j]
  | .ok "Th_theory" =>
    match _hitems : getArr j "items" with
    | .ok arr => (arr.toList.attach.map (fun ⟨x, _⟩ => thAxiomItems x)).flatten
    | .error _ => []
  | _ => []
termination_by jsonSize j
decreasing_by
  exact getArr_decreases _hitems (Array.mem_toList_iff.mp ‹_ ∈ Array.toList _›)

/-- The path an envelope item declares, and the empty string for an item without
one. -/
def itemPath (j : Json) : String := (getStrOpt j "path").getD ""

/-- The scope a fully qualified path is declared in: its components with the
declared name dropped. -/
def pathScope (p : String) : List String := (p.splitOn ".").dropLast

/-- The `axiom_kind` an item's declaration carries. -/
def itemAxiomKind (j : Json) : Option String :=
  match getObj j "decl" with
  | .ok d => getStrOpt d "axiom_kind"
  | .error _ => none

/-- The imported axioms in scope at the statement at `path`, outermost scope
first: every `axiom_kind: Axiom` item of `items` declared in a scope enclosing
`path`, ordered by the depth of that scope. -/
def scopeAxiomItems (items : List Json) (path : String) : List Json :=
  let inScope := (items.flatMap thAxiomItems).filter (fun it =>
    itemAxiomKind it == some "Axiom" && itemPath it != "" && itemPath it != path
      && (pathScope (itemPath it)).isPrefixOf (pathScope path))
  let depth : Json → Nat := fun it => (pathScope (itemPath it)).length
  (List.range ((inScope.map depth).foldl max 0 + 1)).flatMap
    (fun d => inScope.filter (fun it => depth it == d))

/-- The `Th_axiom` item at `path`, or an error naming the path. -/
def findAxiomItem (items : List Json) (path : String) : Except String Json :=
  match (items.flatMap thAxiomItems).find? (fun it => itemPath it == path) with
  | some it => .ok it
  | none => fail s!"the export declares no Th_axiom item at path '{path}'"

/-- Decode an imported axiom of the scope of `path`, reporting its failure as a
failure of the statement it would be a premise of. -/
def decodeScopeAxiom (F : FormTables) (path : String) (ax : Json) :
    Except String EcForm :=
  match axiomTyParams ax with
  | .ok (_, _ :: _) =>
    fail s!"the statement '{path}' is stated under the imported axiom \
      '{itemPath ax}', which binds type parameters: a premise is an EcForm and \
      the type binders are outside it, so the premise has nowhere to bind them"
  | _ =>
    match decodeAxiom F ax with
    | .ok f => .ok f
    | .error m =>
      fail s!"the statement '{path}' is stated under the imported axiom \
        '{itemPath ax}', which does not decode: {m}"

/-- Decode the `axiom_kind: Lemma` item at `path` as the statement its theory
proves: its own statement under the imported axioms of its scope, closed over the
abstract operators all of them read (`EcForm.assembleStatement`). The scope is
`F.scopeItems`.

The type parameters of the lemma are read at the codes `ts`, in the order the
source declares them. A premise binds no type parameter of its own, so a
polymorphic imported axiom of the scope rejects the lemma (`decodeScopeAxiom`).

An `axiom_kind: Axiom` item is refused. Such an item is a hypothesis of its
theory, read at a realization (`importedPropWithOps`), and stating it under
itself holds of every realization, which is not what the source asserts. -/
def decodeLemmaAtTys (F : FormTables) (ts : List EcTy) (path : String) :
    Except String EcForm := do
  let it ← findAxiomItem F.scopeItems path
  let decl ← getObj it "decl"
  let kind ← getStr decl "axiom_kind"
  if kind ≠ "Lemma" then
    fail s!"the statement '{path}' has axiom_kind '{kind}': an imported axiom is \
      a hypothesis of its theory and not a goal of it"
  else
    let goal ← decodeAxiomAt F ts it
    let hyps ← (scopeAxiomItems F.scopeItems path).mapM (decodeScopeAxiom F path)
    .ok (EcForm.assembleStatement hyps goal)

/-- The statement of the lemma at `path` with each of its type parameters read at
the opaque code of that parameter's reserved path. -/
def decodeLemmaAt (F : FormTables) (path : String) : Except String EcForm := do
  let it ← findAxiomItem F.scopeItems path
  let (_, xs) ← axiomTyParams it
  decodeLemmaAtTys F (xs.map tyParamOpaque) path

/-- The signature of each procedure of a decoded module, keyed by the path the
exporter names it by at a judgement or probability site. -/
def procSigsOfStructure (S : DecodedStructure) : List (String × EcSig) :=
  S.procs.map (fun d => (xqualify S.path d.name, d.sp.sig))

/-- Decode the statement of the lemma `name` from an exporter envelope. -/
def importAxiom (F : FormTables) (name : String) (j : Json) : Except String EcForm := do
  let e ← decodeEnvelope j
  let it ← findItem e name
  decodeAxiom F it

/-- Decode the statement of the lemma `name` from an exporter envelope, at the
codes `ts` its type parameters are read at. -/
def importAxiomAt (F : FormTables) (ts : List EcTy) (name : String) (j : Json) :
    Except String EcForm := do
  let e ← decodeEnvelope j
  let it ← findItem e name
  decodeAxiomAt F ts it

/-- Decode the lemma at `path` from an exporter envelope, under the imported
axioms of its scope. The envelope's items are the scope the walk reads, so a
lemma of a theory-inner theory resolves at its full path. -/
def importLemma (F : FormTables) (path : String) (j : Json) :
    Except String EcForm := do
  let e ← decodeEnvelope j
  decodeLemmaAt { F with scopeItems := e.items } path

/-! ## Golden tests

The checks below decode the exporter's own output for a theory carrying one
statement per `f_node` constructor reachable from EasyCrypt's surface syntax —
`forms.expected.json` in this directory, the export of `tests/forms.ec` in the
exporter's tree. They are `#guard` commands rather than `rfl` proofs for the
reason `Json.lean` gives: well-founded recursion is not definitionally reducible,
and the intrinsically typed `EcTerm` family carries no `DecidableEq` instance, so
the expected AST is matched as a pattern.

The rejections are the point of the fixture. Every statement of `forms.ec` whose
`f_node`s reach outside `EcForm` is checked to be an error, so a later change
that let one of them decode to something merely well-typed would fail the
build. -/

section Golden

/-- The exporter's output for the statement theory, as text. -/
private def formsExportText : String := include_str "forms.expected.json"

/-- The exporter's output for the statement theory. -/
private def formsExport : Json :=
  match Json.parse formsExportText with
  | .ok j => j
  | .error _ => Json.null

/-- The tables the statements of that theory decode against. `Ideal` is the one
module of the theory whose body is inside the accepted program fragment — `Enc`
applies the user-declared operator `enc`, whose path is in no dispatch table, and
reads its own global in an expression, which the AST reaches only through
`EcStmt.load`; `Game` is a functor and `Risky` raises — so it is the one
procedure a judgement or a probability node can name. -/
private def formsTables : Except String FormTables := do
  let e ← decodeEnvelope formsExport
  let it ← findItem e "Ideal"
  let S ← decodeStructure ecPrelude 0 it
  .ok (formTables ecPrelude (procSigsOfStructure S))

/-- Decode the statement of the lemma `name` from that theory. -/
private def formsStatement (name : String) : Except String EcForm := do
  let F ← formsTables
  importAxiom F name formsExport

-- The fixture parses and declares the procedure the statements name.
#guard (match formsTables with
        | .ok F => F.procSigs == [("Top.Ideal./main", ⟨.bool, .bool⟩)]
        | _ => false)

-- `forall &m, Pr[Ideal.main(true) @ &m : res] = Pr[Ideal.main(false) @ &m : res]`
-- decodes to a memory quantifier over a comparison of two `Pr[…]` nodes, each
-- applied to the argument the source gives it.
#guard (match formsStatement "ideal_indep" with
        | .ok (.allMem "&m"
                (.probCmp .eq
                  (.pr "Top.Ideal./main" ⟨.bool, .bool⟩ (.lit true) (.named "&m")
                     (.holds (.res .bool .cur)))
                  (.pr "Top.Ideal./main" ⟨.bool, .bool⟩ (.lit false) (.named "&m")
                     (.holds (.res .bool .cur))))) => true
        | _ => false)

-- `forall (b : bool), let p = (b, !b) in (if b then p.`1 else p.`2) = b` decodes
-- to the quantifier, the let, the pair, the two projections and the conditional.
#guard (match formsStatement "form_shapes" with
        | .ok (.allTy .bool "b"
                (.letF "p" (.pair (.var .bool "b") (.bnot (.var .bool "b")))
                  (.eqT
                    (.ite (.var .bool "b")
                      (.fst (.var (.prod .bool .bool) "p"))
                      (.snd (.var (.prod .bool .bool) "p")))
                    (.var .bool "b")))) => true
        | _ => false)

-- `equiv [Enc.main ~ Ideal.main : ={m} ==> ={res}]`: `={m}` is the procedure's
-- formal parameter read at the two memories, and a procedure-local is not heap
-- state.
#guard (match formsStatement "enc_ideal_equiv" with
        | .error _ => true
        | _ => false)

-- The eager judgement.
#guard (match formsStatement "enc_eager" with
        | .error _ => true
        | _ => false)

-- The expectation-Hoare judgement.
#guard (match formsStatement "ideal_ehoare" with
        | .error _ => true
        | _ => false)

-- A match formula.
#guard (match formsStatement "form_match" with
        | .error _ => true
        | _ => false)

-- A let over a tuple pattern.
#guard (match formsStatement "form_let_tuple" with
        | .error _ => true
        | _ => false)

-- `Pr[Ideal.main(true) @ &m : res] = 1%r / 2%r`: the bound is the reciprocal of
-- a numeral, which `EcRealLit` carries as a denominator, so the statement
-- decodes.
#guard (match formsStatement "ideal_uniform" with
        | .ok _ => true
        | _ => false)

-- A statement over a user-declared operator, whose path is in no dispatch table.
#guard (match formsStatement "enc_involutive" with
        | .error _ => true
        | _ => false)

-- A statement over a user-declared predicate.
#guard (match formsStatement "agree_refl" with
        | .error _ => true
        | _ => false)

-- `forall (A <: Adv) &m, (glob A){m} = (glob A){m}`: the module type `Adv` is
-- in no module-type table this fixture builds, and the binder's interface is the
-- one its `ModuleType` node's own signature declares.
#guard (match formsStatement "glob_refl" with
        | .ok (.allModOn "A" I (.allMem "&m" (.memEqOnMod "A" _ _))) =>
          I.names == ["guess"]
        | _ => false)

-- A judgement over a procedure outside the accepted program fragment has no
-- signature, so its argument and result types cannot be reconstructed.
#guard (match formsStatement "enc_hoare" with
        | .error _ => true
        | _ => false)

#guard (match formsStatement "risky_hoare" with
        | .error _ => true
        | _ => false)

/-! ### The judgements the decoder accepts

Every Hoare judgement of `forms.ec` is a rejection, for a reason about the
procedure rather than about the judgement: `Enc.main` takes a `bool` argument, so
the argument EasyCrypt leaves implicit is not reconstructible, and its body is
outside the accepted program fragment, so its signatures never reach the table.
`hoare.expected.json`, the export of
`tests/hoare.ec` in the exporter's tree, is the accepting counterpart: a module
whose one global is a `bool` and whose two procedures take no argument. The checks
below pin the `FhoareF` decoder and the `FbdHoareF` decoder at each of EasyCrypt's
three `hoarecmp` comparisons.

The assertions of that fixture read the module's global, and a global read is the
one term leaf a `#guard` pattern cannot descend into: `EcTerm.glob g m` is indexed
by `g.ty`, a projection out of its own field, so a pattern for it makes the
dependent pattern matcher solve `EcTy.bool = g.ty` with `g` a fresh variable. The
guards below therefore bind the two operands of the equality and read their leaves
back with `EcTerm.globRead` and `EcTerm.litValue`, whose own `match` quantifies the
index. Nothing is left open by this: the global's name, location id and type, the
memory it is read at, and the value it is compared against are all pinned. -/

/-- Whether a term is a read of the global named `nm` at the location id `i`, of
type `t`, at the memory `m`. -/
def isGlobReadAt {t : EcTy} (e : EcTerm t) (nm : String) (i : Nat)
    (m : EcMemRef) : Bool :=
  match e.globRead with
  | some (g, m') => g.name == nm && g.id == i && g.ty == t && m' == m
  | none => false

/-- Whether a term is the `bool` literal `v`. -/
def isBoolLit {t : EcTy} (e : EcTerm t) (v : Bool) : Bool :=
  match t, e.litValue with
  | .bool, some w => w == v
  | _, _ => false

/-- Whether a term is the `int` literal `v`. -/
def isIntLit {t : EcTy} (e : EcTerm t) (v : Int) : Bool :=
  match t, e.litValue with
  | .int, some w => w == v
  | _, _ => false

/-- The exporter's output for the Hoare-judgement theory, as text. -/
def hoareExportText : String := include_str "hoare.expected.json"

/-- The exporter's output for the Hoare-judgement theory. -/
def hoareExport : Json :=
  match Json.parse hoareExportText with
  | .ok j => j
  | .error _ => Json.null

/-- The tables the statements of that theory decode against: the prelude extended
with the `var` declarations of `Coin`, so a global read in a formula has a
location, and the signatures of `Coin`'s procedures, so a judgement over one of
them has a signature. -/
def hoareTables : Except String FormTables := do
  let e ← decodeEnvelope hoareExport
  let it ← findItem e "Coin"
  let S ← decodeStructure ecPrelude 0 it
  .ok (formTables (S.globals.foldl DecodeTables.withGlobal ecPrelude)
        (procSigsOfStructure S))

/-- Decode the statement of the lemma `name` from that theory. -/
def hoareStatement (name : String) : Except String EcForm := do
  let F ← hoareTables
  importAxiom F name hoareExport

-- The fixture parses, and it is an export of the source file it claims.
#guard (match decodeEnvelope hoareExport with
        | .ok e => e.source == "tests/hoare.ec" && e.root == "Top"
        | _ => false)

-- Both procedures of `Coin` are argument-free and return a bit, and the module's
-- one global is a `bool` at the location id the base id 0 gives it.
#guard (match hoareTables with
        | .ok F =>
          F.procSigs == [("Top.Coin./set", ⟨.unit, .bool⟩),
                         ("Top.Coin./toss", ⟨.unit, .bool⟩)]
            && (match F.tables.globals with
                | [("Top.Coin./b", { name := "Top.Coin./b", id := 0, ty := .bool, .. })] => true
                | _ => false)
        | _ => false)

-- `hoare [Coin.set : Coin.b = false ==> res /\ Coin.b = true]` decodes to a Hoare
-- judgement at the unit argument, with the global read at the judgement's memory
-- in both assertions and the result read in the postcondition.
#guard (match hoareStatement "set_sets" with
        | .ok (.hoare "Top.Coin./set" ⟨.unit, .bool⟩ (.lit ()) (.eqT a₁ b₁)
                 (.and (.holds (.res .bool .cur)) (.eqT a₂ b₂))) =>
          isGlobReadAt a₁ "Top.Coin./b" 0 (.side .cur) && isBoolLit b₁ false
            && isGlobReadAt a₂ "Top.Coin./b" 0 (.side .cur) && isBoolLit b₂ true
        | _ => false)

-- `phoare [Coin.toss : true ==> true] = 1%r` decodes to a bounded Hoare judgement
-- at `EcCmp.eq` and the bound `1`. This pattern and the two below pin the value of
-- the bound as well as the shape of the statement, since `EcRealLit` carries the
-- numeral the decoder read.
#guard (match hoareStatement "toss_lossless" with
        | .ok (.bdHoare "Top.Coin./toss" ⟨.unit, .bool⟩ (.lit ()) .tru .tru EcCmp.eq (EcRealLit.mk 1 1)) => true
        | _ => false)

-- `phoare [Coin.toss : Coin.b = false ==> res] <= 1%r` decodes at `EcCmp.le`.
#guard (match hoareStatement "toss_le" with
        | .ok (.bdHoare "Top.Coin./toss" ⟨.unit, .bool⟩ (.lit ()) (.eqT a b)
                 (.holds (.res .bool .cur)) EcCmp.le (EcRealLit.mk 1 1)) =>
          isGlobReadAt a "Top.Coin./b" 0 (.side .cur) && isBoolLit b false
        | _ => false)

-- `phoare [Coin.toss : true ==> res /\ Coin.b = true] >= 0%r` decodes at
-- `EcCmp.ge`.
#guard (match hoareStatement "toss_ge" with
        | .ok (.bdHoare "Top.Coin./toss" ⟨.unit, .bool⟩ (.lit ()) .tru
                 (.and (.holds (.res .bool .cur)) (.eqT a b)) EcCmp.ge (EcRealLit.mk 0 1)) =>
          isGlobReadAt a "Top.Coin./b" 0 (.side .cur) && isBoolLit b true
        | _ => false)

/-! ### An integer term in a probability event

`ints.expected.json`, the export of `tests/ints.ec` in the exporter's tree, has a
lemma whose event compares the integer result of a procedure with an integer
literal. -/

/-- The exporter's output for the integer theory, as text. -/
def intsFormExportText : String := include_str "ints.expected.json"

/-- The exporter's output for the integer theory. -/
def intsFormExport : Json :=
  match Json.parse intsFormExportText with
  | .ok j => j
  | .error _ => Json.null

/-- The tables the statements of that theory decode against: the signature of
`Counter.main`, whose result is an integer. -/
def intsFormTables : Except String FormTables := do
  let e ← decodeEnvelope intsFormExport
  let it ← findItem e "Counter"
  let S ← decodeStructure ecPrelude 0 it
  .ok (formTables ecPrelude (procSigsOfStructure S))

/-- Decode the statement of the lemma `name` from that theory. -/
def intsFormStatement (name : String) : Except String EcForm := do
  let F ← intsFormTables
  importAxiom F name intsFormExport

-- `Counter.main` is declared from unit to int.
#guard (match intsFormTables with
        | .ok F => F.procSigs == [("Top.Counter./main", ⟨.unit, .int⟩)]
        | _ => false)

-- `forall &m, Pr[Counter.main() @ &m : res = 0] <= 1%r` decodes to a memory
-- quantifier over a comparison whose left side is the probability of an event
-- equating the integer result with the integer literal `0`.
#guard (match intsFormStatement "counter_bound" with
        | .ok (.allMem "&m"
                (.probCmp .le
                  (.pr "Top.Counter./main" ⟨.unit, .int⟩ (.lit ()) (.named "&m")
                     (.eqT (.res .int .cur) z))
                  (EcProb.const (EcRealLit.mk 1 1)))) => isIntLit z 0
        | _ => false)

/-- The tables with no procedure and no binder, for the nodes below, which no
`.ec` source produces: EasyCrypt builds a statement judgement in a tactic state
rather than in a lemma statement. -/
private def bareTables : FormTables := formTables ecPrelude []

/-- A judgement node over a statement, at the kind `k`. -/
private def jStmtJudgement (k : String) : Json :=
  Json.mkObj
    [("ty", Json.mkObj [("kind", Json.str "Tconstr"),
                        ("path", Json.str "Top.Pervasive.bool"),
                        ("args", Json.arr #[])]),
     ("kind", Json.str k)]

-- The three statement judgements are rejected by kind, before any field of
-- theirs is read.
#guard (match decodeForm bareTables (jStmtJudgement "FhoareS") with
        | .error _ => true
        | _ => false)

#guard (match decodeForm bareTables (jStmtJudgement "FbdHoareS") with
        | .error _ => true
        | _ => false)

#guard (match decodeForm bareTables (jStmtJudgement "FequivS") with
        | .error _ => true
        | _ => false)

/-- The `bool` type node. -/
private def jFormBool : Json :=
  Json.mkObj [("kind", Json.str "Tconstr"),
              ("path", Json.str "Top.Pervasive.bool"), ("args", Json.arr #[])]

/-- The `real` type node. -/
private def jFormReal : Json :=
  Json.mkObj [("kind", Json.str "Tconstr"),
              ("path", Json.str "Top.Pervasive.real"), ("args", Json.arr #[])]

/-- A nullary real operator node. -/
private def jRealOp (p : String) : Json :=
  Json.mkObj [("ty", jFormReal), ("kind", Json.str "Fop"), ("path", Json.str p),
              ("targs", Json.arr #[])]

/-- An application of the real operator `p`. -/
private def jRealApp (p : String) (args : Array Json) : Json :=
  Json.mkObj [("ty", jFormReal), ("kind", Json.str "Fapp"), ("f", jRealOp p),
              ("args", Json.arr args)]

/-- The real literal `0`. -/
private def jRealZero : Json :=
  jRealApp "Top.CoreReal.from_int"
    #[Json.mkObj [("ty", Json.mkObj [("kind", Json.str "Tconstr"),
                                     ("path", Json.str "Top.Pervasive.int"),
                                     ("args", Json.arr #[])]),
                  ("kind", Json.str "Fint"), ("value", Json.str "0")]]

-- A real literal decodes to a constant probability.
#guard (match decodeProb bareTables jRealZero with
        | .ok (EcProb.const (EcRealLit.mk 0 1)) => true
        | _ => false)

-- A signed difference of two probabilities is rejected: `ℝ≥0∞` subtraction is
-- truncated, so the difference has no faithful image.
#guard (match decodeProb bareTables
            (jRealApp "Top.CoreReal.add"
              #[jRealZero, jRealApp "Top.CoreReal.opp" #[jRealZero]]) with
        | .error _ => true
        | _ => false)

-- Its absolute value is the one shape with an image.
#guard (match decodeProb bareTables
            (jRealApp "Top.Real.`|_|"
              #[jRealApp "Top.CoreReal.add"
                  #[jRealZero, jRealApp "Top.CoreReal.opp" #[jRealZero]]]) with
        | .ok (.absDiff (EcProb.const (EcRealLit.mk 0 1)) (EcProb.const (EcRealLit.mk 0 1))) => true
        | _ => false)

-- A quotient is rejected.
#guard (match decodeProb bareTables
            (jRealApp "Top.CoreReal.div" #[jRealZero, jRealZero]) with
        | .error _ => true
        | _ => false)

-- `res` at a memory no judgement binds is rejected, rather than read at a
-- default side.
#guard (match decodeTerm bareTables .bool
            (Json.mkObj
              [("ty", jFormBool), ("kind", Json.str "Fpvar"),
               ("pv", Json.mkObj [("kind", Json.str "PVloc"),
                                  ("name", Json.str "res")]),
               ("mem", Json.mkObj [("name", Json.str "&hr"),
                                   ("stamp", Json.num 7)])]) with
        | .error _ => true
        | _ => false)

/-- The `int` type node. -/
private def jFormInt : Json :=
  Json.mkObj [("kind", Json.str "Tconstr"),
              ("path", Json.str "Top.Pervasive.int"), ("args", Json.arr #[])]

-- An integer term decodes to a literal at the `int` code.
#guard (match decodeTerm bareTables .int
            (Json.mkObj [("ty", jFormInt), ("kind", Json.str "Fint"),
                         ("value", Json.str "3")]) with
        | .ok e => isIntLit e 3
        | _ => false)

-- A negative integer term decodes at the same code.
#guard (match decodeTerm bareTables .int
            (Json.mkObj [("ty", jFormInt), ("kind", Json.str "Fint"),
                         ("value", Json.str "-3")]) with
        | .ok e => isIntLit e (-3)
        | _ => false)

-- An integer term at another code is rejected, rather than coerced.
#guard (match decodeTerm bareTables .bool
            (Json.mkObj [("ty", jFormBool), ("kind", Json.str "Fint"),
                         ("value", Json.str "3")]) with
        | .error _ => true
        | _ => false)

/-- A nullary operator read, at the type node `ty`. -/
private def jFormNullary (ty : Json) (p : String) : Json :=
  Json.mkObj [("ty", ty), ("kind", Json.str "Fop"), ("path", Json.str p),
              ("targs", Json.arr #[])]

/-- The type node of `int option`. -/
private def jFormIntOption : Json :=
  Json.mkObj [("kind", Json.str "Tconstr"), ("path", Json.str "Top.Logic.option"),
              ("args", Json.arr #[jFormInt])]

/-- The type node of `int list`. -/
private def jFormIntList : Json :=
  Json.mkObj [("kind", Json.str "Tconstr"), ("path", Json.str "Top.List.list"),
              ("args", Json.arr #[jFormInt])]

-- The canonical nullary values read in a term at the codes that have one, at the
-- same value the expression layer gives the same path.
#guard (match decodeTerm bareTables (.option .int)
            (jFormNullary jFormIntOption "Top.Logic.None") with
        | .ok (.lit v) => v == EcTy.noneVal (a := .int)
        | _ => false)
#guard (match decodeTerm bareTables (.list .int)
            (jFormNullary jFormIntList "Top.List.[]") with
        | .ok (.lit v) => v == EcTy.listEmpty (a := .int)
        | _ => false)

-- A code with no such value is rejected, rather than given the canonical
-- inhabitant of whatever code the context asks for. The node's own type says
-- `int`, so this is the read the type checker admits.
#guard (match decodeTerm bareTables .int
            (jFormNullary jFormInt "Top.Logic.None") with
        | .error m => m.startsWith "ec-import: 'Top.Logic.None' at type"
        | _ => false)

-- `witness` is the canonical inhabitant at any code, the reading `oget` takes.
#guard (match decodeTerm bareTables .int
            (jFormNullary jFormInt "Top.Pervasive.witness") with
        | .ok (.lit v) => v == (default : EcTy.int.interp)
        | _ => false)

/-- The type node of `int -> int`. -/
private def jFormIntFun : Json :=
  Json.mkObj [("kind", Json.str "Tfun"), ("dom", jFormInt), ("cod", jFormInt)]

/-- The lambda `fun x => x` at `int -> int`. -/
private def jFormIntId : Json :=
  Json.mkObj
    [("ty", jFormIntFun), ("kind", Json.str "Fquant"),
     ("quant", Json.str "Llambda"),
     ("binders", Json.arr
       #[Json.mkObj [("name", Json.str "x"), ("stamp", Json.num 91)]]),
     ("body", Json.mkObj
        [("ty", jFormInt), ("kind", Json.str "Flocal"),
         ("name", Json.str "x"), ("stamp", Json.num 91)])]

/-- `omap f o` at the result type node `res`, over the function node `f` and the
option node `o`. -/
private def jFormOmapAt (res f o : Json) : Json :=
  Json.mkObj
    [("ty", res), ("kind", Json.str "Fapp"),
     ("f", Json.mkObj
       [("ty", Json.mkObj
          [("kind", Json.str "Tfun"), ("dom", jFormIntFun),
           ("cod", Json.mkObj
             [("kind", Json.str "Tfun"), ("dom", jFormIntOption),
              ("cod", jFormIntOption)])]),
        ("kind", Json.str "Fop"), ("path", Json.str "Top.Logic.omap"),
        ("targs", Json.arr #[jFormInt, jFormInt])]),
     ("args", Json.arr #[f, o])]

-- `omap` reads the element code off its option argument, which is where the
-- result does not carry it.
#guard (match decodeTerm bareTables (.option .int)
            (jFormOmapAt jFormIntOption jFormIntId
              (jFormNullary jFormIntOption "Top.Logic.None")) with
        | .ok (.optionMap (a := .int) _ o) =>
            o.litValue == some (EcTy.noneVal (a := .int))
        | _ => false)

-- The function argument is read at the arrow from the element code to the
-- result's, so the lambda becomes a binder over a read of that binder.
#guard (match decodeTerm bareTables (.option .int)
            (jFormOmapAt jFormIntOption jFormIntId
              (jFormNullary jFormIntOption "Top.Logic.None")) with
        | .ok (.optionMap (.lam .int x (.var .int y)) _) => x == y
        | _ => false)

-- An argument that is no option is rejected, rather than read at the result's
-- element code.
#guard (match decodeTerm bareTables (.option .int)
            (jFormOmapAt jFormIntOption jFormIntId
              (jFormNullary jFormInt "Top.Pervasive.witness")) with
        | .error m => m.startsWith "ec-import: 'Top.Logic.omap' is applied to"
        | _ => false)

-- At a code that is no option the application is rejected: the image of an
-- option is an option.
#guard (match decodeTerm bareTables .int
            (jFormOmapAt jFormInt jFormIntId
              (jFormNullary jFormIntOption "Top.Logic.None")) with
        | .error m => m.startsWith "ec-import: 'Top.Logic.omap' at type"
        | _ => false)

/-- The `int distr` type node. -/
private def jFormIntDistr : Json :=
  Json.mkObj [("kind", Json.str "Tconstr"),
              ("path", Json.str "Top.Distr.distr"),
              ("args", Json.arr #[jFormInt])]

/-- The `int -> bool` type node. -/
private def jFormIntPred : Json :=
  Json.mkObj [("kind", Json.str "Tfun"), ("dom", jFormInt), ("cod", jFormBool)]

/-- The `int -> int distr` type node. -/
private def jFormIntToDistrTy : Json :=
  Json.mkObj [("kind", Json.str "Tfun"), ("dom", jFormInt),
              ("cod", jFormIntDistr)]

/-- The lambda `fun x => witness` at `int -> int distr`. -/
private def jFormIntToDistr : Json :=
  Json.mkObj
    [("ty", jFormIntToDistrTy), ("kind", Json.str "Fquant"),
     ("quant", Json.str "Llambda"),
     ("binders", Json.arr
       #[Json.mkObj [("name", Json.str "x"), ("stamp", Json.num 92)]]),
     ("body", jFormNullary jFormIntDistr "Top.Pervasive.witness")]

/-- `dmap d f` at the result type node `res`, over the distribution node `d` and
the function node `f`. -/
private def jFormDmapAt (res d f : Json) : Json :=
  Json.mkObj
    [("ty", res), ("kind", Json.str "Fapp"),
     ("f", Json.mkObj
       [("ty", Json.mkObj
          [("kind", Json.str "Tfun"), ("dom", jFormIntDistr),
           ("cod", Json.mkObj
             [("kind", Json.str "Tfun"), ("dom", jFormIntFun), ("cod", res)])]),
        ("kind", Json.str "Fop"), ("path", Json.str "Top.Distr.dmap"),
        ("targs", Json.arr #[jFormInt, jFormInt])]),
     ("args", Json.arr #[d, f])]

-- `dmap` reads the source code off its distribution argument and the function
-- at the arrow from that code to the result's.
#guard (match decodeTerm bareTables (.distr .int)
            (jFormDmapAt jFormIntDistr
              (jFormNullary jFormIntDistr "Top.Pervasive.witness")
              jFormIntId) with
        | .ok (.distrMap (a := .int) (.lit _) (.lam .int x (.var .int y))) =>
            x == y
        | _ => false)

-- A first argument that is no distribution is rejected, rather than read at the
-- result's carrier.
#guard (match decodeTerm bareTables (.distr .int)
            (jFormDmapAt jFormIntDistr
              (jFormNullary jFormInt "Top.Pervasive.witness") jFormIntId) with
        | .error m => m.startsWith "ec-import: 'Top.Distr.dmap' is applied to"
        | _ => false)

-- At a code that is no distribution the application is rejected: a pushforward
-- is a distribution.
#guard (match decodeTerm bareTables .int
            (jFormDmapAt jFormInt
              (jFormNullary jFormIntDistr "Top.Pervasive.witness")
              jFormIntId) with
        | .error m => m.startsWith "ec-import: 'Top.Distr.dmap' at type"
        | _ => false)

/-- `dlet d f` at the result type node `res`, over the distribution node `d` and
the distribution-valued function node `f`. -/
private def jFormDletAt (res d f : Json) : Json :=
  Json.mkObj
    [("ty", res), ("kind", Json.str "Fapp"),
     ("f", Json.mkObj
       [("ty", Json.mkObj
          [("kind", Json.str "Tfun"), ("dom", jFormIntDistr),
           ("cod", Json.mkObj
             [("kind", Json.str "Tfun"), ("dom", jFormIntToDistrTy),
              ("cod", res)])]),
        ("kind", Json.str "Fop"), ("path", Json.str "Top.Distr.dlet"),
        ("targs", Json.arr #[jFormInt, jFormInt])]),
     ("args", Json.arr #[d, f])]

-- `dlet` reads its function at the arrow from the source code into the result,
-- so the lambda becomes a binder over a distribution term.
#guard (match decodeTerm bareTables (.distr .int)
            (jFormDletAt jFormIntDistr
              (jFormNullary jFormIntDistr "Top.Pervasive.witness")
              jFormIntToDistr) with
        | .ok (.distrLet (a := .int) (.lit _) (.lam .int _ (.lit _))) => true
        | _ => false)

-- At a code that is no distribution the application is rejected: a bind is a
-- distribution.
#guard (match decodeTerm bareTables .int
            (jFormDletAt jFormInt
              (jFormNullary jFormIntDistr "Top.Pervasive.witness")
              jFormIntToDistr) with
        | .error m => m.startsWith "ec-import: 'Top.Distr.dlet' at type"
        | _ => false)

-- `predT` is the predicate every value satisfies, read unapplied at an arrow
-- code into `bool`.
#guard (match decodeTerm bareTables (.arrow .int .bool)
            (jFormNullary jFormIntPred "Top.Logic.predT") with
        | .ok (.lam .int _ (.lit v)) => v == true
        | _ => false)

-- At a code that is no such arrow the read is rejected.
#guard (match decodeTerm bareTables .bool
            (jFormNullary jFormBool "Top.Logic.predT") with
        | .error m => m.startsWith "ec-import: 'Top.Logic.predT' at type"
        | _ => false)

/-- `to_seq p` at the result type node `res`, over the predicate node `p`. -/
private def jFormToSeqAt (res p : Json) : Json :=
  Json.mkObj
    [("ty", res), ("kind", Json.str "Fapp"),
     ("f", Json.mkObj
       [("ty", Json.mkObj
          [("kind", Json.str "Tfun"), ("dom", jFormIntPred), ("cod", res)]),
        ("kind", Json.str "Fop"), ("path", Json.str "Top.Finite.to_seq"),
        ("targs", Json.arr #[jFormInt])]),
     ("args", Json.arr #[p])]

-- `to_seq` reads its element code off the result, which is a list at it, and
-- its predicate at the arrow from that code into `bool`.
#guard (match decodeTerm bareTables (.list .int)
            (jFormToSeqAt jFormIntList
              (jFormNullary jFormIntPred "Top.Logic.predT")) with
        | .ok (.toSeq (a := .int) (.lam .int _ (.lit v))) => v == true
        | _ => false)

-- At a code that is no list the application is rejected: the values a predicate
-- holds of are a list.
#guard (match decodeTerm bareTables .int
            (jFormToSeqAt jFormInt
              (jFormNullary jFormIntPred "Top.Logic.predT")) with
        | .error m => m.startsWith "ec-import: 'Top.Finite.to_seq' at type"
        | _ => false)

/-- `finite_type` read at the result type node `res` with the type arguments
`targs`. -/
private def jFormFiniteTypeAt (res : Json) (targs : Array Json) : Json :=
  Json.mkObj
    [("ty", res), ("kind", Json.str "Fop"),
     ("path", Json.str "Top.Finite.finite_type"), ("targs", Json.arr targs)]

-- `finite_type` is nullary and carries the code it asserts finiteness of as its
-- type argument, which the term's own `bool` code does not fix.
#guard (match decodeTerm bareTables .bool
            (jFormFiniteTypeAt jFormBool #[jFormBool]) with
        | .ok (.finiteType .bool) => true
        | _ => false)

-- A read with no type argument is rejected, rather than resolved at the code
-- the context asks for.
#guard (match decodeTerm bareTables .bool
            (jFormFiniteTypeAt jFormBool #[]) with
        | .error m =>
            m.startsWith "ec-import: 'Top.Finite.finite_type' read with"
        | _ => false)

-- At a code that is no boolean the read is rejected.
#guard (match decodeTerm bareTables .int
            (jFormFiniteTypeAt jFormInt #[jFormBool]) with
        | .error m => m.startsWith "ec-import: 'Top.Finite.finite_type' at type"
        | _ => false)

/-- An integer literal node at the `int` code. -/
private def jFormIntLit (v : String) : Json :=
  Json.mkObj [("ty", jFormInt), ("kind", Json.str "Fint"), ("value", Json.str v)]

/-- An application of the integer operator `p` at the result type node `res`. -/
private def jFormIntApp (res : Json) (p : String) (args : Array Json) : Json :=
  Json.mkObj
    [("ty", res), ("kind", Json.str "Fapp"),
     ("f", Json.mkObj [("ty", jFormInt), ("kind", Json.str "Fop"),
                       ("path", Json.str p), ("targs", Json.arr #[])]),
     ("args", Json.arr args)]

-- Integer addition in a term decodes at the `int` code.
#guard (match decodeTerm bareTables .int
            (jFormIntApp jFormInt "Top.CoreInt.add"
              #[jFormIntLit "1", jFormIntLit "2"]) with
        | .ok (.intAdd a b) => isIntLit a 1 && isIntLit b 2
        | _ => false)

-- Multiplication and negation decode at the `int` code.
#guard (match decodeTerm bareTables .int
            (jFormIntApp jFormInt "Top.CoreInt.mul"
              #[jFormIntLit "1", jFormIntLit "2"]) with
        | .ok (.intMul a b) => isIntLit a 1 && isIntLit b 2
        | _ => false)
#guard (match decodeTerm bareTables .int
            (jFormIntApp jFormInt "Top.CoreInt.opp" #[jFormIntLit "3"]) with
        | .ok (.intOpp a) => isIntLit a 3
        | _ => false)

/-- The type node `int * int`, which is what `edivz` returns. -/
private def jFormIntPair : Json :=
  Json.mkObj [("kind", Json.str "Ttuple"),
              ("args", Json.arr #[jFormInt, jFormInt])]

-- `edivz` decodes at the pair code, which `%/` and `%%` project out of.
#guard (match decodeTerm bareTables (.prod .int .int)
            (jFormIntApp jFormIntPair "Top.IntDiv.edivz"
              #[jFormIntLit "7", jFormIntLit "2"]) with
        | .ok (.intEdivz a b) => isIntLit a 7 && isIntLit b 2
        | _ => false)

-- Euclidean division is what `edivz` denotes: the remainder is non-negative
-- whatever the signs, and a zero divisor gives the quotient zero and the
-- dividend as remainder, which is EasyCrypt's `edivn m 0 = (0, m)`.
#guard (Int.ediv (-7) 2, Int.emod (-7) 2) == ((-4 : Int), (1 : Int))
#guard (Int.ediv (-7) (-2), Int.emod (-7) (-2)) == ((4 : Int), (1 : Int))
#guard (Int.ediv 5 0, Int.emod 5 0) == ((0 : Int), (5 : Int))

-- The absolute value and the greatest common divisor decode at the `int` code.
#guard (match decodeTerm bareTables .int
            (jFormIntApp jFormInt "Top.CoreInt.absz" #[jFormIntLit "-3"]) with
        | .ok (.intAbsz a) => isIntLit a (-3)
        | _ => false)
#guard (match decodeTerm bareTables .int
            (jFormIntApp jFormInt "Top.gcd"
              #[jFormIntLit "-4", jFormIntLit "-6"]) with
        | .ok (.intGcd a b) => isIntLit a (-4) && isIntLit b (-6)
        | _ => false)

-- `absz` is EasyCrypt's `fun x => (0 <= x) ? x : -x`: non-negative everywhere,
-- fixed at `0`, and the negation on the negatives.
#guard (Int.natAbs 0 : Int) == (0 : Int)
#guard (Int.natAbs 3 : Int) == (3 : Int)
#guard (Int.natAbs (-3) : Int) == (3 : Int)

-- `gcd` at the values its EasyCrypt characterization pins directly: `0` at the
-- pair `(0, 0)` its guard singles out, the absolute value when one argument is
-- `0`, `1` at an argument `1`, and invariant under either sign.
#guard (Int.gcd 0 0 : Int) == (0 : Int)
#guard (Int.gcd 0 (-5) : Int) == (5 : Int)
#guard (Int.gcd (-5) 0 : Int) == (5 : Int)
#guard (Int.gcd 1 (-7) : Int) == (1 : Int)
#guard (Int.gcd (-4) (-6) : Int) == (2 : Int)
#guard (Int.gcd 4 6 : Int) == (Int.gcd (-4) 6 : Int)

-- The order comparison decodes at the `bool` code.
#guard (match decodeTerm bareTables .bool
            (jFormIntApp jFormBool "Top.CoreInt.le"
              #[jFormIntLit "1", jFormIntLit "2"]) with
        | .ok (.intLe a b) => isIntLit a 1 && isIntLit b 2
        | _ => false)

-- The strict order has no constructor of its own: it decodes as the negation of
-- the reversed comparison, the shape `EcExpr.ltGuard` reads back at the
-- expression layer.
#guard (match decodeTerm bareTables .bool
            (jFormIntApp jFormBool "Top.CoreInt.lt"
              #[jFormIntLit "1", jFormIntLit "2"]) with
        | .ok (.bnot (.intLe a b)) => isIntLit a 2 && isIntLit b 1
        | _ => false)

/-! ### Finite-map lookup and update in a term -/

/-- The type node of `(int, bool) fmap`. -/
private def jFormIntBoolMap : Json :=
  Json.mkObj [("kind", Json.str "Tconstr"), ("path", Json.str "Top.FMap.fmap"),
              ("args", Json.arr #[jFormInt, jFormBool])]

/-- The type node of `bool option`. -/
private def jFormBoolOption : Json :=
  Json.mkObj [("kind", Json.str "Tconstr"), ("path", Json.str "Top.Logic.option"),
              ("args", Json.arr #[jFormBool])]

/-- The empty finite map at the `(int, bool) fmap` type node. -/
private def jFormEmptyMap : Json := jFormNullary jFormIntBoolMap "Top.FMap.empty"

/-- `m.[k]` at the result node `res`, over the arguments `args`. -/
private def jFormMapLookupAt (res : Json) (args : Array Json) : Json :=
  Json.mkObj
    [("ty", res), ("kind", Json.str "Fapp"),
     ("f", Json.mkObj
       [("ty", Json.mkObj
          [("kind", Json.str "Tfun"), ("dom", jFormIntBoolMap),
           ("cod", Json.mkObj
             [("kind", Json.str "Tfun"), ("dom", jFormInt), ("cod", res)])]),
        ("kind", Json.str "Fop"), ("path", Json.str "Top.FMap._.[_]"),
        ("targs", Json.arr #[jFormInt, jFormBool])]),
     ("args", Json.arr args)]

-- A lookup decodes at the option of the map's value code, and the key code comes
-- off the map argument's own type field.
#guard (match decodeTerm bareTables (.option .bool)
            (jFormMapLookupAt jFormBoolOption
              #[jFormEmptyMap, jFormIntLit "3"]) with
        | .ok (.mapFind _ k) => isIntLit k 3
        | _ => false)

-- An argument that is no finite map is rejected.
#guard (match decodeTerm bareTables (.option .bool)
            (jFormMapLookupAt jFormBoolOption
              #[jFormIntLit "0", jFormIntLit "3"]) with
        | .error m => m.startsWith "ec-import: 'Top.FMap._.[_]' is applied to"
        | _ => false)

-- A context expecting an option of another code is rejected: the map's value
-- code and the option's are the same code.
#guard (match decodeTerm bareTables (.option .int)
            (jFormMapLookupAt jFormIntOption
              #[jFormEmptyMap, jFormIntLit "3"]) with
        | .error m => m.startsWith "ec-import: 'Top.FMap._.[_]' reads a map of"
        | _ => false)

/-- `m.[k <- v]` at the `(int, bool) fmap` type node, over the arguments
`args`. -/
private def jFormMapSetAt (args : Array Json) : Json :=
  Json.mkObj
    [("ty", jFormIntBoolMap), ("kind", Json.str "Fapp"),
     ("f", Json.mkObj
       [("ty", Json.mkObj
          [("kind", Json.str "Tfun"), ("dom", jFormIntBoolMap),
           ("cod", Json.mkObj
             [("kind", Json.str "Tfun"), ("dom", jFormInt),
              ("cod", Json.mkObj
                [("kind", Json.str "Tfun"), ("dom", jFormBool),
                 ("cod", jFormIntBoolMap)])])]),
        ("kind", Json.str "Fop"), ("path", Json.str "Top.FMap._.[_<-_]"),
        ("targs", Json.arr #[jFormInt, jFormBool])]),
     ("args", Json.arr args)]

-- An update returns a map, so the result code fixes both the key and the value
-- code and no type field has to be read.
#guard (match decodeTerm bareTables (.map .int .bool)
            (jFormMapSetAt
              #[jFormEmptyMap, jFormIntLit "3",
                jFormNullary jFormBool "Top.Pervasive.true"]) with
        | .ok (.mapSet m k v) =>
            m.litValue == some ([] : (EcTy.map .int .bool).interp)
              && isIntLit k 3 && isBoolLit v true
        | _ => false)

-- An update applied to two arguments is rejected, rather than read as the
-- partial application.
#guard (match decodeTerm bareTables (.map .int .bool)
            (jFormMapSetAt #[jFormEmptyMap, jFormIntLit "3"]) with
        | .error m =>
          m.startsWith "ec-import: 'Top.FMap._.[_<-_]' applied to 2 arguments"
        | _ => false)

/-! ### `dom` and `m.[k]` at the spellings the operator table does not carry -/

/-- `dom` at the result node `res`, over the arguments `args`, at the spelling
`FMap.ec`'s own statements write it under. -/
private def jFormBareDomAt (res : Json) (args : Array Json) : Json :=
  Json.mkObj
    [("ty", res), ("kind", Json.str "Fapp"),
     ("f", Json.mkObj
       [("ty", Json.mkObj
          [("kind", Json.str "Tfun"), ("dom", jFormIntBoolMap),
           ("cod", jFormIntPred)]),
        ("kind", Json.str "Fop"), ("path", Json.str "Top.dom"),
        ("targs", Json.arr #[jFormInt, jFormBool])]),
     ("args", Json.arr args)]

-- `dom m k` is the membership test, and the key code comes off the map
-- argument's own type field.
#guard (match decodeTerm bareTables .bool
            (jFormBareDomAt jFormBool #[jFormEmptyMap, jFormIntLit "3"]) with
        | .ok (.mapMem _ k) => isIntLit k 3
        | _ => false)

-- `dom m` read at one argument is the predicate its definition gives, as a
-- lambda over the key.
#guard (match decodeTerm bareTables (.arrow .int .bool)
            (jFormBareDomAt jFormIntPred #[jFormEmptyMap]) with
        | .ok (.lam .int x (.mapMem _ (.var .int y))) => x == y
        | _ => false)

-- An argument that is no finite map is rejected.
#guard (match decodeTerm bareTables .bool
            (jFormBareDomAt jFormBool #[jFormIntLit "0", jFormIntLit "3"]) with
        | .error m => m.startsWith "ec-import: 'Top.dom' is applied to"
        | _ => false)

-- At a code that is neither a boolean nor a predicate the read is rejected.
#guard (match decodeTerm bareTables .int
            (jFormBareDomAt jFormInt #[jFormEmptyMap, jFormIntLit "3"]) with
        | .error m => m.startsWith "ec-import: 'Top.dom' at type"
        | _ => false)

/-- `m.[k]` at the result node `res`, over the arguments `args`, at the spelling
`FMap.ec`'s own statements write it under. -/
private def jFormBareLookupAt (res : Json) (args : Array Json) : Json :=
  Json.mkObj
    [("ty", res), ("kind", Json.str "Fapp"),
     ("f", Json.mkObj
       [("ty", Json.mkObj
          [("kind", Json.str "Tfun"), ("dom", jFormIntBoolMap),
           ("cod", Json.mkObj
             [("kind", Json.str "Tfun"), ("dom", jFormInt), ("cod", res)])]),
        ("kind", Json.str "Fop"), ("path", Json.str "Top._.[_]"),
        ("targs", Json.arr #[jFormInt, jFormBool])]),
     ("args", Json.arr args)]

-- The bare spelling reads the same lookup the qualified one does.
#guard (match decodeTerm bareTables (.option .bool)
            (jFormBareLookupAt jFormBoolOption
              #[jFormEmptyMap, jFormIntLit "3"]) with
        | .ok (.mapFind _ k) => isIntLit k 3
        | _ => false)

-- A context expecting an option of another code is rejected: the map's value
-- code and the option's are the same code.
#guard (match decodeTerm bareTables (.option .int)
            (jFormBareLookupAt jFormIntOption
              #[jFormEmptyMap, jFormIntLit "3"]) with
        | .error m => m.startsWith "ec-import: 'Top._.[_]' reads a map of"
        | _ => false)

/-! ### List catenation and the two distribution operators -/

/-- `s1 ++ s2` at the result node `res`, over the arguments `args`. -/
private def jFormCatAt (res : Json) (args : Array Json) : Json :=
  Json.mkObj
    [("ty", res), ("kind", Json.str "Fapp"),
     ("f", Json.mkObj
       [("ty", Json.mkObj
          [("kind", Json.str "Tfun"), ("dom", jFormIntList),
           ("cod", Json.mkObj
             [("kind", Json.str "Tfun"), ("dom", jFormIntList), ("cod", res)])]),
        ("kind", Json.str "Fop"), ("path", Json.str "Top.++"),
        ("targs", Json.arr #[jFormInt])]),
     ("args", Json.arr args)]

/-- The empty list at the `int list` type node. -/
private def jFormEmptyList : Json := jFormNullary jFormIntList "Top.List.[]"

-- Catenation decodes at the list code the result fixes, which is the code both
-- arguments are read at.
#guard (match decodeTerm bareTables (.list .int)
            (jFormCatAt jFormIntList #[jFormEmptyList, jFormEmptyList]) with
        | .ok (.listCat (a := .int) (.lit u) (.lit v)) =>
            u == EcTy.listEmpty (a := .int) && v == EcTy.listEmpty (a := .int)
        | _ => false)

-- At a code that is no list the application is rejected.
#guard (match decodeTerm bareTables .int
            (jFormCatAt jFormInt #[jFormEmptyList, jFormEmptyList]) with
        | .error m => m.startsWith "ec-import: 'Top.++' at type"
        | _ => false)

/-- The `(int * int) distr` type node. -/
private def jFormIntPairDistr : Json :=
  Json.mkObj [("kind", Json.str "Tconstr"),
              ("path", Json.str "Top.Distr.distr"),
              ("args", Json.arr #[jFormIntPair])]

/-- ``d1 `*` d2`` at the result node `res`, over the arguments `args`. -/
private def jFormDprodAt (res : Json) (args : Array Json) : Json :=
  Json.mkObj
    [("ty", res), ("kind", Json.str "Fapp"),
     ("f", Json.mkObj
       [("ty", Json.mkObj
          [("kind", Json.str "Tfun"), ("dom", jFormIntDistr),
           ("cod", Json.mkObj
             [("kind", Json.str "Tfun"), ("dom", jFormIntDistr), ("cod", res)])]),
        ("kind", Json.str "Fop"), ("path", Json.str "Top.Distr.`*`"),
        ("targs", Json.arr #[jFormInt, jFormInt])]),
     ("args", Json.arr args)]

/-- The canonical inhabitant at the `int distr` type node. -/
private def jFormWitnessDistr : Json :=
  jFormNullary jFormIntDistr "Top.Pervasive.witness"

-- The product decodes at a distribution over pairs, and each factor at the
-- component the pair's code gives.
#guard (match decodeTerm bareTables (.distr (.prod .int .int))
            (jFormDprodAt jFormIntPairDistr
              #[jFormWitnessDistr, jFormWitnessDistr]) with
        | .ok (.distrProd (a := .int) (b := .int) (.lit _) (.lit _)) => true
        | _ => false)

-- At a distribution over a code that is no pair the application is rejected.
#guard (match decodeTerm bareTables (.distr .int)
            (jFormDprodAt jFormIntDistr
              #[jFormWitnessDistr, jFormWitnessDistr]) with
        | .error m => m.startsWith "ec-import: 'Top.Distr.`*`' at type"
        | _ => false)

/-- `d \ p` at the result node `res`, over the arguments `args`. -/
private def jFormDexceptedAt (res : Json) (args : Array Json) : Json :=
  Json.mkObj
    [("ty", res), ("kind", Json.str "Fapp"),
     ("f", Json.mkObj
       [("ty", Json.mkObj
          [("kind", Json.str "Tfun"), ("dom", jFormIntDistr),
           ("cod", Json.mkObj
             [("kind", Json.str "Tfun"), ("dom", jFormIntPred), ("cod", res)])]),
        ("kind", Json.str "Fop"), ("path", Json.str "Top.Dexcepted.\\"),
        ("targs", Json.arr #[jFormInt])]),
     ("args", Json.arr args)]

-- The conditioned distribution decodes at the code of the distribution it
-- conditions, and the predicate at the arrow from that code into `bool`.
#guard (match decodeTerm bareTables (.distr .int)
            (jFormDexceptedAt jFormIntDistr
              #[jFormWitnessDistr,
                jFormNullary jFormIntPred "Top.Logic.predT"]) with
        | .ok (.distrExcept (a := .int) (.lit _) (.lam .int _ (.lit v))) =>
            v == true
        | _ => false)

-- At a code that is no distribution the application is rejected.
#guard (match decodeTerm bareTables .int
            (jFormDexceptedAt jFormInt
              #[jFormWitnessDistr,
                jFormNullary jFormIntPred "Top.Logic.predT"]) with
        | .error m => m.startsWith "ec-import: 'Top.Dexcepted.\\' at type"
        | _ => false)

/-! ### A quantifier in term position

EasyCrypt's propositions are values of `bool`, so `forall` and `exists` stand
wherever a boolean term does. The binder is carried by the term and the body
reads it, which is what a reading that dropped the binder or fixed a witness
would lose. -/

/-- A binder over the values of the type node `ty`, named `nm` at `st`. -/
private def jFormTyBinder (nm : String) (st : Nat) (ty : Json) : Json :=
  Json.mkObj
    [("name", Json.str nm), ("stamp", Json.num st),
     ("gty", Json.mkObj [("kind", Json.str "GTty"), ("ty", ty)])]

/-- A quantifier `q` over the binders `bs` with the body `body`, at the type
node `ty`. -/
private def jFormQuantAt (ty : Json) (q : String) (bs : Array Json)
    (body : Json) : Json :=
  Json.mkObj
    [("ty", ty), ("kind", Json.str "Fquant"), ("quant", Json.str q),
     ("binders", Json.arr bs), ("body", body)]

/-- The comparison `x <= 0` on the logical variable `x` at the stamp `st`. -/
private def jFormLeZero (st : Nat) : Json :=
  jFormIntApp jFormBool "Top.CoreInt.le"
    #[Json.mkObj [("ty", jFormInt), ("kind", Json.str "Flocal"),
                  ("name", Json.str "x"), ("stamp", Json.num st)],
      jFormIntLit "0"]

-- A universally quantified proposition in term position carries its binder, and
-- the body reads it as a logical variable of the same name.
#guard (match decodeTerm bareTables .bool
            (jFormQuantAt jFormBool "Lforall"
              #[jFormTyBinder "x" 93 jFormInt] (jFormLeZero 93)) with
        | .ok (.forallB .int x (.intLe (.var .int y) _)) => x == "x" && x == y
        | _ => false)

-- An existential decodes at the same code, under its own former.
#guard (match decodeTerm bareTables .bool
            (jFormQuantAt jFormBool "Lexists"
              #[jFormTyBinder "x" 93 jFormInt] (jFormLeZero 93)) with
        | .ok (.existsB .int x (.intLe (.var .int y) _)) => x == "x" && x == y
        | _ => false)

-- Several binders nest, the first binder outermost.
#guard (match decodeTerm bareTables .bool
            (jFormQuantAt jFormBool "Lforall"
              #[jFormTyBinder "y" 94 jFormBool,
                jFormTyBinder "x" 93 jFormInt] (jFormLeZero 93)) with
        | .ok (.forallB .bool "y" (.forallB .int "x" _)) => true
        | _ => false)

-- At a code that is no boolean the quantifier is rejected: an EasyCrypt
-- quantifier is a proposition.
#guard (match decodeTerm bareTables .int
            (jFormQuantAt jFormInt "Lforall"
              #[jFormTyBinder "x" 93 jFormInt] (jFormLeZero 93)) with
        | .error m => m.startsWith "ec-import: a quantified term in"
        | _ => false)

-- A binder that is no value of a type code is rejected, rather than dropped.
#guard (match decodeTerm bareTables .bool
            (jFormQuantAt jFormBool "Lforall"
              #[Json.mkObj
                  [("name", Json.str "m"), ("stamp", Json.num 95),
                   ("gty", Json.mkObj [("kind", Json.str "GTmem")])]]
              (jFormLeZero 93)) with
        | .error m => m.startsWith "ec-import: the binder 'm' of sort 'GTmem'"
        | _ => false)

-- A node the exporter marked as outside its coverage is rejected.
#guard (match decodeForm bareTables
            (Json.mkObj [("kind", Json.str "Unsupported"),
                         ("what", Json.str "Fmatch"),
                         ("pp", Json.str "match o with")]) with
        | .error _ => true
        | _ => false)

/-! ### An abstract operator read by a statement

The items below are the exported shapes of `crypto/PRF.eca`'s inner theory
`PseudoRF`, transcribed from an envelope of schema version 8:

```
type K.
op dK : K distr.
axiom dK_ll : is_lossless dK.
```

`dK` is a declaration, so the statement that reads it is a statement about every
realization of it: `decodeAxiom` produces the body, and `EcForm.assembleParams`
closes it under one binder — `EcForm.allConst` at the declared type, since the
declaration takes no argument. The read is matched with `EcTerm.opAppOf` rather
than by a pattern, because `EcTerm.opApp` is indexed by `s.res`, a projection out
of its own field. -/

/-- The type node of `PseudoRF`'s carrier. -/
private def jPRFK : Json :=
  Json.mkObj [("kind", Json.str "Tconstr"),
              ("path", Json.str "Top.PseudoRF.K"), ("args", Json.arr #[])]

/-- The type node of `K distr`. -/
private def jPRFDistrK : Json :=
  Json.mkObj [("kind", Json.str "Tconstr"),
              ("path", Json.str "Top.Distr.distr"), ("args", Json.arr #[jPRFK])]

/-- The `Th_theory` item holding `PseudoRF`'s carrier and its abstract
distribution. -/
private def jPRFDecls : Json :=
  Json.mkObj
    [("kind", Json.str "Th_theory"), ("name", Json.str "PseudoRF"),
     ("path", Json.str "Top.PseudoRF"), ("mode", Json.str "abstract"),
     ("source", Json.null),
     ("items", Json.arr
       #[jAbsTypeDecl "K" "Top.PseudoRF.K",
         Json.mkObj
           [("kind", Json.str "Th_operator"), ("name", Json.str "dK"),
            ("path", Json.str "Top.PseudoRF.dK"),
            ("decl", Json.mkObj
              [("tparams", Json.arr #[]), ("ty", jPRFDistrK),
               ("body", Json.mkObj [("kind", Json.str "Abstract")])])]])]

/-- The `Th_axiom` item of `axiom dK_ll : is_lossless dK.` -/
private def jPRFDKLL : Json :=
  Json.mkObj
    [("kind", Json.str "Th_axiom"), ("name", Json.str "dK_ll"),
     ("path", Json.str "Top.PseudoRF.dK_ll"),
     ("decl", Json.mkObj
       [("tparams", Json.arr #[]), ("axiom_kind", Json.str "Axiom"),
        ("spec", Json.mkObj
          [("ty", jFormBool), ("kind", Json.str "Fapp"),
           ("f", Json.mkObj
             [("ty", Json.mkObj
                [("kind", Json.str "Tfun"), ("dom", jPRFDistrK),
                 ("cod", jFormBool)]),
              ("kind", Json.str "Fop"),
              ("path", Json.str "Top.Distr.is_lossless"),
              ("targs", Json.arr #[jPRFK])]),
           ("args", Json.arr
             #[Json.mkObj
                 [("ty", jPRFDistrK), ("kind", Json.str "Fop"),
                  ("path", Json.str "Top.PseudoRF.dK"),
                  ("targs", Json.arr #[])]])])])]

/-- The tables `PseudoRF`'s statements decode against: its carrier at the opaque
code, then its abstract operators. -/
private def prfFormTables : FormTables :=
  formTables
    (registerThOperators (registerThTypes ecPrelude [jPRFDecls]) [jPRFDecls]) []

/-- The signature `dK`'s declaration gives it. -/
private def dKSig : EcSig := ⟨.unit, .distr (.opaque "Top.PseudoRF.K")⟩

-- `is_lossless dK` decodes to the losslessness assertion over the operator read
-- at the signature its declaration gives it.
#guard (match decodeAxiom prfFormTables jPRFDKLL with
        | .ok (.isLossless d) => d.opAppOf == some ("Top.PseudoRF.dK", dKSig)
        | _ => false)

-- The statement reads one operator and binds none, so assembling it binds that
-- one, and the assembled statement reads no free operator.
#guard (match decodeAxiom prfFormTables jPRFDKLL with
        | .ok f => EcForm.opsOf f == [("Top.PseudoRF.dK", dKSig)]
        | _ => false)

#guard (match decodeAxiom prfFormTables jPRFDKLL with
        | .ok f =>
          (match f.assembleParams with
           | .allConst "Top.PseudoRF.dK" t (.isLossless d) =>
               t == EcTy.distr (EcTy.opaque "Top.PseudoRF.K")
                 && d.opAppOf == some ("Top.PseudoRF.dK", dKSig)
           | _ => false)
            && EcForm.opsOf f.assembleParams == []
        | _ => false)

-- Without the operator declaration the same statement is rejected: the path is in
-- no table, so the read has no image and cannot default to one.
#guard (match decodeAxiom (formTables (registerThTypes ecPrelude [jPRFDecls]) [])
            jPRFDKLL with
        | .error m => m.startsWith "ec-import: unknown nullary operator path"
        | _ => false)

/-- The read of `dK` at its declared type node. -/
private def jPRFDKRead : Json :=
  Json.mkObj [("ty", jPRFDistrK), ("kind", Json.str "Fop"),
              ("path", Json.str "Top.PseudoRF.dK"), ("targs", Json.arr #[])]

/-- `support d x` at the result type node `res`, over the distribution node `d`
and the element node `x`. -/
private def jPRFSupportAt (res d x : Json) : Json :=
  Json.mkObj
    [("ty", res), ("kind", Json.str "Fapp"),
     ("f", Json.mkObj
       [("ty", Json.mkObj
          [("kind", Json.str "Tfun"), ("dom", jPRFDistrK),
           ("cod", Json.mkObj
             [("kind", Json.str "Tfun"), ("dom", jPRFK), ("cod", jFormBool)])]),
        ("kind", Json.str "Fop"), ("path", Json.str "Top.support"),
        ("targs", Json.arr #[jPRFK])]),
     ("args", Json.arr #[d, x])]

-- `support` reads the element code off its distribution argument, so the read
-- of `dK` carries the signature its declaration gives it.
#guard (match decodeTerm prfFormTables .bool
            (jPRFSupportAt jFormBool jPRFDKRead
              (jFormNullary jPRFK "Top.Pervasive.witness")) with
        | .ok (.support d _) => d.opAppOf == some ("Top.PseudoRF.dK", dKSig)
        | _ => false)

-- An argument that is no distribution is rejected.
#guard (match decodeTerm prfFormTables .bool
            (jPRFSupportAt jFormBool (jFormNullary jPRFK "Top.Pervasive.witness")
              (jFormNullary jPRFK "Top.Pervasive.witness")) with
        | .error m => m.startsWith "ec-import: 'Top.support' is applied to"
        | _ => false)

-- At a code that is not `bool` the application is rejected: membership in a
-- distribution's support is a boolean.
#guard (match decodeTerm prfFormTables .int
            (jPRFSupportAt jFormInt jPRFDKRead
              (jFormNullary jPRFK "Top.Pervasive.witness")) with
        | .error m => m.startsWith "ec-import: 'Top.support' at type"
        | _ => false)

/-- The type node of `K -> bool`, the code a predicate over `K` reads at. -/
private def jPRFPredK : Json :=
  Json.mkObj [("kind", Json.str "Tfun"), ("dom", jPRFK), ("cod", jFormBool)]

/-- `pred1 witness`, a predicate over `K`. -/
private def jPRFPred1Witness : Json :=
  Json.mkObj
    [("ty", jPRFPredK), ("kind", Json.str "Fapp"),
     ("f", Json.mkObj
       [("ty", Json.mkObj
          [("kind", Json.str "Tfun"), ("dom", jPRFK), ("cod", jPRFPredK)]),
        ("kind", Json.str "Fop"), ("path", Json.str "Top.Logic.pred1"),
        ("targs", Json.arr #[jPRFK])]),
     ("args", Json.arr #[jFormNullary jPRFK "Top.Pervasive.witness"])]

/-- `mu d P` at the `real` result node, over the distribution node `d` and the
predicate node `P`. -/
private def jPRFMuAt (d P : Json) : Json :=
  Json.mkObj
    [("ty", jFormReal), ("kind", Json.str "Fapp"),
     ("f", Json.mkObj
       [("ty", Json.mkObj
          [("kind", Json.str "Tfun"), ("dom", jPRFDistrK),
           ("cod", Json.mkObj
             [("kind", Json.str "Tfun"), ("dom", jPRFPredK),
              ("cod", jFormReal)])]),
        ("kind", Json.str "Fop"), ("path", Json.str "Top.Pervasive.mu"),
        ("targs", Json.arr #[jPRFK])]),
     ("args", Json.arr #[d, P])]

-- `mu` reads the element code off its distribution argument, so the read of `dK`
-- carries the signature its declaration gives it, and the predicate decodes at
-- the arrow code that element gives.
#guard (match decodeProb prfFormTables (jPRFMuAt jPRFDKRead jPRFPred1Witness) with
        | .ok (.mu d (.lam _ _ (.beq _ _))) =>
            d.opAppOf == some ("Top.PseudoRF.dK", dKSig)
        | _ => false)

-- An argument that is no distribution is rejected.
#guard (match decodeProb prfFormTables
            (jPRFMuAt (jFormNullary jPRFK "Top.Pervasive.witness")
              jPRFPred1Witness) with
        | .error m => m.startsWith "ec-import: 'Top.Pervasive.mu' is applied to"
        | _ => false)

/-! ### An applied abstract operator

The items below are the exported shapes of two corpus statements over
arrow-typed abstract operators, transcribed from envelopes of schema version 8.
`crypto/PRF.eca`'s inner theory `RF` declares one argument:

```
type D.
type R.

abstract theory RF.
  op dR : D -> R distr.
  axiom dR_ll : forall x, is_lossless (dR x).
end RF.
```

and `crypto/assumptions/AEAD.ec` declares three:

```
type K, AData, Msg, Cph.
op enc : K -> AData -> Msg -> Cph distr.
axiom enc_ll : forall k a m, is_lossless (enc k a m).
```

A declaration of `n` arguments is registered at the signature whose argument code
is those arguments' codes as a right-nested product, and a read of it decodes to
`EcTerm.opApp` at that signature, applied to the arguments in the same nesting
(`EcTerm.nestArgs`). The argument count comes from the application and the
argument codes from the declaration, so an application whose arguments do not
nest into the declared argument code is rejected naming both codes. Assembling
binds such a declaration with `EcForm.allOp`, the binder of a declaration whose
realization is a function. -/

/-- The type node of the argument-free type declared at `path`. -/
private def jTyNode (path : String) : Json :=
  Json.mkObj [("kind", Json.str "Tconstr"), ("path", Json.str path),
              ("args", Json.arr #[])]

/-- The type node of the distributions over the type declared at `path`. -/
private def jDistrNode (path : String) : Json :=
  Json.mkObj [("kind", Json.str "Tconstr"),
              ("path", Json.str "Top.Distr.distr"),
              ("args", Json.arr #[jTyNode path])]

/-- The binder of the logical variable `name` at the stamp `st`, ranging over the
type declared at `path`. -/
private def jTyBinder (name : String) (st : Nat) (path : String) : Json :=
  Json.mkObj
    [("name", Json.str name), ("stamp", Json.num st),
     ("gty", Json.mkObj
       [("kind", Json.str "GTty"), ("ty", jTyNode path)])]

/-- The read of the logical variable `name` at the stamp `st`, typed at the type
declared at `path`. -/
private def jLocalNode (name : String) (st : Nat) (path : String) : Json :=
  Json.mkObj
    [("ty", jTyNode path), ("kind", Json.str "Flocal"),
     ("name", Json.str name), ("stamp", Json.num st)]

/-- `is_lossless d` for a term `d` of the distributions over the type declared at
`path`. -/
private def jLosslessNode (path : String) (d : Json) : Json :=
  Json.mkObj
    [("ty", jFormBool), ("kind", Json.str "Fapp"),
     ("f", Json.mkObj
       [("ty", Json.mkObj
          [("kind", Json.str "Tfun"), ("dom", jDistrNode path),
           ("cod", jFormBool)]),
        ("kind", Json.str "Fop"),
        ("path", Json.str "Top.Distr.is_lossless"),
        ("targs", Json.arr #[jTyNode path])]),
     ("args", Json.arr #[d])]

/-- The application of the operator at `path`, whose declared type is `fty`, to
`args`, at the result type `resTy`. -/
private def jOpAppNode (path : String) (fty resTy : Json) (args : Array Json) :
    Json :=
  Json.mkObj
    [("ty", resTy), ("kind", Json.str "Fapp"),
     ("f", Json.mkObj
       [("ty", fty), ("kind", Json.str "Fop"), ("path", Json.str path),
        ("targs", Json.arr #[])]),
     ("args", Json.arr args)]

/-- The `Th_axiom` item of `RF`'s `axiom dR_ll : forall x, is_lossless (dR x).` -/
private def jRFDRLL : Json :=
  Json.mkObj
    [("kind", Json.str "Th_axiom"), ("name", Json.str "dR_ll"),
     ("path", Json.str "Top.RF.dR_ll"),
     ("decl", Json.mkObj
       [("tparams", Json.arr #[]), ("axiom_kind", Json.str "Axiom"),
        ("spec", Json.mkObj
          [("ty", jFormBool), ("kind", Json.str "Fquant"),
           ("quant", Json.str "Lforall"),
           ("binders", Json.arr #[jTyBinder "x" 95133 "Top.D"]),
           ("body", jLosslessNode "Top.R"
             (jOpAppNode "Top.RF.dR"
               (jTyArrow (jTyNode "Top.D") (jDistrNode "Top.R"))
               (jDistrNode "Top.R")
               #[jLocalNode "x" 95133 "Top.D"]))])])]

/-- The signature `dR`'s declaration gives it: one argument at the carrier `D`,
the distributions over `R` as the result. -/
private def dRSig : EcSig := ⟨.opaque "Top.D", .distr (.opaque "Top.R")⟩

/-- The tables `RF`'s statement decodes against: the two carriers at the opaque
codes, and `dR` at the signature its declared type gives it. -/
private def rfFormTables : FormTables :=
  formTables
    ((registerThTypes ecPrelude
        [jAbsTypeDecl "D" "Top.D", jAbsTypeDecl "R" "Top.R"]).withAbstractOp
      "Top.RF.dR" dRSig) []

-- The one argument is the quantified variable at its own code, so the read is an
-- `opApp` at the declaration's signature under the quantifier.
#guard (match decodeAxiom rfFormTables jRFDRLL with
        | .ok (.allTy t "x" (.isLossless d)) =>
            t == EcTy.opaque "Top.D"
              && d.opAppOf == some ("Top.RF.dR", dRSig)
        | _ => false)

-- The statement reads the declaration and binds none, so assembling it binds
-- that one with the signature binder, and reads no free operator.
#guard (match decodeAxiom rfFormTables jRFDRLL with
        | .ok f =>
          (match f.assembleParams with
           | .allOp "Top.RF.dR" s (.allTy _ "x" (.isLossless _)) => s == dRSig
           | _ => false)
            && EcForm.opsOf f.assembleParams == []
        | _ => false)

-- Without the declaration the same statement is rejected: the path is in no
-- table, so the application has no image and cannot default to one.
#guard (match decodeAxiom
            (formTables (registerThTypes ecPrelude
              [jAbsTypeDecl "D" "Top.D", jAbsTypeDecl "R" "Top.R"]) []) jRFDRLL with
        | .error m => m.startsWith "ec-import: unknown operator path 'Top.RF.dR'"
        | _ => false)

/-- The `Th_axiom` item of `axiom enc_ll : forall k a m, is_lossless (enc k a m).` -/
private def jAeadEncLL : Json :=
  Json.mkObj
    [("kind", Json.str "Th_axiom"), ("name", Json.str "enc_ll"),
     ("path", Json.str "Top.enc_ll"),
     ("decl", Json.mkObj
       [("tparams", Json.arr #[]), ("axiom_kind", Json.str "Axiom"),
        ("spec", Json.mkObj
          [("ty", jFormBool), ("kind", Json.str "Fquant"),
           ("quant", Json.str "Lforall"),
           ("binders", Json.arr
             #[jTyBinder "k" 97692 "Top.K", jTyBinder "a" 97694 "Top.AData",
               jTyBinder "m" 97696 "Top.Msg"]),
           ("body", jLosslessNode "Top.Cph"
             (jOpAppNode "Top.enc"
               (jTyArrow (jTyNode "Top.K")
                 (jTyArrow (jTyNode "Top.AData")
                   (jTyArrow (jTyNode "Top.Msg") (jDistrNode "Top.Cph"))))
               (jDistrNode "Top.Cph")
               #[jLocalNode "k" 97692 "Top.K", jLocalNode "a" 97694 "Top.AData",
                 jLocalNode "m" 97696 "Top.Msg"]))])])]

/-- The `Th_type` items of the four carriers `enc` is declared over. -/
private def jAeadCarriers : List Json :=
  [jAbsTypeDecl "K" "Top.K", jAbsTypeDecl "AData" "Top.AData",
   jAbsTypeDecl "Msg" "Top.Msg", jAbsTypeDecl "Cph" "Top.Cph"]

/-- The signature `enc`'s declaration gives it: its three arguments as the
right-nested product, the distributions over the ciphertexts as the result. -/
private def encSig : EcSig :=
  ⟨.prod (.opaque "Top.K") (.prod (.opaque "Top.AData") (.opaque "Top.Msg")),
   .distr (.opaque "Top.Cph")⟩

/-- The tables `AEAD.ec`'s statement decodes against: its four carriers at the
opaque codes, and `enc` at the signature its declared type gives it. -/
private def aeadFormTables : FormTables :=
  formTables
    ((registerThTypes ecPrelude jAeadCarriers).withAbstractOp "Top.enc" encSig) []

-- The three arguments ride the declared argument code as the right-nested pair,
-- so the read is one `opApp` at the declaration's signature.
#guard (match decodeAxiom aeadFormTables jAeadEncLL with
        | .ok (.allTy tk "k" (.allTy ta "a" (.allTy tm "m" (.isLossless d)))) =>
            tk == EcTy.opaque "Top.K" && ta == EcTy.opaque "Top.AData"
              && tm == EcTy.opaque "Top.Msg"
              && d.opAppOf == some ("Top.enc", encSig)
        | _ => false)

-- Assembling binds the declaration at that signature, and the assembled
-- statement reads no free operator.
#guard (match decodeAxiom aeadFormTables jAeadEncLL with
        | .ok f =>
          (match f.assembleParams with
           | .allOp "Top.enc" s (.allTy _ "k" (.allTy _ "a" (.allTy _ "m" _))) =>
               s == encSig
           | _ => false)
            && EcForm.opsOf f.assembleParams == []
        | _ => false)

-- The application is read against the declared argument code: the same statement
-- against a declaration of two arguments is rejected, since three arguments do
-- not nest into a two-component product.
#guard (match decodeAxiom
            (formTables ((registerThTypes ecPrelude jAeadCarriers).withAbstractOp
              "Top.enc" ⟨.prod (.opaque "Top.K") (.opaque "Top.AData"),
                         .distr (.opaque "Top.Cph")⟩) []) jAeadEncLL with
        | .error m =>
            m.startsWith "ec-import: the abstract operator 'Top.enc' is declared at"
        | _ => false)

-- A declaration at another result code is rejected too, naming the code the
-- context expects.
#guard (match decodeAxiom
            (formTables ((registerThTypes ecPrelude jAeadCarriers).withAbstractOp
              "Top.enc" ⟨encSig.arg, .opaque "Top.Cph"⟩) []) jAeadEncLL with
        | .error m =>
            m.startsWith "ec-import: the abstract operator 'Top.enc' is declared at"
        | _ => false)

/-- The right-nested product an applied operator's arguments carry is the one a
procedure's formals carry: the code `EcTerm.nestArgs` builds is `nestTuple` of
the arguments' codes, which is the domain `decodeSigDef` gives a procedure of the
same argument types. -/
theorem nestArgs_fst (a : (t : EcTy) × EcTerm t)
    (rest : List ((t : EcTy) × EcTerm t)) :
    (EcTerm.nestArgs a rest).1 = nestTuple a.1 (rest.map Sigma.fst) := by
  induction rest generalizing a with
  | nil => rfl
  | cons b rest ih => simp [EcTerm.nestArgs, nestTuple, ih]

/-! ### A lemma stated under its theory's imported axiom

The items below are the exported shapes of `crypto/DigitalSignaturesROM.eca`'s
theory `Top.StatelessROM.UUFKOAROM`, transcribed from an envelope of schema
version 8:

```
abstract theory UUFKOAROM.
  op [lossless] dmsg : msg_t distr.
  clone import UUFKOA with op dmsg <- dmsg
  proof *.
  realize dmsg_ll by exact: dmsg_ll.
end UUFKOAROM.
```

`op [lossless] dmsg` declares the operator and the axiom `dmsg_ll` constraining
it; the clone's own `dmsg_ll` is realized, so the export carries it as
`axiom_kind: Lemma` one scope in, at
`Top.StatelessROM.UUFKOAROM.UUFKOA.dmsg_ll`. The lemma's own theory declares no
axiom, so this is the pair that fixes the scope rule: the premise the lemma is
proved from is declared in the enclosing theory.

The declared type of `dmsg` is at `Top.Pervasive.distr`, EasyCrypt's declaration
of `'a distr`; `Top.Distr.distr`, the path `ecPrelude` carries, is the alias
`Distr.ec` defines for it. The export writes both — the operator's declared type
at the declaration path, the argument type of `is_lossless` in the lemma at the
alias — so the tables below register the declaration path alongside it. -/

/-- The type node of `msg_t`, the carrier the messages are drawn from. -/
private def jMsgTy : Json :=
  Json.mkObj [("kind", Json.str "Tconstr"), ("path", Json.str "Top.msg_t"),
              ("args", Json.arr #[])]

/-- The type node of `msg_t distr` at EasyCrypt's declaration of `'a distr`. -/
private def jMsgDistrTy : Json :=
  Json.mkObj [("kind", Json.str "Tconstr"),
              ("path", Json.str "Top.Pervasive.distr"),
              ("args", Json.arr #[jMsgTy])]

/-- The type node of `msg_t distr` at `Distr.ec`'s alias. -/
private def jMsgDistrTyAlias : Json :=
  Json.mkObj [("kind", Json.str "Tconstr"),
              ("path", Json.str "Top.Distr.distr"),
              ("args", Json.arr #[jMsgTy])]

/-- The `Th_type` item of `type msg_t.` -/
private def jMsgT : Json := jAbsTypeDecl "msg_t" "Top.msg_t"

/-- The `Th_operator` item of `op dmsg : msg_t distr.` -/
private def jDmsg : Json :=
  Json.mkObj
    [("kind", Json.str "Th_operator"), ("name", Json.str "dmsg"),
     ("path", Json.str "Top.StatelessROM.UUFKOAROM.dmsg"),
     ("decl", Json.mkObj
       [("tparams", Json.arr #[]), ("ty", jMsgDistrTy),
        ("body", Json.mkObj [("kind", Json.str "Abstract")])])]

/-- The statement `is_lossless dmsg`, whose applied predicate the export types at
`domTy`. -/
private def jDmsgLosslessSpec (domTy : Json) : Json :=
  Json.mkObj
    [("ty", jFormBool), ("kind", Json.str "Fapp"),
     ("f", Json.mkObj
       [("ty", Json.mkObj
          [("kind", Json.str "Tfun"), ("dom", domTy), ("cod", jFormBool)]),
        ("kind", Json.str "Fop"),
        ("path", Json.str "Top.Distr.is_lossless"),
        ("targs", Json.arr #[jMsgTy])]),
     ("args", Json.arr
       #[Json.mkObj
           [("ty", jMsgDistrTy), ("kind", Json.str "Fop"),
            ("path", Json.str "Top.StatelessROM.UUFKOAROM.dmsg"),
            ("targs", Json.arr #[])]])]

/-- The `Th_axiom` item the operator's `[lossless]` annotation declares. -/
private def jDmsgLLAxiom : Json :=
  Json.mkObj
    [("kind", Json.str "Th_axiom"), ("name", Json.str "dmsg_ll"),
     ("path", Json.str "Top.StatelessROM.UUFKOAROM.dmsg_ll"),
     ("decl", Json.mkObj
       [("tparams", Json.arr #[]), ("axiom_kind", Json.str "Axiom"),
        ("spec", jDmsgLosslessSpec jMsgDistrTy)])]

/-- The `Th_axiom` item of the clone's realized `dmsg_ll`. -/
private def jDmsgLLLemma : Json :=
  Json.mkObj
    [("kind", Json.str "Th_axiom"), ("name", Json.str "dmsg_ll"),
     ("path", Json.str "Top.StatelessROM.UUFKOAROM.UUFKOA.dmsg_ll"),
     ("decl", Json.mkObj
       [("tparams", Json.arr #[]), ("axiom_kind", Json.str "Lemma"),
        ("spec", jDmsgLosslessSpec jMsgDistrTyAlias)])]

/-- The `Th_theory` item of the clone instance. -/
private def jUUFKOA : Json :=
  Json.mkObj
    [("kind", Json.str "Th_theory"), ("name", Json.str "UUFKOA"),
     ("path", Json.str "Top.StatelessROM.UUFKOAROM.UUFKOA"),
     ("mode", Json.str "concrete"), ("source", Json.null),
     ("items", Json.arr #[jDmsgLLLemma])]

/-- The `Th_theory` item declaring the operator, its axiom and the clone. -/
private def jUUFKOAROM : Json :=
  Json.mkObj
    [("kind", Json.str "Th_theory"), ("name", Json.str "UUFKOAROM"),
     ("path", Json.str "Top.StatelessROM.UUFKOAROM"),
     ("mode", Json.str "abstract"), ("source", Json.null),
     ("items", Json.arr #[jDmsg, jDmsgLLAxiom, jUUFKOA])]

/-- The envelope items the statement's scope is walked in. -/
private def dsromItems : List Json :=
  [jMsgT,
   Json.mkObj
     [("kind", Json.str "Th_theory"), ("name", Json.str "StatelessROM"),
      ("path", Json.str "Top.StatelessROM"),
      ("mode", Json.str "concrete"), ("source", Json.null),
      ("items", Json.arr #[jUUFKOAROM])]]

/-- The tables the theory's statements decode against, carrying the envelope's
items as the scope a lemma's premises are read from. -/
private def dsromTables : FormTables :=
  formTables
    (registerThOperators (registerThTypes ecPrelude dsromItems) dsromItems) []
    (scopeItems := dsromItems)

/-- The path of the realized lemma. -/
private def dmsgLemmaPath : String := "Top.StatelessROM.UUFKOAROM.UUFKOA.dmsg_ll"

/-- The signature `dmsg`'s declaration gives it. -/
private def dmsgSig : EcSig := ⟨.unit, .distr (.opaque "Top.msg_t")⟩

-- The scope walk reaches one scope out and finds the axiom the lemma is proved
-- from.
#guard (scopeAxiomItems dsromItems dmsgLemmaPath).map itemPath
  == ["Top.StatelessROM.UUFKOAROM.dmsg_ll"]

-- The lemma's own theory declares no axiom, so reading it alone finds none.
#guard (scopeAxiomItems [jUUFKOA] dmsgLemmaPath).isEmpty

-- An axiom of an unrelated scope is not a premise.
#guard (scopeAxiomItems dsromItems "Top.Other.T.thm").isEmpty

-- The assembled statement is the goal under that axiom, both reads discharged by
-- one binder.
#guard (match decodeLemmaAt dsromTables dmsgLemmaPath with
        | .ok (.allConst "Top.StatelessROM.UUFKOAROM.dmsg" t
                 (.imp (.isLossless h) (.isLossless g))) =>
            t == EcTy.distr (EcTy.opaque "Top.msg_t")
              && h.opAppOf == some ("Top.StatelessROM.UUFKOAROM.dmsg", dmsgSig)
              && g.opAppOf == some ("Top.StatelessROM.UUFKOAROM.dmsg", dmsgSig)
        | _ => false)

#guard (match decodeLemmaAt dsromTables dmsgLemmaPath with
        | .ok f => EcForm.opsOf f == []
        | _ => false)

-- An imported axiom is not a goal of its theory.
#guard (match decodeLemmaAt dsromTables "Top.StatelessROM.UUFKOAROM.dmsg_ll" with
        | .error m => m.startsWith "ec-import: the statement"
        | _ => false)

-- A path no item declares is an error naming the path.
#guard (match decodeLemmaAt dsromTables "Top.StatelessROM.UUFKOAROM.absent" with
        | .error m => m.startsWith "ec-import: the export declares no Th_axiom"
        | _ => false)

/-- An imported axiom of the same scope whose statement reads an operator path in
no table. -/
private def jUndecodableAxiom : Json :=
  Json.mkObj
    [("kind", Json.str "Th_axiom"), ("name", Json.str "dmsg_side"),
     ("path", Json.str "Top.StatelessROM.UUFKOAROM.dmsg_side"),
     ("decl", Json.mkObj
       [("tparams", Json.arr #[]), ("axiom_kind", Json.str "Axiom"),
        ("spec", Json.mkObj
          [("ty", jFormBool), ("kind", Json.str "Fop"),
           ("path", Json.str "Top.StatelessROM.UUFKOAROM.side"),
           ("targs", Json.arr #[])])])]

/-- The same scope carrying that axiom. -/
private def dsromItemsUndecodable : List Json :=
  [jMsgT,
   Json.mkObj
     [("kind", Json.str "Th_theory"), ("name", Json.str "StatelessROM"),
      ("path", Json.str "Top.StatelessROM"),
      ("mode", Json.str "concrete"), ("source", Json.null),
      ("items", Json.arr
        #[Json.mkObj
            [("kind", Json.str "Th_theory"), ("name", Json.str "UUFKOAROM"),
             ("path", Json.str "Top.StatelessROM.UUFKOAROM"),
             ("mode", Json.str "abstract"), ("source", Json.null),
             ("items", Json.arr #[jDmsg, jDmsgLLAxiom, jUndecodableAxiom, jUUFKOA])]])]]

-- An axiom of the scope that does not decode rejects the lemma and names the
-- axiom, rather than assembling a goal that is missing a premise.
#guard (match decodeLemmaAt { dsromTables with
            scopeItems := dsromItemsUndecodable } dmsgLemmaPath with
        | .error m =>
            m.startsWith "ec-import: the statement"
              && (m.splitOn "Top.StatelessROM.UUFKOAROM.dmsg_side").length != 1
        | _ => false)

-- `is_lossless` applied to a term that is not a distribution is rejected.
#guard (match decodeForm prfFormTables
            (Json.mkObj
              [("ty", jFormBool), ("kind", Json.str "Fapp"),
               ("f", Json.mkObj
                 [("ty", jFormBool), ("kind", Json.str "Fop"),
                  ("path", Json.str "Top.Distr.is_lossless"),
                  ("targs", Json.arr #[])]),
               ("args", Json.arr
                 #[Json.mkObj [("ty", jFormBool), ("kind", Json.str "Fop"),
                               ("path", Json.str "Top.Pervasive.true"),
                               ("targs", Json.arr #[])]])]) with
        | .error _ => true
        | _ => false)

/-! ### A polymorphic statement

`Top.pairS` of EasyCrypt's `theories/core/Core.ec` is

```
lemma pairS ['a 'b] : forall (x : 'a * 'b), x = (x.`1, x.`2).
```

The nodes below are the exporter's payload for that item: two type parameters, a
`Ttuple` of two `Tvar` nodes in the binder's type, and the same `Tvar` nodes in
the type of every subterm and in the `targs` of the applied equality. -/

/-- A type-variable node, at the name and uniqueness stamp the export writes. -/
private def jTvar (nm : String) (st : Nat) : Json :=
  Json.mkObj [("kind", Json.str "Tvar"), ("name", Json.str nm), ("stamp", Json.num st)]

/-- The type `'a * 'b`. -/
private def jPairTvarTy : Json :=
  Json.mkObj [("kind", Json.str "Ttuple"),
    ("args", Json.arr #[jTvar "'a" 5162, jTvar "'b" 5163])]

/-- The type `bool`, as the statement's nodes carry it. -/
private def jPairSBoolTy : Json :=
  Json.mkObj [("kind", Json.str "Tconstr"),
    ("path", Json.str "Top.Pervasive.bool"), ("args", Json.arr #[])]

/-- The bound variable `x : 'a * 'b`. -/
private def jPairSLocal : Json :=
  Json.mkObj [("ty", jPairTvarTy), ("kind", Json.str "Flocal"),
    ("name", Json.str "x"), ("stamp", Json.num 5164)]

/-- A projection of the bound variable, at the component type `t`. -/
private def jPairSProj (t : Json) (i : Nat) : Json :=
  Json.mkObj [("ty", t), ("kind", Json.str "Fproj"), ("target", jPairSLocal),
    ("index", Json.num i)]

/-- Equality at `'a * 'b`. -/
private def jPairSEqOp : Json :=
  Json.mkObj
    [("ty", Json.mkObj [("kind", Json.str "Tfun"), ("dom", jPairTvarTy),
        ("cod", Json.mkObj [("kind", Json.str "Tfun"), ("dom", jPairTvarTy),
          ("cod", jPairSBoolTy)])]),
     ("kind", Json.str "Fop"), ("path", Json.str "Top.Pervasive.="),
     ("targs", Json.arr #[jPairTvarTy])]

/-- The body: the bound variable equated with the pair of its two
projections. -/
private def jPairSBody : Json :=
  Json.mkObj [("ty", jPairSBoolTy), ("kind", Json.str "Fapp"), ("f", jPairSEqOp),
    ("args", Json.arr #[jPairSLocal,
      Json.mkObj [("ty", jPairTvarTy), ("kind", Json.str "Ftuple"),
        ("args", Json.arr #[jPairSProj (jTvar "'a" 5162) 0,
                            jPairSProj (jTvar "'b" 5163) 1])]])]

/-- The `Th_axiom` item `Top.pairS`. -/
def jPairSItem : Json :=
  Json.mkObj [("kind", Json.str "Th_axiom"), ("name", Json.str "pairS"),
    ("path", Json.str "Top.pairS"),
    ("decl", Json.mkObj
      [("tparams", Json.arr #[Json.str "'a", Json.str "'b"]),
       ("axiom_kind", Json.str "Lemma"),
       ("spec", Json.mkObj [("ty", jPairSBoolTy), ("kind", Json.str "Fquant"),
         ("quant", Json.str "Lforall"),
         ("binders", Json.arr #[Json.mkObj
           [("name", Json.str "x"), ("stamp", Json.num 5164),
            ("gty", Json.mkObj [("kind", Json.str "GTty"), ("ty", jPairTvarTy)])]]),
         ("body", jPairSBody)])])]

-- The item declares two type parameters, in the order the source writes them.
#guard (match axiomTyParams jPairSItem with
        | .ok ("pairS", ["'a", "'b"]) => true
        | _ => false)

-- Each parameter carries one stamp everywhere it occurs, so the name is enough
-- to tell the two apart.
#guard (tyVarIdents tyParamDepth jPairSItem).eraseDups
  == [("'a", 5162), ("'b", 5163)]

#guard (tyVarIdents tyParamDepth jPairSItem).length == 18

-- The rewriting leaves no type variable behind.
#guard tyVarIdents tyParamDepth
    (substTyParams ["'a", "'b"] tyParamDepth jPairSItem) == []

-- With no assignment, each parameter is read at the opaque code of its reserved
-- path, and every type position of the statement takes it: the binder's type,
-- the equated terms, and the two projections.
#guard (match decodeAxiom bareTables jPairSItem with
        | .ok (.allTy (.prod (.opaque "#tyvar.'a") (.opaque "#tyvar.'b")) "x"
                 (.eqT (.var _ "x")
                   (.pair (.fst (.var _ "x")) (.snd (.var _ "x"))))) => true
        | _ => false)

#guard (match decodeAxiom bareTables jPairSItem with
        | .ok f => EcForm.opsOf f == []
        | _ => false)

-- At an assignment the same statement decodes at the assigned codes.
#guard (match decodeAxiomAt bareTables [.bool, .int] jPairSItem with
        | .ok (.allTy (.prod .bool .int) "x"
                 (.eqT (.var _ "x")
                   (.pair (.fst (.var _ "x")) (.snd (.var _ "x"))))) => true
        | _ => false)

#guard (match decodeAxiomAt bareTables [.list .int, .fset .bool] jPairSItem with
        | .ok (.allTy (.prod (.list .int) (.fset .bool)) "x" (.eqT _ _)) => true
        | _ => false)

-- An assignment of the wrong length is refused rather than padded.
#guard (match decodeAxiomAt bareTables [.bool] jPairSItem with
        | .error _ => true
        | _ => false)

/-! ### A statement reading a defined operator

`Top.^^` of EasyCrypt's `theories/core/Bool.ec` is `op (^^) b1 b2 = b1 = !b2.`,
and `Top.xorC` is `lemma xorC : forall b1 b2, b1 ^^ b2 = b2 ^^ b1.`. The nodes
below are the exporter's payload for the two items. The lemma binds `b1` and `b2`
at its own stamps and the definition binds parameters of the same two source
names at its own, which is the case the expansion's renaming is for: bound under
their source names alone, the definition's parameters would be refused by
`FormTables.bindLocal`. -/

/-- The type `bool`, as the two items carry it. -/
private def jXorBoolTy : Json :=
  Json.mkObj [("kind", Json.str "Tconstr"),
    ("path", Json.str "Top.Pervasive.bool"), ("args", Json.arr #[])]

/-- The type `bool -> bool`. -/
private def jXorFun1 : Json :=
  Json.mkObj [("kind", Json.str "Tfun"), ("dom", jXorBoolTy), ("cod", jXorBoolTy)]

/-- The type `bool -> bool -> bool`. -/
private def jXorFun2 : Json :=
  Json.mkObj [("kind", Json.str "Tfun"), ("dom", jXorBoolTy), ("cod", jXorFun1)]

/-- A `bool`-typed read of a stamped identifier. -/
private def jXorLocal (nm : String) (st : Nat) : Json :=
  Json.mkObj [("ty", jXorBoolTy), ("kind", Json.str "Flocal"),
    ("name", Json.str nm), ("stamp", Json.num st)]

/-- A `bool`-typed binder. -/
private def jXorBinder (nm : String) (st : Nat) : Json :=
  Json.mkObj [("name", Json.str nm), ("stamp", Json.num st),
    ("gty", Json.mkObj [("kind", Json.str "GTty"), ("ty", jXorBoolTy)])]

/-- Equality at `bool`. -/
private def jXorEqOp : Json :=
  Json.mkObj [("ty", jXorFun2), ("kind", Json.str "Fop"),
    ("path", Json.str "Top.Pervasive.="), ("targs", Json.arr #[jXorBoolTy])]

/-- Boolean negation. -/
private def jXorNotOp : Json :=
  Json.mkObj [("ty", jXorFun1), ("kind", Json.str "Fop"),
    ("path", Json.str "Top.Pervasive.[!]"), ("targs", Json.arr #[])]

/-- A read of the defined operator. -/
private def jXorOpNode : Json :=
  Json.mkObj [("ty", jXorFun2), ("kind", Json.str "Fop"),
    ("path", Json.str "Top.^^"), ("targs", Json.arr #[])]

/-- A `bool`-typed application. -/
private def jXorApp (f : Json) (args : Array Json) : Json :=
  Json.mkObj [("ty", jXorBoolTy), ("kind", Json.str "Fapp"), ("f", f),
    ("args", Json.arr args)]

/-- The `Th_operator` item `Top.^^`. -/
def jXorOp : Json :=
  Json.mkObj [("kind", Json.str "Th_operator"), ("name", Json.str "^^"),
    ("path", Json.str "Top.^^"),
    ("decl", Json.mkObj
      [("tparams", Json.arr #[]), ("ty", jXorFun2),
       ("body", Json.mkObj
         [("kind", Json.str "OP_Plain"),
          ("form", Json.mkObj
            [("ty", jXorFun2), ("kind", Json.str "Fquant"),
             ("quant", Json.str "Llambda"),
             ("binders", Json.arr #[jXorBinder "b1" 32499, jXorBinder "b2" 32500]),
             ("body", jXorApp jXorEqOp
               #[jXorLocal "b1" 32499,
                 jXorApp jXorNotOp #[jXorLocal "b2" 32500]])])])])]

/-- The `Th_axiom` item `Top.xorC`. -/
def jXorCItem : Json :=
  Json.mkObj [("kind", Json.str "Th_axiom"), ("name", Json.str "xorC"),
    ("path", Json.str "Top.xorC"),
    ("decl", Json.mkObj
      [("tparams", Json.arr #[]), ("axiom_kind", Json.str "Lemma"),
       ("spec", Json.mkObj
         [("ty", jXorBoolTy), ("kind", Json.str "Fquant"),
          ("quant", Json.str "Lforall"),
          ("binders", Json.arr #[jXorBinder "b1" 32541, jXorBinder "b2" 32543]),
          ("body", jXorApp jXorEqOp
            #[jXorApp jXorOpNode #[jXorLocal "b1" 32541, jXorLocal "b2" 32543],
              jXorApp jXorOpNode #[jXorLocal "b2" 32543, jXorLocal "b1" 32541]])])])]

/-- The tables the lemma decodes against: the prelude with the definition
registered through the walk that registers a theory's operators. -/
private def xorTables : FormTables :=
  formTables (registerThOperators ecPrelude [jXorOp]) []

-- The declaration registers as a definition and not as a parameter.
#guard xorTables.tables.defOpPaths.map Prod.fst == ["Top.^^"]

#guard xorTables.tables.absOpPaths == []

-- Each read expands to the definition's body under one binder per parameter, in
-- source order and the first parameter outermost. The binders carry the
-- parameters' stamps beside their source names, so the lemma's own `b1` and `b2`
-- are untouched.
#guard (match decodeAxiom xorTables jXorCItem with
        | .ok (.allTy .bool "b1" (.allTy .bool "b2"
                 (.eqT (.letIn "b1_32499" _ (.letIn "b2_32500" _ (.beq _ (.bnot _))))
                       (.letIn "b1_32499" _ (.letIn "b2_32500" _ (.beq _ (.bnot _))))))) =>
            true
        | _ => false)

-- The expanded statement reads no abstract operator.
#guard (match decodeAxiom xorTables jXorCItem with
        | .ok f => EcForm.opsOf f == []
        | _ => false)

-- Without the definition registered, the read has no image and the statement is
-- refused naming the path.
#guard (match decodeAxiom bareTables jXorCItem with
        | .error _ => true
        | _ => false)

-- The definition is dropped for the decode of its own body, so the table a read
-- decodes against is shorter than the one it started from.
#guard (xorTables.withoutDefOp "Top.^^").tables.defOpPaths.isEmpty

/-! ### A statement that reads a definition branching on the strict order

`Top.max` of EasyCrypt's `theories/datatypes/Int.ec` is
`op max (a b : int) = if a < b then b else a.`, and `Top.lez_maxr` is
`lemma lez_maxr : forall a b, a <= b => max a b = b.`. The lemma's antecedent is
the order comparison and the definition's body branches on the strict one, so the
statement carries both spellings: the comparison at its own node and the negation
of the reversed comparison inside the inlined body. -/

/-- The type `int`, as the two items carry it. -/
private def jMaxIntTy : Json :=
  Json.mkObj [("kind", Json.str "Tconstr"),
    ("path", Json.str "Top.Pervasive.int"), ("args", Json.arr #[])]

/-- A binary arrow type. -/
private def jMaxFun2 (d₁ d₂ c : Json) : Json :=
  Json.mkObj [("kind", Json.str "Tfun"), ("dom", d₁),
    ("cod", Json.mkObj [("kind", Json.str "Tfun"), ("dom", d₂), ("cod", c)])]

/-- A read of a stamped identifier at the type `t`. -/
private def jMaxLocal (t : Json) (nm : String) (st : Nat) : Json :=
  Json.mkObj [("ty", t), ("kind", Json.str "Flocal"), ("name", Json.str nm),
    ("stamp", Json.num st)]

/-- A binder at the type `t`. -/
private def jMaxBinder (nm : String) (st : Nat) (t : Json) : Json :=
  Json.mkObj [("name", Json.str nm), ("stamp", Json.num st),
    ("gty", Json.mkObj [("kind", Json.str "GTty"), ("ty", t)])]

/-- An operator node at the type `t`. -/
private def jMaxOpNode (t : Json) (p : String) (targs : Array Json) : Json :=
  Json.mkObj [("ty", t), ("kind", Json.str "Fop"), ("path", Json.str p),
    ("targs", Json.arr targs)]

/-- An application at the type `t`. -/
private def jMaxApp (t f : Json) (args : Array Json) : Json :=
  Json.mkObj [("ty", t), ("kind", Json.str "Fapp"), ("f", f), ("args", Json.arr args)]

private def jMaxA : Json := jMaxLocal jMaxIntTy "a" 6828
private def jMaxB : Json := jMaxLocal jMaxIntTy "b" 6829

/-- The `Th_operator` item `Top.max`. -/
def jMaxOp : Json :=
  Json.mkObj [("kind", Json.str "Th_operator"), ("name", Json.str "max"),
    ("path", Json.str "Top.max"),
    ("decl", Json.mkObj
      [("tparams", Json.arr #[]),
       ("ty", jMaxFun2 jMaxIntTy jMaxIntTy jMaxIntTy),
       ("body", Json.mkObj
         [("kind", Json.str "OP_Plain"),
          ("form", Json.mkObj
            [("ty", jMaxFun2 jMaxIntTy jMaxIntTy jMaxIntTy),
             ("kind", Json.str "Fquant"), ("quant", Json.str "Llambda"),
             ("binders", Json.arr #[jMaxBinder "a" 6828 jMaxIntTy,
                                    jMaxBinder "b" 6829 jMaxIntTy]),
             ("body", Json.mkObj
               [("ty", jMaxIntTy), ("kind", Json.str "Fif"),
                ("cond", jMaxApp jXorBoolTy
                  (jMaxOpNode (jMaxFun2 jMaxIntTy jMaxIntTy jXorBoolTy)
                    "Top.CoreInt.lt" #[]) #[jMaxA, jMaxB]),
                ("then", jMaxB), ("else", jMaxA)])])])])]

private def jLezA : Json := jMaxLocal jMaxIntTy "a" 6878
private def jLezB : Json := jMaxLocal jMaxIntTy "b" 6880

/-- The `Th_axiom` item `Top.lez_maxr`. -/
def jLezMaxrItem : Json :=
  Json.mkObj [("kind", Json.str "Th_axiom"), ("name", Json.str "lez_maxr"),
    ("path", Json.str "Top.lez_maxr"),
    ("decl", Json.mkObj
      [("tparams", Json.arr #[]), ("axiom_kind", Json.str "Lemma"),
       ("spec", Json.mkObj
         [("ty", jXorBoolTy), ("kind", Json.str "Fquant"),
          ("quant", Json.str "Lforall"),
          ("binders", Json.arr #[jMaxBinder "a" 6878 jMaxIntTy,
                                 jMaxBinder "b" 6880 jMaxIntTy]),
          ("body", jMaxApp jXorBoolTy
            (jMaxOpNode (jMaxFun2 jXorBoolTy jXorBoolTy jXorBoolTy)
              "Top.Pervasive.=>" #[])
            #[jMaxApp jXorBoolTy
                (jMaxOpNode (jMaxFun2 jMaxIntTy jMaxIntTy jXorBoolTy)
                  "Top.CoreInt.le" #[]) #[jLezA, jLezB],
              jMaxApp jXorBoolTy
                (jMaxOpNode (jMaxFun2 jMaxIntTy jMaxIntTy jXorBoolTy)
                  "Top.Pervasive.=" #[jMaxIntTy])
                #[jMaxApp jMaxIntTy
                    (jMaxOpNode (jMaxFun2 jMaxIntTy jMaxIntTy jMaxIntTy)
                      "Top.max" #[]) #[jLezA, jLezB],
                  jLezB]])])])]

/-- The tables the lemma decodes against. -/
private def maxTables : FormTables :=
  formTables (registerThOperators ecPrelude [jMaxOp]) []

#guard maxTables.tables.defOpPaths.map Prod.fst == ["Top.max"]

-- The lemma decodes under one binder per bound variable: the antecedent is the
-- order comparison, and the left side of the consequent is the definition's body
-- under one `let` per parameter, branching on the negation of the reversed
-- comparison.
#guard (match decodeAxiom maxTables jLezMaxrItem with
        | .ok (.allTy .int "a" (.allTy .int "b"
                 (.imp (.holds (.intLe _ _))
                       (.eqT (.letIn _ _ (.letIn _ _ (.ite (.bnot (.intLe _ _)) _ _)))
                             _)))) => true
        | _ => false)

-- The expanded statement reads no abstract operator.
#guard (match decodeAxiom maxTables jLezMaxrItem with
        | .ok f => EcForm.opsOf f == []
        | _ => false)

-- A definition read with no argument is one lambda per parameter over the body,
-- with each parameter bound to the lambda's own variable.
#guard (match decodeTerm maxTables (.arrow .int (.arrow .int .int))
            (jMaxOpNode (jMaxFun2 jMaxIntTy jMaxIntTy jMaxIntTy) "Top.max" #[]) with
        | .ok (.lam .int _ (.lam .int _
                 (.letIn _ _ (.letIn _ _ (.ite (.bnot (.intLe _ _)) _ _))))) => true
        | _ => false)

-- The lambda binders carry a `#`, which no source identifier holds.
#guard (match decodeTerm maxTables (.arrow .int (.arrow .int .int))
            (jMaxOpNode (jMaxFun2 jMaxIntTy jMaxIntTy jMaxIntTy) "Top.max" #[]) with
        | .ok (.lam _ n₁ (.lam _ n₂ _)) => n₁ == "Top.max#1" && n₂ == "Top.max#2"
        | _ => false)

-- A read at a code with fewer arrows than the definition has parameters is
-- rejected, rather than read at the body.
#guard (match decodeTerm maxTables .int (jMaxOpNode jMaxIntTy "Top.max" #[]) with
        | .error m =>
          m.startsWith "ec-import: the operator 'Top.max' is defined with 2"
        | _ => false)

-- A read at an arrow code whose domain is not the parameter's declared code is
-- rejected.
#guard (match decodeTerm maxTables (.arrow .bool (.arrow .int .int))
            (jMaxOpNode (jMaxFun2 jXorBoolTy jMaxIntTy jMaxIntTy) "Top.max" #[]) with
        | .error m =>
          m.startsWith "ec-import: the operator 'Top.max' is defined at parameter"
        | _ => false)

/-- `Top.^^`'s tables with boolean negation removed, at which its definition's
body has no image. -/
private def xorTablesNoNot : FormTables :=
  { xorTables with
    tables := { xorTables.tables with
      opPaths := xorTables.tables.opPaths.filter
        (fun e => e.1 != "Top.Pervasive.[!]") } }

-- A failure inside a definition's body is reported as a failure of the operator,
-- naming it, since the node it fails at is one the statement does not contain.
#guard (match decodeAxiom xorTablesNoNot jXorCItem with
        | .error m =>
          (m.splitOn "Top.^^").length > 1
            && (m.splitOn "is defined by a term that does not decode").length > 1
        | _ => false)

/-! ### Module binders at a module type declared inside a theory

`formosa_modbinders.json` holds two nodes of the exporter's output for
`formosa-crypto/formosa-mlkem`, each copied whole: the module type that
`Top.Gm0_Gm1`'s module binder is declared at, and a binder at a module type six
theories deep. Neither module type is a top-level item of the envelope it comes
from, so neither is in the module-type table `surveyExtendTables` builds, and the
first binds two module parameters, which `decodeModTypeInterface` rejects. Both
`ModuleType` nodes carry the signature the binder is read against. -/

/-- The two module-binder nodes, as text. -/
private def formosaModText : String := include_str "formosa_modbinders.json"

/-- The two module-binder nodes. -/
private def formosaModNodes : Json :=
  match Json.parse formosaModText with
  | .ok j => j
  | .error _ => Json.null

/-- The node the two are read from by key. -/
private def formosaModNode (k : String) : Json :=
  (formosaModNodes.getObjVal? k).toOption.getD Json.null

/-- The tables the two nodes decode against: the prelude, and the abstract types
their procedure signatures name. -/
private def formosaModTables : DecodeTables :=
  ["Top.TT.plaintext", "Top.TT.randomness", "Top.key",
   "Top.TT.PKE.pkey", "Top.TT.PKE.ciphertext"].foldl
    DecodeTables.withOpaqueType ecPrelude

-- `Top.KEMROMx2.CCA_ADV` binds two module parameters, so the route a module-type
-- declaration is registered through has no interface for it.
#guard (match getObj (formosaModNode "cca_adv") "sig" with
        | .ok sigJ =>
          (match decodeModSig formosaModTables sigJ with
           | .error _ => true
           | .ok _ => false)
        | .error _ => false)

-- Its node's own signature declares `guess`, at the argument tuple and result
-- type the source gives it.
#guard (match decodeModTypeSig formosaModTables (formosaModNode "cca_adv") with
        | .ok I =>
          I.names == ["guess"]
            && (match I.sig "guess" with
                | ⟨.prod (.opaque "Top.TT.PKE.pkey")
                    (.prod (.opaque "Top.TT.PKE.ciphertext") (.opaque "Top.key")),
                   .bool⟩ => true
                | _ => false)
        | .error _ => false)

-- A binder at `Top.MLWE_PKE_Hash.FO_MLKEM.UU.TT.PKE.LorR.A` quantifies over a
-- module at the interface that module type declares, against tables that carry
-- no module type at all.
#guard (match bindBinder (formTables ecPrelude []) "Lforall"
                (formosaModNode "lorr_binder") with
        | .ok (F, w) =>
          F.modBinders.map Prod.fst == ["L"]
            && (match w (.holds (.lit true)) with
                | .allMod "L" I (.holds (.lit true)) => I.names == ["main"]
                | _ => false)
        | .error _ => false)

/-! ### Integer comparison as the exported corpus carries it

Three statements of EasyCrypt's `theories/datatypes/Int.ec`, transcribed from
their nodes in an envelope of schema version 10:

```
lemma lez01 : 0 <= 1.
lemma lezz  : forall (x : int), x <= x.
lemma ltzW  : forall (z1 z2 : int), z1 < z2 => z1 <= z2.
```

`ltzW` carries both spellings of the order side by side, which is what pins the
strict one to the negation of the reversed comparison. -/

/-- The head of an integer relation, at the arrow type the envelope carries. -/
private def jIntRelOp (p : String) : Json :=
  jMaxOpNode (jMaxFun2 jMaxIntTy jMaxIntTy jFormBool) p #[]

/-- The head of the boolean implication, at the arrow type the envelope
carries. -/
private def jBoolImpOp : Json :=
  jMaxOpNode (jMaxFun2 jFormBool jFormBool jFormBool) "Top.Pervasive.=>" #[]

/-- The body of `Top.lez01`. -/
private def jLez01Body : Json :=
  jMaxApp jFormBool (jIntRelOp "Top.CoreInt.le")
    #[jFormIntLit "0", jFormIntLit "1"]

-- A comparison in formula position is the comparison term, asserted to hold.
#guard (match decodeForm bareTables jLez01Body with
        | .ok (.holds (.intLe a b)) => isIntLit a 0 && isIntLit b 1
        | _ => false)

/-- The `Th_axiom` item `Top.lezz`. -/
private def jLezzItem : Json :=
  Json.mkObj [("kind", Json.str "Th_axiom"), ("name", Json.str "lezz"),
    ("path", Json.str "Top.lezz"),
    ("decl", Json.mkObj
      [("tparams", Json.arr #[]), ("axiom_kind", Json.str "Lemma"),
       ("spec", Json.mkObj
         [("ty", jFormBool), ("kind", Json.str "Fquant"),
          ("quant", Json.str "Lforall"),
          ("binders", Json.arr #[jMaxBinder "x" 5372 jMaxIntTy]),
          ("body", jMaxApp jFormBool (jIntRelOp "Top.CoreInt.le")
            #[jMaxLocal jMaxIntTy "x" 5372,
              jMaxLocal jMaxIntTy "x" 5372])])])]

-- Both operands resolve to the one binder the statement quantifies over.
#guard (match decodeAxiom bareTables jLezzItem with
        | .ok (.allTy .int "x" (.holds (.intLe (.var .int nx) (.var .int ny)))) =>
          nx == ny
        | _ => false)

/-- The `Th_axiom` item `Top.ltzW`. -/
private def jLtzWItem : Json :=
  Json.mkObj [("kind", Json.str "Th_axiom"), ("name", Json.str "ltzW"),
    ("path", Json.str "Top.ltzW"),
    ("decl", Json.mkObj
      [("tparams", Json.arr #[]), ("axiom_kind", Json.str "Lemma"),
       ("spec", Json.mkObj
         [("ty", jFormBool), ("kind", Json.str "Fquant"),
          ("quant", Json.str "Lforall"),
          ("binders", Json.arr #[jMaxBinder "z1" 5903 jMaxIntTy,
                                 jMaxBinder "z2" 5904 jMaxIntTy]),
          ("body", jMaxApp jFormBool jBoolImpOp
            #[jMaxApp jFormBool (jIntRelOp "Top.CoreInt.lt")
                #[jMaxLocal jMaxIntTy "z1" 5903,
                  jMaxLocal jMaxIntTy "z2" 5904],
              jMaxApp jFormBool (jIntRelOp "Top.CoreInt.le")
                #[jMaxLocal jMaxIntTy "z1" 5903,
                  jMaxLocal jMaxIntTy "z2" 5904]])])])]

-- The antecedent is the negation of the reversed comparison, so its operands
-- stand in the opposite order to the consequent's.
#guard (match decodeAxiom bareTables jLtzWItem with
        | .ok (.allTy .int "z1" (.allTy .int "z2"
                 (.imp (.holds (.bnot (.intLe (.var .int a₁) (.var .int a₂))))
                       (.holds (.intLe (.var .int b₁) (.var .int b₂)))))) =>
          a₁ != a₂ && a₁ == b₂ && a₂ == b₁
        | _ => false)

/-! ### List observation in a statement

`size` reaches the term layer at the shape the expression layer already reads it
at: the list's own type node gives the element code. -/


/-- A statement over one binder named `l` at the type node `bty`, with `body` its
assertion. -/
private def jListItem (nm : String) (bty body : Json) : Json :=
  Json.mkObj [("kind", Json.str "Th_axiom"), ("name", Json.str nm),
    ("path", Json.str s!"Top.{nm}"),
    ("decl", Json.mkObj
      [("tparams", Json.arr #[]), ("axiom_kind", Json.str "Lemma"),
       ("spec", Json.mkObj
         [("ty", jFormBool), ("kind", Json.str "Fquant"),
          ("quant", Json.str "Lforall"),
          ("binders", Json.arr #[jMaxBinder "l" 4211 bty]),
          ("body", body)])])]

-- `0 <= size l` reads the element code off the list's own type node.
#guard (match decodeAxiom bareTables
            (jListItem "sizeGe0" jFormIntList
              (jMaxApp jFormBool (jIntRelOp "Top.CoreInt.le")
                #[jFormIntLit "0",
                  jMaxApp jFormInt
                    (jMaxOpNode (Json.mkObj [("kind", Json.str "Tfun"),
                        ("dom", jFormIntList), ("cod", jMaxIntTy)])
                      "Top.List.size" #[])
                    #[jMaxLocal jFormIntList "l" 4211]])) with
        | .ok (.allTy (.list .int) "l" (.holds (.intLe a (.listSize (.var _ _))))) =>
          isIntLit a 0
        | _ => false)

/-! ### A definition over type parameters read by a statement

`prelude/Logic.ec` declares

```
op associative ['a] (o : 'a -> 'a -> 'a) =
  forall x y z, o x (o y z) = o (o x y) z.
```

and a client writes `associative f` for a concrete `f`. The nodes below are that
shape: a `Th_operator` item whose `tparams` names the type parameter and whose
`PR_Plain` body is a lambda over the value parameter, and an `Fapp` reading it at
one type argument and one value argument. -/

/-- The type parameter of the declaration. -/
private def jAssocTvar : Json := jTvar "'a" 2572

/-- The type of the declaration's value parameter, `'a -> 'a -> 'a`. -/
private def jAssocParamTy : Json := jMaxFun2 jAssocTvar jAssocTvar jAssocTvar

/-- A read of the value parameter. -/
private def jAssocO : Json := jMaxLocal jAssocParamTy "o" 2573

/-- The parameter applied to two arguments. -/
private def jAssocApp (a b : Json) : Json := jMaxApp jAssocTvar jAssocO #[a, b]

private def jAssocX : Json := jMaxLocal jAssocTvar "x" 2575
private def jAssocY : Json := jMaxLocal jAssocTvar "y" 2577
private def jAssocZ : Json := jMaxLocal jAssocTvar "z" 2579

/-- The quantified body the declaration's lambda binds. -/
private def jAssocBody : Json :=
  Json.mkObj
    [("ty", jFormBool), ("kind", Json.str "Fquant"),
     ("quant", Json.str "Lforall"),
     ("binders", Json.arr #[jMaxBinder "x" 2575 jAssocTvar,
                            jMaxBinder "y" 2577 jAssocTvar,
                            jMaxBinder "z" 2579 jAssocTvar]),
     ("body", jMaxApp jFormBool
       (jMaxOpNode (jMaxFun2 jAssocTvar jAssocTvar jFormBool)
         "Top.Pervasive.=" #[jAssocTvar])
       #[jAssocApp jAssocX (jAssocApp jAssocY jAssocZ),
         jAssocApp (jAssocApp jAssocX jAssocY) jAssocZ])]

/-- The `Th_operator` item `Top.Logic.assoc`. -/
def jAssocOp : Json :=
  Json.mkObj [("kind", Json.str "Th_operator"), ("name", Json.str "assoc"),
    ("path", Json.str "Top.Logic.assoc"),
    ("decl", Json.mkObj
      [("tparams", Json.arr #[Json.str "'a"]),
       ("ty", jTyArrow jAssocParamTy jFormBool),
       ("body", Json.mkObj
         [("kind", Json.str "PR_Plain"),
          ("form", Json.mkObj
            [("ty", jTyArrow jAssocParamTy jFormBool),
             ("kind", Json.str "Fquant"), ("quant", Json.str "Llambda"),
             ("binders", Json.arr #[jMaxBinder "o" 2573 jAssocParamTy]),
             ("body", jAssocBody)])])])]

/-- The carrier the read site gives the type parameter. -/
private def jAssocDTy : Json := jTyNode "Top.D"

/-- The type of the operator the read site gives the value parameter. -/
private def jAssocFTy : Json := jMaxFun2 jAssocDTy jAssocDTy jAssocDTy

/-- The signature `f`'s declaration gives it: two arguments at the carrier `D` as
the right-nested product, and `D` as the result. -/
private def assocFSig : EcSig :=
  ⟨.prod (.opaque "Top.D") (.opaque "Top.D"), .opaque "Top.D"⟩

/-- `assoc<:D> f`, the read of the declaration. -/
private def jAssocRead : Json :=
  jMaxApp jFormBool
    (jMaxOpNode (jTyArrow jAssocFTy jFormBool) "Top.Logic.assoc" #[jAssocDTy])
    #[jMaxOpNode jAssocFTy "Top.f" #[]]

/-- The tables the read decodes against: the carrier at the opaque code, `f` at
the signature its declared type gives it, and the declaration over the type
parameter. -/
private def assocTables : FormTables :=
  formTables
    ((registerThOperators (registerThTypes ecPrelude [jAbsTypeDecl "D" "Top.D"])
        [jAssocOp]).withAbstractOp "Top.f" assocFSig) []

-- The declaration registers as written, in the table of definitions over type
-- parameters and in no other.
#guard assocTables.tables.polyOpPaths.map Prod.fst == ["Top.Logic.assoc"]
#guard assocTables.tables.defOpPaths.isEmpty

-- The read decodes to the declaration's body: three quantifiers at the code the
-- type argument gives the type parameter, over an equality.
#guard (match decodeForm assocTables jAssocRead with
        | .ok (.allTy t "x" (.allTy _ "y" (.allTy _ "z" (.eqT _ _)))) =>
          t == EcTy.opaque "Top.D"
        | _ => false)

-- The value parameter is replaced by the operator the read site gives it, so the
-- equated terms are applications of that operator and the statement reads it.
#guard (match decodeForm assocTables jAssocRead with
        | .ok f => EcForm.opsOf f == [("Top.f", assocFSig), ("Top.f", assocFSig),
                                      ("Top.f", assocFSig), ("Top.f", assocFSig)]
        | _ => false)

-- Without the declaration the same read is rejected: the path is in no table.
#guard (match decodeForm
            (formTables ((registerThTypes ecPrelude
              [jAbsTypeDecl "D" "Top.D"]).withAbstractOp "Top.f" assocFSig) [])
            jAssocRead with
        | .error m =>
          m.startsWith "ec-import: unknown operator path 'Top.Logic.assoc'"
        | _ => false)

/-! ### A definition that applies its own parameters, read at lambdas

`prelude/Logic.ec` declares

```
op cancel ['a 'b] (f : 'a -> 'b) (g : 'b -> 'a) = forall x, g (f x) = x.
```

The nodes below are the exporter's payload for it, at the stamps and the
type-parameter order the export writes: a `PR_Plain` body that is a lambda over
the two value parameters, over a quantifier whose body applies both of them.

A read site writes a partial application as a lambda — `right_loop inv o` reads
`cancel` at `fun x => o x y` — so the arguments that reach the parameters here
are lambdas, and each meets an application of the parameter it replaces. The read
below is at `fun u => h u` and `fun v => v`, and the statement after it quantifies
over an `x` of its own, which is the name the declaration's binder carries. -/

/-- The type parameters of the declaration. -/
private def jCanA : Json := jTvar "'a" 1904
private def jCanB : Json := jTvar "'b" 1903

/-- The type of the first value parameter, `'a -> 'b`. -/
private def jCanFTy : Json := jTyArrow jCanA jCanB

/-- The type of the second value parameter, `'b -> 'a`. -/
private def jCanGTy : Json := jTyArrow jCanB jCanA

/-- The type of the declaration, `('a -> 'b) -> ('b -> 'a) -> bool`. -/
private def jCanDeclTy : Json := jTyArrow jCanFTy (jTyArrow jCanGTy jFormBool)

private def jCanF : Json := jMaxLocal jCanFTy "f" 1905
private def jCanG : Json := jMaxLocal jCanGTy "g" 1906
private def jCanX : Json := jMaxLocal jCanA "x" 1908

/-- The quantified body the declaration's lambda binds, `forall x, g (f x) = x`. -/
private def jCanBody : Json :=
  Json.mkObj
    [("ty", jFormBool), ("kind", Json.str "Fquant"),
     ("quant", Json.str "Lforall"),
     ("binders", Json.arr #[jMaxBinder "x" 1908 jCanA]),
     ("body", jMaxApp jFormBool
       (jMaxOpNode (jMaxFun2 jCanA jCanA jFormBool) "Top.Pervasive.=" #[jCanA])
       #[jMaxApp jCanA jCanG #[jMaxApp jCanB jCanF #[jCanX]], jCanX])]

/-- The `Th_operator` item `Top.cancel`. -/
def jCancelOp : Json :=
  Json.mkObj [("kind", Json.str "Th_operator"), ("name", Json.str "cancel"),
    ("path", Json.str "Top.cancel"),
    ("decl", Json.mkObj
      [("tparams", Json.arr #[Json.str "'b", Json.str "'a"]),
       ("ty", jCanDeclTy),
       ("body", Json.mkObj
         [("kind", Json.str "PR_Plain"),
          ("form", Json.mkObj
            [("ty", jCanDeclTy), ("kind", Json.str "Fquant"),
             ("quant", Json.str "Llambda"),
             ("binders", Json.arr #[jMaxBinder "f" 1905 jCanFTy,
                                    jMaxBinder "g" 1906 jCanGTy]),
             ("body", jCanBody)])])])]

/-- The carrier the read site gives both type parameters. -/
private def jCanDTy : Json := jTyNode "Top.D"

/-- The type `D -> D`. -/
private def jCanDFun : Json := jTyArrow jCanDTy jCanDTy

/-- The signature `h`'s declaration gives it. -/
private def canHSig : EcSig := ⟨.opaque "Top.D", .opaque "Top.D"⟩

/-- `fun u => h u`, the first value argument. -/
private def jCanLamH : Json :=
  Json.mkObj
    [("ty", jCanDFun), ("kind", Json.str "Fquant"), ("quant", Json.str "Llambda"),
     ("binders", Json.arr #[jMaxBinder "u" 9101 jCanDTy]),
     ("body", jMaxApp jCanDTy (jMaxOpNode jCanDFun "Top.h" #[])
       #[jMaxLocal jCanDTy "u" 9101])]

/-- `fun v => v`, the second value argument. -/
private def jCanLamId : Json :=
  Json.mkObj
    [("ty", jCanDFun), ("kind", Json.str "Fquant"), ("quant", Json.str "Llambda"),
     ("binders", Json.arr #[jMaxBinder "v" 9102 jCanDTy]),
     ("body", jMaxLocal jCanDTy "v" 9102)]

/-- The head of the read, `cancel<:D, D>`. -/
private def jCanHead : Json :=
  jMaxOpNode (jTyArrow jCanDFun (jTyArrow jCanDFun jFormBool)) "Top.cancel"
    #[jCanDTy, jCanDTy]

/-- `cancel (fun u => h u) (fun v => v)`. -/
private def jCanRead : Json := jMaxApp jFormBool jCanHead #[jCanLamH, jCanLamId]

/-- The tables the read decodes against: the carrier at the opaque code, `h` at
the signature its declared type gives it, and the declaration over the type
parameters. -/
private def cancelTables : FormTables :=
  formTables
    ((registerThOperators (registerThTypes ecPrelude [jAbsTypeDecl "D" "Top.D"])
        [jCancelOp]).withAbstractOp "Top.h" canHSig) []

#guard cancelTables.tables.polyOpPaths.map Prod.fst == ["Top.cancel"]

-- Each argument is contracted at the application of the parameter it replaces:
-- `f x` becomes `h x` and `g (h x)` becomes `h x`, so the read decodes to the
-- declaration's binder over `h x = x`.
#guard (match decodeForm cancelTables jCanRead with
        | .ok (.allTy (.opaque "Top.D") "x"
                 (.eqT (.opApp "Top.h" _ _) (.var _ "x"))) => true
        | _ => false)

-- The identity argument leaves nothing of itself behind, so the statement reads
-- the one operator the other argument names, once.
#guard (match decodeForm cancelTables jCanRead with
        | .ok f => EcForm.opsOf f == [("Top.h", canHSig)]
        | _ => false)

/-- The `Th_axiom` item `Top.canV`: a statement quantifying over an `x` of its own
and reading the declaration, whose binder carries that name too. -/
private def jCanVItem : Json :=
  Json.mkObj [("kind", Json.str "Th_axiom"), ("name", Json.str "canV"),
    ("path", Json.str "Top.canV"),
    ("decl", Json.mkObj
      [("tparams", Json.arr #[]), ("axiom_kind", Json.str "Lemma"),
       ("spec", Json.mkObj
         [("ty", jFormBool), ("kind", Json.str "Fquant"),
          ("quant", Json.str "Lforall"),
          ("binders", Json.arr #[jMaxBinder "x" 9110 jCanDTy]),
          ("body", jMaxApp jFormBool jBoolImpOp
            #[jMaxApp jFormBool
                (jMaxOpNode (jMaxFun2 jCanDTy jCanDTy jFormBool)
                  "Top.Pervasive.=" #[jCanDTy])
                #[jMaxApp jCanDTy (jMaxOpNode jCanDFun "Top.h" #[])
                    #[jMaxLocal jCanDTy "x" 9110],
                  jMaxLocal jCanDTy "x" 9110],
              jCanRead])])])]

-- The statement's own binder is bound under its source name, and the
-- declaration's binder, whose source name that one holds, under its source name
-- and its stamp. The reads under each resolve to the name its binder was bound
-- under.
#guard (match decodeAxiom cancelTables jCanVItem with
        | .ok (.allTy _ "x"
                 (.imp (.eqT _ (.var _ "x"))
                       (.allTy _ "x_1908" (.eqT _ (.var _ "x_1908"))))) => true
        | _ => false)

/-- `fun u w => u`, a lambda of two binders at a parameter the declaration
applies to one argument. -/
private def jCanLam2 : Json :=
  Json.mkObj
    [("ty", jCanDFun), ("kind", Json.str "Fquant"), ("quant", Json.str "Llambda"),
     ("binders", Json.arr #[jMaxBinder "u" 9121 jCanDTy,
                            jMaxBinder "w" 9122 jCanDTy]),
     ("body", jMaxLocal jCanDTy "u" 9121)]

/-- The read at that lambda. -/
private def jCanReadArity : Json := jMaxApp jFormBool jCanHead #[jCanLam2, jCanLamId]

-- An argument whose binders the application does not match in number is left
-- where it is put, and the node is named by the head it leaves behind.
#guard (match decodeForm cancelTables jCanReadArity with
        | .error m =>
          (m.splitOn "application of a head of kind 'Fquant'").length > 1
        | _ => false)

/-! ### A concrete definition whose body reads a definition over type parameters

`prelude/Logic.ec` declares

```
op injective ['a 'b] (f : 'a -> 'b) = forall x y, f x = f y => x = y.
```

and `algebra/Ring.ec` declares, in each of its ring theories,

```
op lreg (x : t) = injective (fun y => x * y).
```

The nodes below are the exporter's payload for the two, at the stamps and the
type-parameter order the export writes. `lreg`'s parameter and result types are
codes, so it registers as a concrete definition, and its body is an application
of a definition over type parameters, which the term layer has no image for: a
read of `lreg` in formula position is decoded as a formula. -/

/-- The type parameters of `injective`. -/
private def jInjB : Json := jTvar "'b" 1872
private def jInjA : Json := jTvar "'a" 1873

/-- The type of `injective`'s value parameter, `'a -> 'b`. -/
private def jInjFTy : Json := jTyArrow jInjA jInjB

private def jInjF : Json := jMaxLocal jInjFTy "f" 1874
private def jInjX : Json := jMaxLocal jInjA "x" 1876
private def jInjY : Json := jMaxLocal jInjA "y" 1878

/-- `forall x y, f x = f y => x = y`, the body `injective`'s lambda binds. -/
private def jInjBody : Json :=
  Json.mkObj
    [("ty", jFormBool), ("kind", Json.str "Fquant"),
     ("quant", Json.str "Lforall"),
     ("binders", Json.arr #[jMaxBinder "x" 1876 jInjA, jMaxBinder "y" 1878 jInjA]),
     ("body", jMaxApp jFormBool
       (jMaxOpNode (jMaxFun2 jFormBool jFormBool jFormBool) "Top.Pervasive.=>" #[])
       #[jMaxApp jFormBool
           (jMaxOpNode (jMaxFun2 jInjB jInjB jFormBool) "Top.Pervasive.=" #[jInjB])
           #[jMaxApp jInjB jInjF #[jInjX], jMaxApp jInjB jInjF #[jInjY]],
         jMaxApp jFormBool
           (jMaxOpNode (jMaxFun2 jInjA jInjA jFormBool) "Top.Pervasive.=" #[jInjA])
           #[jInjX, jInjY]])]

/-- The `Th_operator` item `Top.injective`. -/
def jInjectiveOp : Json :=
  Json.mkObj [("kind", Json.str "Th_operator"), ("name", Json.str "injective"),
    ("path", Json.str "Top.injective"),
    ("decl", Json.mkObj
      [("tparams", Json.arr #[Json.str "'b", Json.str "'a"]),
       ("ty", jTyArrow jInjFTy jFormBool),
       ("body", Json.mkObj
         [("kind", Json.str "OP_Plain"),
          ("form", Json.mkObj
            [("ty", jTyArrow jInjFTy jFormBool),
             ("kind", Json.str "Fquant"), ("quant", Json.str "Llambda"),
             ("binders", Json.arr #[jMaxBinder "f" 1874 jInjFTy]),
             ("body", jInjBody)])])])]

/-- The carrier `lreg` is declared over. -/
private def jLregTy : Json := jTyNode "Top.t"

/-- The signature the multiplication's declared type gives it. -/
private def lregMulSig : EcSig :=
  ⟨.prod (.opaque "Top.t") (.opaque "Top.t"), .opaque "Top.t"⟩

/-- `fun y => x * y`, the argument `lreg`'s body reads `injective` at. -/
private def jLregLam : Json :=
  Json.mkObj
    [("ty", jTyArrow jLregTy jLregTy), ("kind", Json.str "Fquant"),
     ("quant", Json.str "Llambda"),
     ("binders", Json.arr #[jMaxBinder "y" 11042 jLregTy]),
     ("body", jMaxApp jLregTy
       (jMaxOpNode (jMaxFun2 jLregTy jLregTy jLregTy) "Top.mul" #[])
       #[jMaxLocal jLregTy "x" 11041, jMaxLocal jLregTy "y" 11042])]

/-- The `Th_operator` item `Top.lreg`. -/
def jLregOp : Json :=
  Json.mkObj [("kind", Json.str "Th_operator"), ("name", Json.str "lreg"),
    ("path", Json.str "Top.lreg"),
    ("decl", Json.mkObj
      [("tparams", Json.arr #[]), ("ty", jTyArrow jLregTy jFormBool),
       ("body", Json.mkObj
         [("kind", Json.str "OP_Plain"),
          ("form", Json.mkObj
            [("ty", jTyArrow jLregTy jFormBool),
             ("kind", Json.str "Fquant"), ("quant", Json.str "Llambda"),
             ("binders", Json.arr #[jMaxBinder "x" 11041 jLregTy]),
             ("body", jMaxApp jFormBool
               (jMaxOpNode (jTyArrow (jTyArrow jLregTy jLregTy) jFormBool)
                 "Top.injective" #[jLregTy, jLregTy])
               #[jLregLam])])])])]

/-- The `Th_axiom` item `Top.lregV`, the statement `forall a, lreg a`. -/
def jLregVItem : Json :=
  Json.mkObj [("kind", Json.str "Th_axiom"), ("name", Json.str "lregV"),
    ("path", Json.str "Top.lregV"),
    ("decl", Json.mkObj
      [("tparams", Json.arr #[]), ("axiom_kind", Json.str "Lemma"),
       ("spec", Json.mkObj
         [("ty", jFormBool), ("kind", Json.str "Fquant"),
          ("quant", Json.str "Lforall"),
          ("binders", Json.arr #[jMaxBinder "a" 11050 jLregTy]),
          ("body", jMaxApp jFormBool
            (jMaxOpNode (jTyArrow jLregTy jFormBool) "Top.lreg" #[])
            #[jMaxLocal jLregTy "a" 11050])])])]

/-- The tables the lemma decodes against: the carrier at the opaque code, the
multiplication at the signature its declared type gives it, and the two
definitions. -/
private def lregTables : FormTables :=
  formTables
    ((registerThOperators (registerThTypes ecPrelude [jAbsTypeDecl "t" "Top.t"])
        [jInjectiveOp, jLregOp]).withAbstractOp "Top.mul" lregMulSig) []

-- `injective` registers over its type parameters and `lreg` as a definition
-- whose types are codes already.
#guard lregTables.tables.polyOpPaths.map Prod.fst == ["Top.injective"]
#guard lregTables.tables.defOpPaths.map Prod.fst == ["Top.lreg"]

-- `lreg`'s body applies a definition over type parameters, one of the two shapes
-- the term layer has no image for.
#guard (match List.lookup "Top.lreg" lregTables.tables.defOpPaths with
        | some d => defBodyIsForm lregTables.tables d.body
        | none => false)

-- The read decodes to the definition's body under one `letF` per parameter, and
-- that body to the quantified formula the definition it reads expands to.
#guard (match decodeAxiom lregTables jLregVItem with
        | .ok (.allTy _ "a"
                 (.letF "x_11041" (.var _ "a")
                   (.allTy _ "x" (.allTy _ "y"
                     (.imp (.eqT _ _) (.eqT (.var _ "x") (.var _ "y"))))))) => true
        | _ => false)

-- The multiplication the argument names is the operator the expanded statement
-- reads, and assembling the statement binds it.
#guard (match decodeAxiom lregTables jLregVItem with
        | .ok f =>
          (match f.assembleParams with
           | .allOp "Top.mul" s _ => s == lregMulSig
           | _ => false)
            && EcForm.opsOf f.assembleParams == []
        | _ => false)

-- Without the definition over type parameters the same read has no formula
-- route, and the term layer names the path the body applies.
#guard (match decodeAxiom
            (formTables ((registerThOperators
              (registerThTypes ecPrelude [jAbsTypeDecl "t" "Top.t"])
                [jLregOp]).withAbstractOp "Top.mul" lregMulSig) [])
            jLregVItem with
        | .error m => (m.splitOn "Top.injective").length > 1
        | _ => false)

/-- The `Th_axiom` item `Top.xorHolds`, the statement `forall b1 b2, b1 ^^ b2`:
a read of a concrete definition in formula position whose body is an application
of the prelude's equality. -/
def jXorHoldsItem : Json :=
  Json.mkObj [("kind", Json.str "Th_axiom"), ("name", Json.str "xorHolds"),
    ("path", Json.str "Top.xorHolds"),
    ("decl", Json.mkObj
      [("tparams", Json.arr #[]), ("axiom_kind", Json.str "Lemma"),
       ("spec", Json.mkObj
         [("ty", jXorBoolTy), ("kind", Json.str "Fquant"),
          ("quant", Json.str "Lforall"),
          ("binders", Json.arr #[jXorBinder "b1" 32541, jXorBinder "b2" 32543]),
          ("body", jXorApp jXorOpNode
            #[jXorLocal "b1" 32541, jXorLocal "b2" 32543])])])]

-- That body is neither quantified nor an application of a definition over type
-- parameters, so the read takes the term route and the formula is the term
-- holding.
#guard (match List.lookup "Top.^^" xorTables.tables.defOpPaths with
        | some d => !defBodyIsForm xorTables.tables d.body
        | none => false)

#guard (match decodeAxiom xorTables jXorHoldsItem with
        | .ok (.allTy .bool "b1" (.allTy .bool "b2"
                 (.holds (.letIn "b1_32499" _
                   (.letIn "b2_32500" _ (.beq _ (.bnot _))))))) => true
        | _ => false)

/-! ### A statement that quantifies over a function and applies it

`datatypes/Int.ec` declares

```
op iter ['a] : int -> ('a -> 'a) -> 'a -> 'a.
lemma iter1 ['a] (opr : 'a -> 'a) (x : 'a) : iter 1 opr x = opr x.
```

The nodes below are the exporter's payload for the lemma: a `Lforall` binder
whose `GTty` type is a `Tfun`, and a body equating a read of the declared `iter`
with an `Fapp` whose head is the `Flocal` that binder bound. The right-hand side
is the shape this file's higher-order route decodes — a function quantified over
and applied, with no lambda anywhere. -/

/-- The type parameter of the statement, at the stamp the export writes. -/
private def jIterTvar : Json := jTvar "'a" 6503

/-- The type of the quantified function, `'a -> 'a`. -/
private def jIterFunTy : Json := jTyArrow jIterTvar jIterTvar

/-- The signature `iter`'s declared type gives it at the assignment `'a := int`:
the three arguments as the right-nested product, and the carrier as the result. -/
private def iterSig : EcSig :=
  ⟨.prod .int (.prod (.arrow .int .int) .int), .int⟩

/-- The `Th_axiom` item `Top.IterOp.iter1`. -/
private def jIter1Item : Json :=
  Json.mkObj [("kind", Json.str "Th_axiom"), ("name", Json.str "iter1"),
    ("path", Json.str "Top.IterOp.iter1"),
    ("decl", Json.mkObj
      [("tparams", Json.arr #[Json.str "'a"]), ("axiom_kind", Json.str "Lemma"),
       ("spec", Json.mkObj
         [("ty", jFormBool), ("kind", Json.str "Fquant"),
          ("quant", Json.str "Lforall"),
          ("binders", Json.arr #[jMaxBinder "opr" 6505 jIterFunTy,
                                 jMaxBinder "x" 6506 jIterTvar]),
          ("body", jMaxApp jFormBool
            (jMaxOpNode (jMaxFun2 jIterTvar jIterTvar jFormBool)
              "Top.Pervasive.=" #[jIterTvar])
            #[jMaxApp jIterTvar
                (jMaxOpNode (jTyArrow jFormInt (jTyArrow jIterFunTy jIterFunTy))
                  "Top.IterOp.iter" #[jIterTvar])
                #[Json.mkObj [("ty", jFormInt), ("kind", Json.str "Fint"),
                              ("value", Json.str "1")],
                  jMaxLocal jIterFunTy "opr" 6505,
                  jMaxLocal jIterTvar "x" 6506],
              jMaxApp jIterTvar (jMaxLocal jIterFunTy "opr" 6505)
                #[jMaxLocal jIterTvar "x" 6506]])])])]

/-- The tables the lemma decodes against: `iter` at the signature its declared
type gives it, at the assignment the guards below read the statement at. -/
private def iterTables : FormTables :=
  formTables (ecPrelude.withAbstractOp "Top.IterOp.iter" iterSig) []

-- The binder's type is a function type, so the statement quantifies at an arrow
-- code, and the right-hand side is that variable applied to the second binder.
#guard (match decodeAxiomAt iterTables [.int] jIter1Item with
        | .ok (.allTy (.arrow .int .int) "opr"
                 (.allTy .int "x"
                   (.eqT _ (.app (.var _ "opr") (.var _ "x"))))) => true
        | _ => false)

-- The left-hand side is the declared operator applied to the three arguments as
-- the right-nested pair, the function among them.
#guard (match decodeAxiomAt iterTables [.int] jIter1Item with
        | .ok (.allTy _ "opr" (.allTy _ "x" (.eqT lhs _))) =>
          lhs.opAppOf == some ("Top.IterOp.iter", iterSig)
        | _ => false)

-- The statement reads that one operator and binds none, so assembling it binds
-- exactly the operator.
#guard (match decodeAxiomAt iterTables [.int] jIter1Item with
        | .ok f => EcForm.opsOf f == [("Top.IterOp.iter", iterSig)]
        | _ => false)

end Golden

end CatCrypt.Crypto.EasyCryptImport

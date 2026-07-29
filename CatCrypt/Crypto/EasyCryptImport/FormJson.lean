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
| `Fpvar` of `PVloc res` | `EcTerm.res` at the memory's side |
| `Fpvar` of `PVglob` | `EcTerm.glob` |
| `Fapp` of a boolean operator | the matching `EcTerm` node, or the matching `EcForm` connective |
| `Fapp` of `=` at a type code | `EcTerm.beq` / `EcForm.eqT` |
| `Fapp` of `=`, `<=`, `<` at `real` | `EcForm.probCmp` |
| `Ftuple`, `Fproj` | `EcTerm.pair`, `.fst` / `.snd` |
| `Fif`, `Flet` of an `LSymbol` | `EcTerm.ite` / `EcForm.ifF`, `EcTerm.letIn` / `EcForm.letF` |
| `Fapp` of `=` between two `Fglob` | `EcForm.memEqOn` / `.memEqOnMod` |
| `Fquant` of `GTty` / `GTmem` / `GTmodty` | `EcForm.allTy` / `.exTy`, `.allMem` / `.exMem`, `.allMod` / `.allModOn` or `.allModRestr` / `.allModRestrOn` |
| `Fquant` of `GTty` at `real` | `EcForm.allProb` |
| `FhoareF`, `FbdHoareF`, `FequivF` | `EcForm.hoare`, `.bdHoare`, `.equiv` |
| `FbdHoareF` over an abstract module's procedure | `EcForm.lossless` |
| `Fpr` | `EcProb.pr` |
| `Fapp` of real `+`, `*` | `EcProb.add`, `.mul` |
| `Fapp` of `\|·\|` to a difference | `EcProb.absDiff` |
| `Fapp` of `from_int` to a non-negative `Fint` | `EcProb.const` |

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
* `Fint`, and any real term outside the probability fragment — in particular a
  quotient, a signed negation, and a signed difference of two probabilities;
* `Fpvar` of a `PVloc` other than `res`, the procedure-local read at a memory;
* `Fquant` of a lambda, and an existential over a module type;
* a module restriction that names individual procedures, or that lists what the
  module may touch rather than what it may not: the emitted hypothesis is stated
  against a module's footprint;
* a bounded Hoare judgement over an abstract module's procedure other than
  `islossless`: the module has no body to reason against;
* a `Th_axiom` with type parameters;
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
is built from, and propositional equivalence. -/
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
  /-- Real absolute value. -/
  realAbs : String
  /-- The non-strict order on the reals. -/
  realLe : String
  /-- The strict order on the reals. -/
  realLt : String
  /-- Propositional equivalence. -/
  iffOp : String
  /-- The name EasyCrypt gives the result of a judgement. -/
  resName : String

/-- The paths of EasyCrypt's real prelude and of `<=>`. -/
def ecFormPaths : FormPaths where
  realTy := "Top.Pervasive.real"
  realFromInt := "Top.CoreReal.from_int"
  realAdd := "Top.CoreReal.add"
  realMul := "Top.CoreReal.mul"
  realOpp := "Top.CoreReal.opp"
  realAbs := "Top.Real.`|_|"
  realLe := "Top.CoreReal.le"
  realLt := "Top.CoreReal.lt"
  iffOp := "Top.Pervasive.<=>"
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

/-- The tables for a statement about the modules of one export, with no binder in
scope. -/
def formTables (T : DecodeTables) (procSigs : List (String × EcSig))
    (modTypes : List (String × EcInterface) := [])
    (modGlobals : List (String × List EcGlobal) := []) : FormTables where
  tables := T
  paths := ecFormPaths
  procSigs := procSigs
  modTypes := modTypes
  modGlobals := modGlobals
  modBinders := []
  modBinderStamps := []
  mems := []
  locals := []

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
      fail s!"the procedure '{q}' is not in the ingestion's signature table and \
        names no procedure of a module binder in scope, so the signature its \
        judgement carries cannot be reconstructed"

/-! ## Module restrictions

An exported restriction is a `use_restr` over procedure paths and over module
paths: a negative set of what the module may not touch, and an optional positive
set of what it may. Only the negative module set has an image — the footprint of
the named modules' `var` declarations — so the other three components are
rejected rather than dropped. -/

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

/-- The footprint an exported module restriction names: the `var` declarations of
every module in its negative module set, or `none` when the restriction is
empty. -/
def restrGlobals (F : FormTables) (g : Json) : Except String (Option (List EcGlobal)) := do
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
    let gss ← ms.mapM (fun m =>
      match List.lookup m F.modGlobals with
      | some gs => .ok gs
      | none =>
        fail s!"the restricting module '{m}' is not in the ingestion's \
          module-globals table, so the footprint it names is unknown")
    .ok (some gss.flatten)

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
    fail s!"application of a head of kind '{k}' in {j.compress}: a formula \
      applies operators only, and the AST has no higher-order application"

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

/-- Whether a node is an application of the operator `p`. -/
def isAppOf (p : String) (j : Json) : Bool :=
  match j.getObjValAs? String "kind" with
  | .ok "Fapp" =>
    match appHeadPath j with
    | .ok q => q == p
    | .error _ => false
  | _ => false

/-- Transport a term along an equality of type codes. -/
def EcTerm.castTy {a b : EcTy} (h : a = b) (e : EcTerm a) : EcTerm b :=
  cast (congrArg EcTerm h) e

/-- The judgement node kinds, which are formulas and never terms or
probabilities. -/
def judgementKinds : List String :=
  ["FhoareF", "FhoareS", "FbdHoareF", "FbdHoareS", "FeHoareF", "FeHoareS",
   "FequivF", "FequivS", "FeagerF"]

/-! ## Terms

A term decodes at the type code the context expects, and the node's own `ty`
field must agree with it, exactly as an expression does in `Json.lean`. `EcTerm`
contains no formula, so this decoder stands outside the mutual recursion
below. -/

/-- Decode a formula node in term position, at the type code `t`. -/
def decodeTerm (F : FormTables) (t : EcTy) (j : Json) : Except String (EcTerm t) :=
  match getStr j "kind" with
  | .error e => .error e
  | .ok kind =>
    if kind = "Fint" then
      fail s!"integer term in {j.compress}: EcTy has no int code, so an integer \
        term has no EcTerm image"
    else if kind = "Fglob" then
      fail s!"'glob M' in value position in {j.compress}: a memory restricted to \
        a module's footprint is not a value of an EcTy"
    else if kind = "Fmatch" then
      fail s!"match term in {j.compress}: EcTy has no sum or inductive codes, so \
        there is nothing to match on"
    else if kind = "Fquant" then
      fail s!"quantified term in {j.compress}: EcTerm has no binder"
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
        if kind = "Flocal" then
          match localNameOf F j with
          | .error e => .error e
          | .ok x => .ok (.var t x)
        else if kind = "Fop" then
          match getStr j "path" with
          | .error e => .error e
          | .ok p =>
            match List.lookup p F.tables.constPaths with
            | none =>
              fail s!"unknown nullary operator path '{p}' in {j.compress}: the \
                ingestion's constant table has no entry, so the operator has no \
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
              match arr.toList.attach with
              | [⟨x, _⟩, ⟨y, _⟩] =>
                match decodeTerm F a x with
                | .error e => .error e
                | .ok xe =>
                  match decodeTerm F b y with
                  | .error e => .error e
                  | .ok ye => .ok (.pair xe ye)
              | _ => fail s!"tuple of {arr.size} components at a binary product code"
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
                      match F.bindLocal st nm with
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
        else if kind = "Fapp" then
          match getObj j "f" with
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
                  fail s!"unknown operator path '{p}' applied in {j.compress}: \
                    the ingestion's operator table has no entry, so the \
                    application has no EcTerm image"
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
                    | _, _ =>
                      fail s!"operator '{p}' cannot produce a value of type {repr t}"
            | .ok k =>
              fail s!"application of a head of kind '{k}': the AST applies \
                operators only, and has no higher-order application"
        else
          fail s!"unsupported formula node kind '{kind}' in term position in \
            {j.compress}"
termination_by jsonSize j
decreasing_by
  all_goals first
    | exact getArr_decreases (by assumption) (Array.mem_toList_iff.mp ‹_ ∈ Array.toList _›)
    | exact getObj_decreases (by assumption)

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
sits under, so the formula decoder makes a single recursive call, on the body. -/

/-- The tables extended by one binder, and the quantifier node it wraps a formula
in. -/
def bindBinder (F : FormTables) (q : String) (b : Json) :
    Except String (FormTables × (EcForm → EcForm)) := do
  let nm ← getStr b "name"
  let st ← getNat b "stamp"
  let g ← getObj b "gty"
  match ← getStr g "kind" with
  | "GTty" =>
    if tyConstrPath g "ty" == some F.paths.realTy then
      if q = "Lforall" then
        let F' ← F.bindLocal st nm
        .ok (F', fun body => .allProb nm body)
      else
        fail s!"the real-valued binder '{nm}' under '{q}': EcForm quantifies a \
          probability parameter universally only"
    else
      let t ← decodeTyField F.tables g "ty"
      if q = "Lforall" then
        let F' ← F.bindLocal st nm
        .ok (F', fun body => .allTy t nm body)
      else if q = "Lexists" then
        let F' ← F.bindLocal st nm
        .ok (F', fun body => .exTy t nm body)
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
    match List.lookup mtName F.modTypes with
    | none =>
      fail s!"the module type '{mtName}' is not in the ingestion's module-type \
        table, so the binder has no interface"
    | some I =>
      if q = "Lforall" then
        let gs ← restrGlobals F g
        let F' := F.bindModBinder st nm I
        match gs with
        | none =>
          .ok (F', fun body =>
            if body.namesGlobOf nm then .allModOn nm I body else .allMod nm I body)
        | some gs =>
          .ok (F', fun body =>
            if body.namesGlobOf nm then .allModRestrOn nm I gs body
            else .allModRestr nm I gs body)
      else
        fail s!"the module binder '{nm}' under '{q}': EcForm quantifies a module \
          universally only"
  | k => fail s!"unknown binder sort '{k}' in {g.compress}"

/-- The tables extended by every binder of a quantifier node, and the chain of
quantifier nodes its body sits under. -/
def bindBinders (F : FormTables) (q : String) : List Json →
    Except String (FormTables × (EcForm → EcForm))
  | [] => .ok (F, id)
  | b :: rest => do
    let (F₁, w₁) ← bindBinder F q b
    let (F₂, w₂) ← bindBinders F₁ q rest
    .ok (F₂, fun body => w₁ (w₂ body))

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

/-- The value a real literal denotes. A bound in the fragment is a closed
constant, and `from_int` of a non-negative integer is its only shape. -/
def decodeRealLit (F : FormTables) (j : Json) : Except String ℝ≥0∞ := do
  let p ← appHeadPath j
  if p ≠ F.paths.realFromInt then
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
        | some m => .ok (m : ℝ≥0∞)
        | none =>
          fail s!"the integer literal '{v}' is not a non-negative decimal, and a \
            negative bound has no image in ℝ≥0∞"
    | _ => fail s!"'{p}' applied to {arr.size} arguments, expected 1"

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
          match bindBinders F q bs.toList with
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
                  match F.bindLocal st nm with
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
      | .error e => .error e
      | .ok p =>
        match _hfa : getArr j "args" with
        | .error e => .error e
        | .ok arr =>
          if p = F.paths.realLe || p = F.paths.realLt then
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
            | _ =>
              match decodeTerm F .bool j with
              | .error e => .error e
              | .ok b => .ok (.holds b)
    else
      match decodeTerm F .bool j with
      | .error e => .error e
      | .ok b => .ok (.holds b)
termination_by jsonSize j
decreasing_by
  all_goals first
    | exact getObj_decreases (by assumption)
    | exact getArr_decreases (by assumption) (Array.mem_toList_iff.mp ‹_ ∈ Array.toList _›)

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
termination_by jsonSize j
decreasing_by exact getObj_decreases _hmain

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
            else
              fail s!"the real operator '{p}' in {j.compress}: EcProb has \
                Pr[…], a constant, a parameter, a sum, a product and an \
                absolute difference, and nothing else"
    else
      fail s!"the node kind '{kind}' in probability position in {j.compress}"
termination_by jsonSize j
decreasing_by
  all_goals first
    | exact getObj_decreases _hev
    | exact getArr_decreases _hpa (Array.mem_toList_iff.mp ‹_ ∈ Array.toList _›)

/-- Decode the event of a `Pr[…]` node. Its memory is the post-state the
procedure leaves, which is the judgement's own memory. -/
def decodeProbEvent (F : FormTables) (j : Json) : Except String EcForm :=
  match memStampOf j "mem" with
  | .error e => .error e
  | .ok st =>
    match _hpe : getObj j "form" with
    | .error e => .error e
    | .ok formJ => decodeForm (F.bindMemStamp st (.side .cur)) formJ
termination_by jsonSize j
decreasing_by exact getObj_decreases _hpe

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
termination_by jsonSize j
decreasing_by
  all_goals exact getArr_decreases _hda (Array.mem_toList_iff.mp ‹_ ∈ Array.toList _›)

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
termination_by jsonSize j
decreasing_by
  all_goals exact getArr_decreases _hna (Array.mem_toList_iff.mp ‹_ ∈ Array.toList _›)

end

/-! ## Lemmas -/

/-- Decode a `Th_axiom` item's statement. -/
def decodeAxiom (F : FormTables) (j : Json) : Except String EcForm := do
  let kind ← getStr j "kind"
  if kind ≠ "Th_axiom" then
    fail s!"theory item of kind '{kind}': only Th_axiom carries a statement"
  else
    let name ← getStr j "name"
    let decl ← getObj j "decl"
    let tparams ← getArr decl "tparams"
    if !tparams.isEmpty then
      fail s!"the statement '{name}' has {tparams.size} type parameters, and \
        EcForm has no type quantifier"
    else
      let spec ← getObj decl "spec"
      decodeForm F spec

/-- The signature of each procedure of a decoded module, keyed by the path the
exporter names it by at a judgement or probability site. -/
def procSigsOfStructure (S : DecodedStructure) : List (String × EcSig) :=
  S.procs.map (fun d => (xqualify S.path d.name, d.sp.sig))

/-- Decode the statement of the lemma `name` from an exporter envelope. -/
def importAxiom (F : FormTables) (name : String) (j : Json) : Except String EcForm := do
  let e ← decodeEnvelope j
  let it ← findItem e name
  decodeAxiom F it

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
has an `int` global, `Game` is a functor and `Risky` raises — so it is the one
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

-- `Pr[Ideal.main(true) @ &m : res] = 1%r / 2%r`: the bound is a quotient, and
-- `EcProb` has no division.
#guard (match formsStatement "ideal_uniform" with
        | .error _ => true
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
-- not in this fixture's module-type table, so the binder has no interface.
#guard (match formsStatement "glob_refl" with
        | .error _ => true
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
the argument EasyCrypt leaves implicit is not reconstructible, and `Enc` has an
`int` global, so its body is outside the accepted program fragment and its
signatures never reach the table. `hoare.expected.json`, the export of
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
                | [("Top.Coin./b", { name := "Top.Coin./b", id := 0, ty := .bool })] => true
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
-- at `EcCmp.eq`. The bound is left open in this pattern and the two below because
-- `ℝ≥0∞` has no computable equality, as in the `otp_pr_diff` guard of
-- `Examples/OTPEquivImport.lean`: these guards pin the shape of the statement and
-- the comparison, and not the value of the constant.
#guard (match hoareStatement "toss_lossless" with
        | .ok (.bdHoare "Top.Coin./toss" ⟨.unit, .bool⟩ (.lit ()) .tru .tru .eq _) => true
        | _ => false)

-- `phoare [Coin.toss : Coin.b = false ==> res] <= 1%r` decodes at `EcCmp.le`.
#guard (match hoareStatement "toss_le" with
        | .ok (.bdHoare "Top.Coin./toss" ⟨.unit, .bool⟩ (.lit ()) (.eqT a b)
                 (.holds (.res .bool .cur)) .le _) =>
          isGlobReadAt a "Top.Coin./b" 0 (.side .cur) && isBoolLit b false
        | _ => false)

-- `phoare [Coin.toss : true ==> res /\ Coin.b = true] >= 0%r` decodes at
-- `EcCmp.ge`.
#guard (match hoareStatement "toss_ge" with
        | .ok (.bdHoare "Top.Coin./toss" ⟨.unit, .bool⟩ (.lit ()) .tru
                 (.and (.holds (.res .bool .cur)) (.eqT a b)) .ge _) =>
          isGlobReadAt a "Top.Coin./b" 0 (.side .cur) && isBoolLit b true
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
        | .ok (.const _) => true
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
        | .ok (.absDiff (.const _) (.const _)) => true
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

-- An integer term is rejected.
#guard (match decodeTerm bareTables .bool
            (Json.mkObj [("ty", jFormBool), ("kind", Json.str "Fint"),
                         ("value", Json.str "3")]) with
        | .error _ => true
        | _ => false)

-- A node the exporter marked as outside its coverage is rejected.
#guard (match decodeForm bareTables
            (Json.mkObj [("kind", Json.str "Unsupported"),
                         ("what", Json.str "Fmatch"),
                         ("pp", Json.str "match o with")]) with
        | .error _ => true
        | _ => false)

end Golden

end CatCrypt.Crypto.EasyCryptImport

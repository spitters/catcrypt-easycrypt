/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.EasyCryptImport.Json

/-!
# EasyCrypt import: emitting the decoded AST as Lean source

This module renders the importer's AST (`Ty.lean`, `Ast.lean`) as Lean source
text: `emitTy`, `emitVal`, `emitExpr`, `emitStmt`, `emitGame`, `emitModule` print
a value as a term that elaborates to that value, and `emitFile` wraps a printed
declaration in a provenance header and the imports it needs.

## Why the AST is printed rather than decoded in a proof

The decoders of `Json.lean` are well-founded recursive, so `decodeGame` has no
kernel-reducible equations: a decoded game cannot be evaluated inside a proof,
and the golden checks of `Json.lean` are `#guard` commands rather than `rfl`
proofs. The pipeline therefore runs the decoder at tool time and commits its
output as Lean source, matching how `haxpipeT` emits committed Lean for the Rust
frontend: `emitFromJson` decodes an exporter envelope and prints a module, that
module is committed, and theorems are proved about the committed literal, which
is a term the kernel reduces.

## Intrinsic typing in the printed term

`EcExpr` is indexed by an `EcTy` code, and the emitter prints that code as a named
argument wherever neither the result type nor the printed subterms determine it:

* `EcExpr.lit`'s value argument is at `t.interp`, and `EcTy.interp` is a function
  on codes, so a value does not determine the code it comes from: the literal is
  printed as `EcExpr.lit (t := <code>) <value>`, with the value printed by
  `emitVal` at that code;
* `EcExpr.beq`'s comparison type and `EcExpr.fst`/`.snd`'s discarded component do
  not appear in the result type, and neither do the key and value codes of
  `EcExpr.mapMem` and `EcExpr.mapGetD`.

`EcExpr.pair`'s component codes and `EcExpr.finAdd`'s cardinality are printed as
named arguments too, so that every printed expression elaborates without an
expected type propagated from its context. `EcDistr` is printed the same way, by
`emitDistr`.

Everywhere else the index is fixed by the enclosing constructor's printed
arguments — `EcStmt.assign` prints its type code before the expression,
`EcStmt.store` prints the global whose `ty` field is the expression's index, and
`EcStmt.callProc` prints the signature whose `arg` field is the argument's index
— so the printed term elaborates with no further ascription.

## Emitting a module

`EcModule.procs` and `EcInterface.sig` are functions, so `emitModule` prints the
shape `decodeModule` builds: an association list of `SigProc` entries, and the
module's two function fields as `sigProcOf` against that list. The list holds one
entry per name of `M.interface.names`, so the printed module agrees with `M` at
every declared name and sends every other name to `undeclaredProc`. A name
outside `names` is undeclared, which is the convention `EcInterface` records.
`emitInterface` prints a standalone interface — a module type, as `Modules.lean`
uses it for an abstract module's declared procedures — the same way, as
`interfaceOfSigs` over its declared names; a module's own interface is printed by
`emitModule`, since its `sig` field is the signature component of the module's
procedure list.

## Emitting a functor

An `EcFunctor` is a module together with the name and the interface of its
parameter, and both of those print with what is already here: `emitModule` for the
body, `emitInterface` for the parameter's module type. `emitFunctor` prints the
body's declarations under `<declName>Body` and the functor over them.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.EasyCryptImport

open Lean (Json)

/-! ## Atoms -/

/-- Lines joined by newlines, with a trailing newline. -/
def emitLines (ls : List String) : String := String.intercalate "\n" ls ++ "\n"

/-- A string as a Lean string literal. -/
def emitStr (s : String) : String := String.quote s

/-- A list of already-printed terms as a Lean list literal. -/
def emitTerms (xs : List String) : String :=
  "[" ++ String.intercalate ", " xs ++ "]"

/-- A type code as a Lean term. -/
def emitTy : EcTy → String
  | .unit => "EcTy.unit"
  | .bool => "EcTy.bool"
  | .fin n => s!"(EcTy.fin {n})"
  | .prod a b => s!"(EcTy.prod {emitTy a} {emitTy b})"
  | .int => "EcTy.int"
  | .map a b => s!"(EcTy.map {emitTy a} {emitTy b})"

/-- A value of `t.interp` as a Lean term at that type. A `fin n` value is printed
as a numeral ascribed to `Fin (n + 1)`, and a map value as an association-list
literal ascribed to the interpretation of its code. -/
def emitVal : (t : EcTy) → t.interp → String
  | .unit, _ => "()"
  | .bool, b => match (show Bool from b) with | true => "true" | false => "false"
  | .fin n, k => s!"({k.val} : Fin {n + 1})"
  | .prod a b, v => "(" ++ emitVal a v.1 ++ ", " ++ emitVal b v.2 ++ ")"
  | .int, z => "(" ++ toString (show Int from z) ++ " : Int)"
  | .map a b, m =>
      "([" ++ String.intercalate ", "
        ((show List (a.interp × b.interp) from m).map (fun kv =>
          "(" ++ emitVal a kv.1 ++ ", " ++ emitVal b kv.2 ++ ")"))
        ++ "] : " ++ emitTy (.map a b) ++ ".interp)"

/-- A procedure signature as a Lean term. -/
def emitSig (s : EcSig) : String :=
  "(EcSig.mk " ++ emitTy s.arg ++ " " ++ emitTy s.res ++ ")"

/-- A module-scoped global as a Lean term. -/
def emitGlobal (g : EcGlobal) : String :=
  "(EcGlobal.mk " ++ emitStr g.name ++ " " ++ toString g.id ++ " "
    ++ emitTy g.ty ++ ")"

/-- A local variable's identity as a Lean term. A program variable carries no
stamp and is printed as its source name, which elaborates at `EcVarId` through
`EcVarId.ofName`; a stamped identifier is printed with both fields. -/
def emitVarId (x : EcVarId) : String :=
  match x.stamp with
  | none => emitStr x.name
  | some s => "(EcVarId.mk " ++ emitStr x.name ++ " (some " ++ toString s ++ "))"

/-! ## Expressions -/

/-- An expression as a Lean term, with a named argument for every index the result
type does not determine. -/
def emitExpr : {t : EcTy} → EcExpr t → String
  | _, .var t x => "(EcExpr.var " ++ emitTy t ++ " " ++ emitVarId x ++ ")"
  | t, .lit v => "(EcExpr.lit (t := " ++ emitTy t ++ ") " ++ emitVal t v ++ ")"
  | _, .bnot e => "(EcExpr.bnot " ++ emitExpr e ++ ")"
  | _, .band a b => "(EcExpr.band " ++ emitExpr a ++ " " ++ emitExpr b ++ ")"
  | _, .bxor a b => "(EcExpr.bxor " ++ emitExpr a ++ " " ++ emitExpr b ++ ")"
  | _, @EcExpr.beq t a b =>
      "(EcExpr.beq (t := " ++ emitTy t ++ ") " ++ emitExpr a ++ " "
        ++ emitExpr b ++ ")"
  | _, @EcExpr.pair a b x y =>
      "(EcExpr.pair (a := " ++ emitTy a ++ ") (b := " ++ emitTy b ++ ") "
        ++ emitExpr x ++ " " ++ emitExpr y ++ ")"
  | _, @EcExpr.fst a b p =>
      "(EcExpr.fst (a := " ++ emitTy a ++ ") (b := " ++ emitTy b ++ ") "
        ++ emitExpr p ++ ")"
  | _, @EcExpr.snd a b p =>
      "(EcExpr.snd (a := " ++ emitTy a ++ ") (b := " ++ emitTy b ++ ") "
        ++ emitExpr p ++ ")"
  | _, @EcExpr.finAdd n a b =>
      "(EcExpr.finAdd (n := " ++ toString n ++ ") " ++ emitExpr a ++ " "
        ++ emitExpr b ++ ")"
  | _, .intAdd a b => "(EcExpr.intAdd " ++ emitExpr a ++ " " ++ emitExpr b ++ ")"
  | _, .intLe a b => "(EcExpr.intLe " ++ emitExpr a ++ " " ++ emitExpr b ++ ")"
  | _, .mapSet m k v =>
      "(EcExpr.mapSet " ++ emitExpr m ++ " " ++ emitExpr k ++ " " ++ emitExpr v ++ ")"
  | _, @EcExpr.mapMem a b m k =>
      "(EcExpr.mapMem (a := " ++ emitTy a ++ ") (b := " ++ emitTy b ++ ") "
        ++ emitExpr m ++ " " ++ emitExpr k ++ ")"
  | _, @EcExpr.mapGetD a b m k d =>
      "(EcExpr.mapGetD (a := " ++ emitTy a ++ ") (b := " ++ emitTy b ++ ") "
        ++ emitExpr m ++ " " ++ emitExpr k ++ " " ++ emitExpr d ++ ")"

/-! ## Distributions -/

/-- A distribution expression as a Lean term. The carrier codes that neither the
result type nor the printed subterms determine are printed as named arguments —
`EcDistr.point`'s and `EcDistr.cond`'s carrier, `EcDistr.map`'s and
`EcDistr.letD`'s source and target, `EcDistr.scale`'s and `EcDistr.restrict`'s
carrier — so a printed distribution elaborates without an expected type propagated
from its context. `EcDistr.prod`'s two codes are determined by its factors.
`EcDistr.uniform`'s finiteness argument is its `by rfl` default, as
`EcStmt.sample`'s is. -/
def emitDistr : {t : EcTy} → EcDistr t → String
  | _, .uniform t _ => "(EcDistr.uniform " ++ emitTy t ++ ")"
  | t, .point e =>
      "(EcDistr.point (t := " ++ emitTy t ++ ") " ++ emitExpr e ++ ")"
  | _, @EcDistr.map a b d x e =>
      "(EcDistr.map (a := " ++ emitTy a ++ ") (b := " ++ emitTy b ++ ") "
        ++ emitDistr d ++ " " ++ emitVarId x ++ " " ++ emitExpr e ++ ")"
  | _, @EcDistr.cond t d x p =>
      "(EcDistr.cond (t := " ++ emitTy t ++ ") " ++ emitDistr d ++ " "
        ++ emitVarId x ++ " " ++ emitExpr p ++ ")"
  | _, @EcDistr.letD a b d x body =>
      "(EcDistr.letD (a := " ++ emitTy a ++ ") (b := " ++ emitTy b ++ ") "
        ++ emitDistr d ++ " " ++ emitVarId x ++ " " ++ emitDistr body ++ ")"
  | _, @EcDistr.prod _ _ d₁ d₂ =>
      "(EcDistr.prod " ++ emitDistr d₁ ++ " " ++ emitDistr d₂ ++ ")"
  | _, @EcDistr.scale t d =>
      "(EcDistr.scale (t := " ++ emitTy t ++ ") " ++ emitDistr d ++ ")"
  | _, @EcDistr.restrict t d x p =>
      "(EcDistr.restrict (t := " ++ emitTy t ++ ") " ++ emitDistr d ++ " "
        ++ emitVarId x ++ " " ++ emitExpr p ++ ")"

/-! ## Statements -/

mutual

/-- A statement as a Lean term on one line. -/
def emitStmt : EcStmt → String
  | .assign t x e =>
      "(EcStmt.assign " ++ emitTy t ++ " " ++ emitStr x ++ " " ++ emitExpr e ++ ")"
  | .sample t x _ => "(EcStmt.sample " ++ emitTy t ++ " " ++ emitStr x ++ ")"
  | .sampleD t x d =>
      "(EcStmt.sampleD " ++ emitTy t ++ " " ++ emitStr x ++ " " ++ emitDistr d ++ ")"
  | .load g x => "(EcStmt.load " ++ emitGlobal g ++ " " ++ emitStr x ++ ")"
  | .store g e => "(EcStmt.store " ++ emitGlobal g ++ " " ++ emitExpr e ++ ")"
  | .ite c thn els =>
      "(EcStmt.ite " ++ emitExpr c ++ " " ++ emitTerms (emitStmtList thn) ++ " "
        ++ emitTerms (emitStmtList els) ++ ")"
  | .forN n body =>
      "(EcStmt.forN " ++ toString n ++ " " ++ emitTerms (emitStmtList body) ++ ")"
  | .call p => "(EcStmt.call " ++ emitStr p ++ ")"
  | .callProc q s arg x =>
      "(EcStmt.callProc " ++ emitStr q ++ " " ++ emitSig s ++ " "
        ++ emitExpr arg ++ " " ++ emitStr x ++ ")"

/-- The statements of a block, each as a Lean term on one line. -/
def emitStmtList : List EcStmt → List String
  | [] => []
  | s :: ss => emitStmt s :: emitStmtList ss

end

/-- A statement block as a Lean list literal on one line. -/
def emitBlock (ss : List EcStmt) : String := emitTerms (emitStmtList ss)

/-- A statement block as a Lean list literal, one statement per line, opened on a
fresh line and indented by `ind`. A block nested inside a statement stays on that
statement's line. -/
def emitBlockLines (ind : String) (ss : List EcStmt) : String :=
  match emitStmtList ss with
  | [] => "\n" ++ ind ++ "[]"
  | ls => "\n" ++ ind ++ "[ " ++ String.intercalate (",\n" ++ ind ++ "  ") ls ++ " ]"

/-! ## Declarations -/

/-- A game as a Lean `def` of type `EcGame` named `declName`. -/
def emitGame (declName : String) (g : EcGame) : String :=
  emitLines
    [ "/-- The imported EasyCrypt game `" ++ g.name ++ "`. -/",
      "def " ++ declName ++ " : EcGame where",
      "  name := " ++ emitStr g.name,
      "  locals := " ++ emitTerms (g.locals.map emitStr),
      "  procs := "
        ++ emitTerms (g.procs.map (fun p =>
             "(" ++ emitStr p.1 ++ ", " ++ emitBlock p.2 ++ ")")),
      "  body :=" ++ emitBlockLines "    " g.body,
      "  ret := " ++ emitExpr g.ret ]

/-- A procedure at a signature as a `SigProc` term whose continuation lines are
indented by `ind`. -/
def emitSigProc (ind : String) (sp : SigProc) : String :=
  "{ sig := " ++ emitSig sp.sig ++ "\n"
    ++ ind ++ "  proc := EcProcAt.mk " ++ emitStr sp.proc.param
    ++ emitBlockLines (ind ++ "    ") sp.proc.body ++ "\n"
    ++ ind ++ "    " ++ emitExpr sp.proc.ret ++ " }"

/-- An interface as a Lean term: `interfaceOfSigs` over the signature of each
declared name. `EcInterface.sig` is a function and `names` is what it declares, so
the printed interface agrees with the argument at every declared name and sends
every other name to the unit-to-unit signature. -/
def emitInterface (I : EcInterface) : String :=
  "(interfaceOfSigs "
    ++ emitTerms (I.names.map (fun p =>
         "(" ++ emitStr p ++ ", " ++ emitSig (I.sig p) ++ ")"))
    ++ ")"

/-- The declared procedures of a module, as a list of name/`SigProc` pairs. -/
def sigProcsOfModule (M : EcModule) : List (String × SigProc) :=
  M.interface.names.map (fun p => (p, ⟨M.interface.sig p, M.procs p⟩))

/-- A module as two Lean `def`s: `<declName>Procs`, the association list of its
declared procedures, and `<declName>`, the `EcModule` whose `interface.sig` and
`procs` are `sigProcOf` against that list. -/
def emitModule (declName : String) (M : EcModule) : String :=
  let entries := (sigProcsOfModule M).map (fun e =>
    "    (" ++ emitStr e.1 ++ ",\n      " ++ emitSigProc "      " e.2 ++ ")")
  emitLines
    [ "/-- The procedures the imported module `" ++ M.name ++ "` declares. -/",
      "def " ++ declName ++ "Procs : List (String × SigProc) :=",
      "  [",
      String.intercalate ",\n" entries,
      "  ]",
      "",
      "/-- The imported EasyCrypt module `" ++ M.name ++ "`. -/",
      "def " ++ declName ++ " : EcModule where",
      "  name := " ++ emitStr M.name,
      "  interface :=",
      "    { names := " ++ emitTerms (M.interface.names.map emitStr),
      "      sig := fun p => (sigProcOf " ++ declName ++ "Procs p).sig }",
      "  globals := " ++ emitTerms (M.globals.map emitGlobal),
      "  procs := fun p => (sigProcOf " ++ declName ++ "Procs p).proc" ]

/-- A functor as the `def`s of its body — printed by `emitModule` under
`<declName>Body` — followed by `<declName>`, the `EcFunctor` over them. The
parameter's interface is a module type and is printed by `emitInterface`; the
parameter's name is the prefix the body calls it by. -/
def emitFunctor (declName : String) (F : EcFunctor) : String :=
  emitModule (declName ++ "Body") F.body
    ++ emitLines
      [ "",
        "/-- The imported EasyCrypt functor `" ++ F.name ++ "`. -/",
        "def " ++ declName ++ " : EcFunctor where",
        "  name := " ++ emitStr F.name,
        "  paramName := " ++ emitStr F.paramName,
        "  paramInterface := " ++ emitInterface F.paramInterface,
        "  body := " ++ declName ++ "Body" ]

/-! ## Files -/

/-- The item a generated module declares. -/
inductive EmitItem where
  /-- A closed game. -/
  | game (g : EcGame)
  /-- A concrete module. -/
  | «module» (M : EcModule)
  /-- A functor. -/
  | functor (F : EcFunctor)

/-- The name of the emitted item, as it appears in the export. -/
def EmitItem.name : EmitItem → String
  | .game g => g.name
  | .module M => M.name
  | .functor F => F.name

/-- The importer module a generated file needs: the AST for a game, and the
`SigProc` helpers as well for a module and for a functor. -/
def EmitItem.imports : EmitItem → List String
  | .game _ => ["CatCrypt.Crypto.EasyCryptImport.Ast"]
  | .module _ => ["CatCrypt.Crypto.EasyCryptImport.Json"]
  | .functor _ => ["CatCrypt.Crypto.EasyCryptImport.Json"]

/-- The printed declarations of an item. -/
def EmitItem.decls (declName : String) : EmitItem → String
  | .game g => emitGame declName g
  | .module M => emitModule declName M
  | .functor F => emitFunctor declName F

/-- The namespace a generated file declares its item in. -/
def generatedNamespace : String := "CatCrypt.Crypto.EasyCryptImport.Generated"

/-- The copyright header every file of the repository carries. -/
def copyrightHeader : String :=
  emitLines
    [ "/-",
      "Copyright (c) 2026 CatCrypt Contributors. All rights reserved.",
      "Released under MIT license as described in the file LICENSE.",
      "Authors: CatCrypt Contributors",
      "-/" ]

/-- The provenance block of a generated file: the source path, the source digest,
the schema name and version, the EasyCrypt build identity the exporter recorded,
and the trust boundary the generated literal sits behind. -/
def provenanceBlock (e : EcExport) (item : String) : String :=
  emitLines
    [ "/-!",
      "# Generated EasyCrypt import: " ++ item,
      "",
      "This file is generated from an EasyCrypt export by `emitFile`",
      "(`CatCrypt/Crypto/EasyCryptImport/Emit.lean`). Regenerate it rather than",
      "editing it.",
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
      "-/" ]

/-- A whole generated Lean module: the copyright header, the imports the item
needs, the provenance block, and the printed declarations. -/
def emitFile (e : EcExport) (declName : String) (item : EmitItem) : String :=
  copyrightHeader
    ++ String.join (item.imports.map (fun m => "import " ++ m ++ "\n"))
    ++ "\n" ++ provenanceBlock e item.name
    ++ "\nset_option autoImplicit false\n"
    ++ "\nnamespace " ++ generatedNamespace ++ "\n\n"
    ++ item.decls declName
    ++ "\nend " ++ generatedNamespace ++ "\n"

/-- Decode the item `name` of an exporter envelope and print the generated Lean
module. `kind` selects the decoder: `"game"` decodes a module whose `main`
returns a bit as an `EcGame`, `"module"` decodes a concrete `EcModule`, and
`"functor"` decodes a module of one parameter as an `EcFunctor`. Globals are
placed at location ids from `baseId` upwards. -/
def emitFromJson (T : DecodeTables) (kind name declName : String) (j : Json)
    (baseId : Nat := 0) : Except String String := do
  let e ← decodeEnvelope j
  let it ← findItem e name
  match kind with
  | "game" => .ok (emitFile e declName (.game (← decodeGame T baseId it)))
  | "module" => .ok (emitFile e declName (.module (← decodeModule T baseId it)))
  | "functor" => .ok (emitFile e declName (.functor (← decodeFunctor T baseId it)))
  | _ =>
    fail s!"unknown item kind '{kind}': the kinds are 'game', 'module' and \
      'functor'"

end CatCrypt.Crypto.EasyCryptImport

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.EasyCryptImport.EmitForm
import CatCrypt.Crypto.EasyCryptImport.FormJson
import CatCrypt.Crypto.EasyCryptImport.FunctorN

/-!
# EasyCrypt import: the `ec2lean` entry point

`main` reads an exporter envelope from a JSON file, decodes one of its items with
`emitFromJson`, and writes the generated Lean module.

## Invocation

```
lake env lean --run CatCrypt/Crypto/EasyCryptImport/EmitMain.lean \
  <export.json> <game|module|functor> <item-name> <decl-name> <out.lean>
```

A second mode surveys an envelope instead of emitting one item:

```
lake env lean --run CatCrypt/Crypto/EasyCryptImport/EmitMain.lean \
  --survey <export.json>
```

The survey checks the envelope's schema guard, then attempts to decode every
theory item and prints one line per item — `OK <kind> <name>`,
`PARAM <kind> <name> ops=<n>` or `ERR <kind> <name>: <error>` — followed by a
tally line `SURVEY <ok> ok / <param> param / <err> err`. A `Th_theory` item
prints one line per *inner* item, labelled by the inner item's full path
(`OK Th_module Top.H.Count`), then a summary line
`THEORY <name> (<mode>) <ok> ok / <param> param / <err> err`; the tally counts
the inner items and not the theory wrapper. The exit code is `0` whatever the
tally: the survey measures decoder coverage, it gates nothing.

`PARAM` is a line kind of its own because a parametric decode is weaker than a
closed one, and a reader has to see which it is: the item either declares a parameter
of the statements that read it (`Th_operator`) or is a statement conditional on
a realization of the operators it reads (`Th_axiom` with a non-empty
`EcForm.opsOf`), and `ops=<n>` is the number of `EcForm.allOp` binders the
assembled statement carries. A `PARAM` item is counted apart from the `OK`
tally.

A `Th_axiom` item of `axiom_kind: Lemma` is surveyed at the statement its theory
proves — its own statement under the imported axioms of the scopes enclosing it,
closed over the abstract operators all of them read (`decodeLemmaAt`). Its
`ops=<n>` counts the binders of that assembled statement, so an operator only a
premise reads is counted, and a lemma whose scope carries an axiom that does not
decode reports `ERR` naming that axiom rather than a goal missing a premise.

## Surveying a directory in one process

A corpus survey is one invocation rather than one per envelope:

```
lake env lean --run CatCrypt/Crypto/EasyCryptImport/EmitMain.lean \
  --survey-all <dir>
```

Every `*.json` file directly in `<dir>` is surveyed in the same process, and each
envelope's report lines — the item lines and its own `SURVEY` tally — are printed
behind the file's stem and a space, so the output is the per-file runs
concatenated with a column naming the envelope. A run ends with one aggregate
line,

```
SURVEY-ALL <files> files / <bad> envelope err / <ok> ok / <param> param / <err> err
```

whose item buckets are the sum over the envelopes that decoded. The exit code is
`0`, as it is for `--survey`.

Four decisions the mode makes:

* **The listing is sorted here.** `System.FilePath.readDir` reports directory
  entries in the order the filesystem gives them, which is neither alphabetical
  nor stable across machines, so `surveyJsonNames` sorts the `*.json` names
  ascending by `String` ordering (byte order on the underlying characters:
  uppercase before lowercase). Two runs over the same directory therefore emit
  the same lines in the same order and diff cleanly.
* **Only the directory's own entries are read**, not a recursive walk: an
  envelope corpus is a flat directory, and a recursive walk would give two files
  of one name the same prefix.
* **A file that does not open, does not parse, or fails the schema-version
  guard is reported and the batch continues.** Its line is
  `<stem> ERR envelope: <first line of the error>` and it counts in the `<bad>`
  bucket, apart from the item buckets, since a file that yields no items is not
  the same as a file whose items fail to decode. Aborting the batch would make
  one bad file cost the whole corpus the run, which is the cost this mode exists
  to remove. The error goes to standard output rather than to standard error, so
  the batch's report is one stream; `--survey` keeps writing its own to standard
  error.
* **A directory that cannot be read raises**, as an unreadable file does under
  `--survey`. That is a caller error about the argument, not a measurement.

The mode reads the corpus twice: a first pass registers the type and operator
declarations of every envelope into one set of tables, and the survey then
decodes each envelope against them. The two passes are what make a use of a
declaration meet its declaration, since a client of a theory names what it reads
and the theory's own envelope declares it.

The two spellings of a path are both reachable. An envelope roots its own
top-level items at `Top` while a client qualifies them by the theory's name, read
off the file stem (`algebra__IntDiv.ec.json` is `IntDiv`), so the first pass
carries each declaration to the qualified path a client writes
(`qualifyTopPath`), and the survey of an envelope reads the tables' entries under
its own theory at the bare paths it writes (`unqualifyTopPath`). Both are copies
appended behind what is already there, so an entry a declaration puts at a path
wins the lookup over every copy.

What is retained between envelopes is those tables and the five counters: the
parsed JSON and the report lines of one envelope are dropped at the end of its
iteration.

A third mode writes one `Th_axiom` item of an envelope as a statement — the
imported proposition and its shallow reading — instead of a program:

```
lake env lean --run CatCrypt/Crypto/EasyCryptImport/EmitMain.lean \
  --statement <export.json> <item-name> <decl-name> <out.lean> \
  --rho <text> --form <text> [--import <module>] [--open <namespace>] \
  [--proc <path>=<text>] [--procfn <path>=<text>] [--iface <name>=<text>]
```

The item is decoded against the envelope's own types, operators, modules and
module types, then closed over the operators it reads
(`EcForm.assembleParams`), and the pair `emitStatementPair` prints is wrapped in
a generated module by `emitStatementFile`. `--rho` and `--form` are required:
they name the resolution environment the statement is translated against and
the committed form the statement is the reading of, and both live in a module
the caller names through `--import`.

## The caller-supplied tables

`ShallowCtx` carries three tables of Lean text — the computation a judgement or
a probability node runs, the unapplied procedure `islossless` reads, and the
interface a module binder ranges over — and the three repeatable flags `--proc`,
`--procfn` and `--iface` fill them, each taking `<key>=<text>` split at the
first `=`. They are flags rather than a side file because the emitted `rfl` is
what checks them: text naming a definition that does not exist fails to
elaborate, and text naming the wrong computation fails the equation, so the
mechanism that carries the text needs no checking of its own. A key naming a
path the form does not read prints nothing and is reported as the printer's
error at that path.

Regenerating `Examples/OTPEquivGenerated.lean`, which `EmitCheck.lean` checks
against the emitter's current output:

```
lake env lean --run CatCrypt/Crypto/EasyCryptImport/EmitMain.lean \
  --statement CatCrypt/Crypto/EasyCryptImport/otpequiv.expected.json \
  otp_equiv otpEquivStatement \
  CatCrypt/Crypto/EasyCryptImport/Examples/OTPEquivGenerated.lean \
  --rho OTPEquivImport.otpEnv --form OTPEquivImport.otpEquivForm \
  --import CatCrypt.Crypto.EasyCryptImport.Examples.OTPEquivImport \
  --open CatCrypt.Crypto.EasyCryptBridge \
  --proc 'Top.OTP0./main=lowerClosedGame (OTPImport.otpGame false)' \
  --proc 'Top.OTP1./main=lowerClosedGame (OTPImport.otpGame true)'
```

`<out.lean>` of `-` prints to standard output. The exit code is `0` on success
and `1` on a JSON parse error, a decode error, or a bad argument list; a decode
error is written to standard error with the message the decoder produced.

The generated file declares `<decl-name>` in the namespace
`CatCrypt.Crypto.EasyCryptImport.Generated`; a module also declares
`<decl-name>Procs`, and a functor declares `<decl-name>Body` and
`<decl-name>BodyProcs`. Regenerating `Examples/OTPGenerated.lean`,
`Examples/OTPArgGenerated.lean` and `Examples/NegGenerated.lean`, which
`EmitCheck.lean` checks against the emitter's current output:

```
lake env lean --run CatCrypt/Crypto/EasyCryptImport/EmitMain.lean \
  CatCrypt/Crypto/EasyCryptImport/otp.expected.json game OTP0 otp0Game \
  CatCrypt/Crypto/EasyCryptImport/Examples/OTPGenerated.lean
lake env lean --run CatCrypt/Crypto/EasyCryptImport/EmitMain.lean \
  CatCrypt/Crypto/EasyCryptImport/otp.expected.json module OTPArg otpArgModule \
  CatCrypt/Crypto/EasyCryptImport/Examples/OTPArgGenerated.lean
lake env lean --run CatCrypt/Crypto/EasyCryptImport/EmitMain.lean \
  CatCrypt/Crypto/EasyCryptImport/functor.expected.json functor Neg negFunctor \
  CatCrypt/Crypto/EasyCryptImport/Examples/NegGenerated.lean
```

## Dispatch tables

The tables `main` decodes against are `ecPrelude`, the paths of EasyCrypt's
boolean and unit prelude. The survey additionally registers the envelope's own
abstract types (`registerThTypes`) before decoding, so an item may mention a
`type pkey.` declared alongside it. The directory mode extends them further with
the corpus's own declarations, under both path spellings. A source that uses a
finite scalar type or a further uniform distribution needs
`DecodeTables.withFinType` / `.withUniformDistr`, which no command line names:
call `emitFromJson` from Lean with the extended tables.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.EasyCryptImport

open Lean (Json)
open Hax.JsonSize

/-- The usage message. -/
def emitUsage : String :=
  emitLines
    [ "usage: ec2lean <export.json> <game|module|functor> <item-name> <decl-name> <out.lean>",
      "       <out.lean> of '-' prints to standard output",
      "       ec2lean --survey <export.json> reports whether each item decodes",
      "       ec2lean --survey-all <dir> surveys every *.json of <dir> in one process",
      "       ec2lean --statement <export.json> <item-name> <decl-name> <out.lean> \\",
      "         --rho <text> --form <text> [--import <module>] [--open <namespace>] \\",
      "         [--proc <path>=<text>] [--procfn <path>=<text>] [--iface <name>=<text>]",
      "       writes an imported statement and its shallow reading" ]

/-- The path a `Th_module` item declares and the `var` footprint its body gives:
the item's own `var` declarations, at heap location ids `0` upwards in
declaration order.

A restriction names a module for the footprint the emitted hypothesis is stated
against, and that footprint is the `var` list, which the item carries whatever
its parameter list and whatever its procedures do. This reads neither: a functor
declares a footprint as a parameter-free module does, and so does a module whose
procedures reach a construct with no image. The body's `procs` and the item's
`sig` are replaced by empty ones and the rest of the body is passed to
`decodeStructureBody`, so a footprint and the globals of a decoded structure are
the same names at the same ids.

A body that nests a module is rejected here as it is there: `glob M` of a nesting
module covers the nested state, which the `var` list alone understates, and a
footprint smaller than the source's makes the hypothesis it restricts wider. -/
def moduleGlobalsOf (T : DecodeTables) (baseId : Nat) (j : Json) :
    Except String (String × List EcGlobal) := do
  let kind ← getStr j "kind"
  if kind ≠ "Th_module" then
    fail s!"theory item of kind '{kind}': only Th_module declares module \
      variables"
  else
    let name ← getStr j "name"
    let mpath ← getStr j "path"
    let modJ ← getObj j "module"
    let bodyJ ← getObj modJ "body"
    let bodyKind ← getStr bodyJ "kind"
    if bodyKind ≠ "ME_Structure" then
      fail s!"module '{name}' has body kind '{bodyKind}': only ME_Structure \
        declares variables"
    else
      let modsA ← getArr bodyJ "modules"
      let varsA ← getArr bodyJ "vars"
      let varsOnly : Json :=
        Json.mkObj
          [("body", Json.mkObj
              [("kind", Json.str "ME_Structure"), ("modules", Json.arr modsA),
               ("vars", Json.arr varsA), ("procs", Json.arr #[])]),
           ("sig", Json.arr #[])]
      let S ← decodeStructureBody T baseId name mpath varsOnly
      .ok (S.path, S.globals)

/-- Extend statement tables with one scope's items: the procedure signatures and
globals of every item that decodes as a parameter-free module structure, the
`var` footprint of every `Th_module` item whose declarations decode
(`moduleGlobalsOf`), and the interface of every module type that decodes, each
keyed by its path. The structures' signatures also register in the dispatch
tables at their cross-paths, so a later item's result-discarding call to an
earlier module resolves. Abstract types are registered envelope-wide up front
(`registerThTypes` walks `Th_theory` items), so type paths read from
`F.tables`. New entries sit in front of `F`'s, so a theory-inner path shadows
an outer entry of the same path.

Each module is decoded at a heap location range disjoint from every other's,
starting at `F.nextLoc` and running in item order, because distinct modules hold
distinct state: a shared range would make one module's footprint another's, and
`globLocs` reads a footprint by location id alone. A module's footprint and its
entry in the global table are decoded at the same base, so the two agree. -/
def surveyExtendTables (F : FormTables) (items : List Json) : FormTables :=
  let alloc := items.foldl
    (fun (acc : Nat × List DecodedStructure × List (String × List EcGlobal)) it =>
      let (next, ss, fps) := acc
      match moduleGlobalsOf F.tables next it with
      | .ok (p, gs) =>
        let ss' := match decodeStructure F.tables next it with
                   | .ok S => S :: ss
                   | .error _ => ss
        (next + gs.length, ss', (p, gs) :: fps)
      | .error _ =>
        match decodeStructure F.tables next it with
        | .ok S => (next + S.globals.length, S :: ss, fps)
        | .error _ => acc)
    (F.nextLoc, [], [])
  let structs := alloc.2.1.reverse
  let footprints := alloc.2.2.reverse
  let T' := (structs.flatMap (·.globals)).foldl DecodeTables.withGlobal F.tables
  let T'' := (structs.flatMap procSigsOfStructure).foldl
    (fun T qs => T.withProcSig qs.1 qs.2) T'
  let modTypes := items.filterMap (fun it =>
    match getStr it "path", decodeModTypeInterface F.tables it with
    | .ok p, .ok I => some (p, I)
    | _, _ => none)
  { F with tables := T''
           procSigs := structs.flatMap procSigsOfStructure ++ F.procSigs
           modTypes := modTypes ++ F.modTypes
           modGlobals := footprints ++ F.modGlobals
           nextLoc := alloc.1 }

/-- The statement tables the survey decodes `Th_axiom` items against: the
envelope's abstract types (its `Th_type` items, theory-inner ones included,
registered first so later items resolve their paths), then its abstract operator
declarations, whose types name those paths, then the top-level modules and module
types through `surveyExtendTables`. A theory's own modules and module types extend
these at the descent into the theory, in `surveyItemLines`.

The envelope's items are also the scope a lemma's premises are read from
(`FormTables.scopeItems`): an `axiom_kind: Lemma` item is stated under the
imported axioms of the theories enclosing it, and `decodeLemmaAt` walks that
list to find them. Paths inside a theory are fully qualified, so the top-level
list is the scope of every item the descent reaches, and `surveyExtendTables`
carries it through unchanged. -/
def surveyFormTables (T : DecodeTables) (items : List Json) : FormTables :=
  let T' := registerThOperators (registerThTypes T items) items
  surveyExtendTables (formTables T' [] (scopeItems := items)) items

/-- What a decoded item is: closed, or parametric in the realization of `ops`
abstract operators. -/
inductive SurveyResult where
  /-- The item decodes without mentioning an abstract operator. -/
  | closed
  /-- The item declares or reads abstract operators, `ops` of them after
  assembly. -/
  | param (ops : Nat)
  deriving DecidableEq, Repr

/-- The operator binders an assembled statement carries at its head: one per
abstract operator the statement is quantified over (`EcForm.assembleParams`
builds them, and `EcForm.opsOf` of the result is empty, so the binders are what
counts the parameters of an assembled statement). -/
def assembledOpBinders : EcForm → Nat
  | .allOp _ _ body => assembledOpBinders body + 1
  | .allConst _ _ body => assembledOpBinders body + 1
  | _ => 0

/-- Decode one envelope item with the decoder its kind and shape select: a
`Th_module` decodes as a module, a functor or an n-ary functor by its parameter
count, a `Th_modtype` as an interface or a parameterised module type by its
`sig`'s parameter count, a `Th_type` as an abstract type, an alias or a datatype
declaration in the order `registerThTypeDecls` registers the three, a `Th_clear`
as the paths it clears, a `Th_operator` as an abstract operator declaration, and a
`Th_axiom` as a statement against `F`. A kind with no decoder is a decode error. A
`Th_type` that decodes as none of the three reports the abstract decoder's error,
which names the respect in which the declaration is not abstract. `Th_theory` is
not dispatched here: the survey descends into a theory's items through
`surveyItemLines`.

A `Th_axiom` item of `axiom_kind: Lemma` decodes through `decodeLemmaAt`, at the
statement its theory proves: its own statement under the imported axioms of its
scope, closed over the abstract operators all of them read. The `ops` a `PARAM`
line reports are therefore the assembled statement's, and a lemma whose scope
carries an axiom that does not decode is an `ERR` naming that axiom. An
`axiom_kind: Axiom` item is the hypothesis of its theory and decodes as itself. -/
def surveyDecodeItem (F : FormTables) (kind : String) (it : Json) :
    Except String SurveyResult := do
  match kind with
  | "Th_module" =>
    let modJ ← getObj it "module"
    let params ← getArr modJ "params"
    match params.size with
    | 0 => let _ ← decodeModule F.tables 0 it; .ok .closed
    | 1 => let _ ← decodeFunctor F.tables 0 it; .ok .closed
    | _ => let _ ← decodeFunctorN F.tables 0 it; .ok .closed
  | "Th_modtype" =>
    let sigJ ← getObj it "sig"
    let params ← getArr sigJ "params"
    if params.isEmpty then
      let _ ← decodeModTypeInterface F.tables it; .ok .closed
    else
      let _ ← decodeModTypeN F.tables it; .ok .closed
  | "Th_type" =>
    match decodeThType it with
    | .ok _ => .ok .closed
    | .error m =>
      match decodeThTypeAlias F.tables it with
      | .ok _ => .ok .closed
      | .error _ =>
        match decodeThTypeEnum it with
        | .ok _ => .ok .closed
        | .error _ => .error m
  | "Th_clear" =>
    let _ ← decodeThClear it
    .ok .closed
  | "Th_operator" =>
    let _ ← decodeThOperatorAbstract F.tables it
    .ok (.param 1)
  | "Th_axiom" =>
    if itemAxiomKind it == some "Lemma" then
      let f ← decodeLemmaAt F (itemPath it)
      let n := assembledOpBinders f
      if n == 0 then .ok .closed else .ok (.param n)
    else
      let f ← decodeAxiom F it
      let ops := opsUnique f.opsOf
      if ops.isEmpty then .ok .closed else .ok (.param ops.length)
  | k => fail s!"no decoder for item kind '{k}'"

/-- The survey lines and tally one envelope item contributes, labelled `label`
— the item's `name` at the top level, its full `path` inside a theory. A leaf
item contributes one line — `OK <kind> <label>`,
`PARAM <kind> <label> ops=<n>`, or `ERR <kind> <label>: <first line of the
decode error>` — and tallies one item, in the `ok`, the `param` or neither
bucket. A `Th_theory` item contributes one line per inner item, each labelled by
its full path and decoded against the tables extended with the theory's own
modules and module types, then a summary line
`THEORY <label> (<mode>) <ok> ok / <param> param / <err> err`; its tally is the
inner items', theory-inner theories included, and the theory wrapper itself
counts nothing. An abstract theory's items are quantified over the theory's
declared parameters, which the export does not realise, so an inner item that
mentions such a name reports that name's own decode error rather than a
theory-level one.

The tally is `(ok, param, total)`; the error count is `total - ok - param`. -/
def surveyItemLines (F : FormTables) (label kind : String) (it : Json) :
    List String × Nat × Nat × Nat :=
  if kind = "Th_theory" then
    match _hitems : getArr it "items" with
    | .error m => ([s!"ERR Th_theory {label}: {(m.splitOn "\n").headD m}"], 0, 0, 1)
    | .ok arr =>
      let F' := surveyExtendTables F arr.toList
      let reports := arr.toList.attach.map (fun ⟨x, _⟩ =>
        let k := (getStr x "kind").toOption.getD "?"
        let l := (getStr x "path").toOption.getD
          ((getStr x "name").toOption.getD "?")
        surveyItemLines F' l k x)
      let ok := (reports.map (·.2.1)).sum
      let par := (reports.map (·.2.2.1)).sum
      let tot := (reports.map (·.2.2.2)).sum
      let mode := (getStr it "mode").toOption.getD "?"
      ((reports.map (·.1)).flatten ++
        [s!"THEORY {label} ({mode}) {ok} ok / {par} param / {tot - ok - par} err"],
        ok, par, tot)
  else
    match surveyDecodeItem F kind it with
    | .ok .closed => ([s!"OK {kind} {label}"], 1, 0, 1)
    | .ok (.param n) => ([s!"PARAM {kind} {label} ops={n}"], 0, 1, 1)
    | .error m => ([s!"ERR {kind} {label}: {(m.splitOn "\n").headD m}"], 0, 0, 1)
termination_by jsonSize it
decreasing_by
  exact getArr_decreases _hitems (Array.mem_toList_iff.mp ‹_ ∈ Array.toList _›)

/-- The exporter envelope a file's text holds, with `inPath` naming the source in
a JSON parse error. The schema name and version are checked by
`decodeEnvelope`. -/
def surveyEnvelopeOf (inPath text : String) : Except String EcExport := do
  let j ← (Json.parse text).mapError (fun m => s!"{inPath}: {m}")
  decodeEnvelope j

/-- The tally line a survey of one envelope ends with. The error bucket is the
leaf items that are neither `ok` nor `param`. -/
def surveyTallyLine (ok par tot : Nat) : String :=
  s!"SURVEY {ok} ok / {par} param / {tot - ok - par} err"

/-- The report lines of one envelope, each behind `pfx`. The empty prefix leaves
them as they are. -/
def surveyPrefixed (pfx : String) (lines : List String) : List String :=
  lines.map (pfx ++ ·)

/-- Print an envelope's report lines, each behind `pfx`, and return its
`(ok, param, total)` tally over leaf items. Each item's lines are printed and
dropped before the next item decodes. -/
def surveyPrintEnvelope (T : DecodeTables) (pfx : String) (e : EcExport) :
    IO (Nat × Nat × Nat) := do
  let F := surveyFormTables T e.items
  let mut nOk := 0
  let mut nPar := 0
  let mut nTot := 0
  for it in e.items do
    let kind := (getStr it "kind").toOption.getD "?"
    let name := (getStr it "name").toOption.getD "?"
    let (lines, ok, par, tot) := surveyItemLines F name kind it
    for l in surveyPrefixed pfx lines do
      IO.println l
    nOk := nOk + ok
    nPar := nPar + par
    nTot := nTot + tot
  return (nOk, nPar, nTot)

/-- Read an exporter envelope and print, one line per theory item, what the item
decodes to — `OK <kind> <name>`, `PARAM <kind> <name> ops=<n>` or
`ERR <kind> <name>: <first line of the decode error>`, with a `Th_theory` item
reported through `surveyItemLines` as one line per inner item and a `THEORY`
summary — then the tally line
`SURVEY <ok> ok / <param> param / <err> err`, whose buckets count leaf items (a
theory's inner items, not the theory wrapper). Returns `0` whatever the tally; an
envelope that does not parse or fails the schema guard reports the error on
standard error and tallies an empty survey. -/
def surveyMain (inPath : String) : IO UInt32 := do
  let text ← IO.FS.readFile inPath
  match surveyEnvelopeOf inPath text with
  | .error m =>
    IO.eprintln s!"ec2lean: {m}"
    IO.println (surveyTallyLine 0 0 0)
    return 0
  | .ok e =>
    let (nOk, nPar, nTot) ← surveyPrintEnvelope ecPrelude "" e
    IO.println (surveyTallyLine nOk nPar nTot)
    return 0

/-! ## The directory mode -/

/-- The `*.json` entries of a directory listing, ascending by name. The listing
`System.FilePath.readDir` returns is in the filesystem's own order, so the sort
is what makes two runs over one directory comparable line for line. -/
def surveyJsonNames (names : List String) : List String :=
  (names.filter (·.endsWith ".json")).mergeSort (fun a b => a ≤ b)

/-- The column an envelope's report lines carry in the directory mode: the file
name without its final extension, then a space. -/
def surveyFilePrefix (fileName : String) : String :=
  ((fileName : System.FilePath).fileStem.getD fileName) ++ " "

/-- The aggregate line a directory survey ends with: the files read, the files
that yielded no envelope, and the item buckets summed over the envelopes that
decoded. -/
def surveyAllTallyLine (files bad ok par tot : Nat) : String :=
  s!"SURVEY-ALL {files} files / {bad} envelope err / {ok} ok / {par} param / \
    {tot - ok - par} err"

/-- The text of a file, with an IO failure reported as a message rather than
raised. -/
def readFileOrError (p : System.FilePath) : IO (Except String String) := do
  try
    let text ← IO.FS.readFile p
    return .ok text
  catch e =>
    return .error (toString e)

/-- Whether a corpus file name is one of EasyCrypt's prelude theories, which the
exporter writes with the `prelude__` stem the directory it read them from gives.

Every theory is elaborated with the prelude in scope, so a use of one of its
paths can appear in any envelope while the declaration appears only in the
prelude's own. Registering these first is what makes the two meet. -/
def isPreludeEnvelope (name : String) : Bool := name.startsWith "prelude__"

/-- The theory an envelope's own top-level items belong to, read off the file
name: the stem between the directory prefix and the first extension, so
`prelude__Logic.ec.json` is `Logic`. -/
def envelopeTheoryName (name : String) : String :=
  let stem := (name.splitOn "__").getLastD name
  (stem.splitOn ".").headD stem

/-- The path a top-level item of the theory `th` carries outside its own
envelope: `th` inserted behind `Top.`. An envelope roots the items it declares
itself at `Top`, while every client writes them under the theory's name, so
`Top.associative` of `Logic.ec` is `Top.Logic.associative` everywhere it is read,
and the inner-theory item `Top.IterOp.iterop` of `Int.ec` is
`Top.Int.IterOp.iterop`. A path outside `Top`, and `Top.` with nothing behind it,
have no such reading. -/
def qualifyTopPath (th : String) (p : String) : Option String :=
  if p.startsWith "Top." then
    let rest := p.drop 4
    if rest.isEmpty then none else some ("Top." ++ th ++ "." ++ rest)
  else none

/-- The path a client's spelling of an item of the theory `th` carries inside
`th`'s own envelope: `th` dropped from behind `Top.`, so the ingestion's entry
`Top.IntDiv.edivz` is `Top.edivz` where `IntDiv.ec` declares it. A path under
another theory, and `Top.<th>.` with nothing behind it, have no such reading. -/
def unqualifyTopPath (th : String) (p : String) : Option String :=
  let pfx := "Top." ++ th ++ "."
  if p.startsWith pfx then
    let rest := p.drop pfx.length
    if rest.isEmpty then none else some ("Top." ++ rest)
  else none

/-- The entries `new` holds and `old` did not. Registration extends a table in
front, so the added entries are its leading segment. -/
def entriesAdded {α : Type} (old new : List (String × α)) : List (String × α) :=
  new.take (new.length - old.length)

/-- The entries of `es` keyed again by the path the theory `th` gives them
outside its own envelope. An entry whose path has no such reading is dropped. -/
def theoryQualifiedCopies {α : Type} (th : String) (es : List (String × α)) :
    List (String × α) :=
  es.filterMap (fun e => (qualifyTopPath th e.1).map (fun q => (q, e.2)))

/-- The entries of `es` keyed again by the path the theory `th` writes for them
inside its own envelope. An entry under another theory is dropped. -/
def theoryLocalCopies {α : Type} (th : String) (es : List (String × α)) :
    List (String × α) :=
  es.filterMap (fun e => (unqualifyTopPath th e.1).map (fun q => (q, e.2)))

/-- The paths of `ps` written as the theory `th` writes them inside its own
envelope. A path under another theory is dropped. -/
def theoryLocalPaths (th : String) (ps : List String) : List String :=
  ps.filterMap (unqualifyTopPath th)

/-- The table `new`, followed by the entries it holds and `old` did not, keyed
again by their theory-qualified paths.

The copies are appended rather than prepended, and only the entries this
envelope added are copied: `List.lookup` takes the first match, so an entry a
declaration puts at a qualified path stays ahead of every alias. -/
def aliasAddedEntries {α : Type} (th : String) (old new : List (String × α)) :
    List (String × α) :=
  new ++ theoryQualifiedCopies th (entriesAdded old new)

/-- The table `old`, followed by the entries `new` holds and it did not, keyed by
their theory-qualified paths alone.

A theory outside the prelude is read under its name, so the bare paths its own
envelope writes are dropped here and only the qualified copies cross to the
corpus's other envelopes. The copies are appended, as they are in
`aliasAddedEntries`. -/
def qualifyAddedEntries {α : Type} (th : String) (old new : List (String × α)) :
    List (String × α) :=
  old ++ theoryQualifiedCopies th (entriesAdded old new)

/-- The tables `T'` an envelope's registration produced from `T`, with the
declaration entries it added keyed again by their theory-qualified paths. The
bare paths stay, which is what a prelude theory's declarations are read at
wherever they are in scope. -/
def aliasEnvelopeTheory (th : String) (T T' : DecodeTables) : DecodeTables :=
  { T' with
    tyPaths := aliasAddedEntries th T.tyPaths T'.tyPaths
    constPaths := aliasAddedEntries th T.constPaths T'.constPaths
    absOpPaths := aliasAddedEntries th T.absOpPaths T'.absOpPaths
    defOpPaths := aliasAddedEntries th T.defOpPaths T'.defOpPaths
    polyOpPaths := aliasAddedEntries th T.polyOpPaths T'.polyOpPaths }

/-- The tables `T`, with the declaration entries an envelope's registration added
to it keyed by their theory-qualified paths alone: what one envelope's items
declare is reachable in another envelope at the path that one writes, and the
bare paths of the declaring envelope do not cross. -/
def qualifyEnvelopeTheory (th : String) (T T' : DecodeTables) : DecodeTables :=
  { T with
    tyPaths := qualifyAddedEntries th T.tyPaths T'.tyPaths
    constPaths := qualifyAddedEntries th T.constPaths T'.constPaths
    absOpPaths := qualifyAddedEntries th T.absOpPaths T'.absOpPaths
    defOpPaths := qualifyAddedEntries th T.defOpPaths T'.defOpPaths
    polyOpPaths := qualifyAddedEntries th T.polyOpPaths T'.polyOpPaths }

/-- The tables an envelope of the theory `th` is surveyed against: `T`, followed
by every entry of `T` under `th` keyed again by the path `th`'s own envelope
writes for it. An envelope roots its own items at `Top`, so the entry a client
reads as `Top.IntDiv.edivz` is read as `Top.edivz` inside `IntDiv.ec`, and the
copy is what makes the ingestion's entry meet that spelling.

The copies are appended, so an entry the tables already hold at a bare path wins
the lookup. -/
def unqualifyEnvelopeTheory (th : String) (T : DecodeTables) : DecodeTables :=
  { T with
    tyPaths := T.tyPaths ++ theoryLocalCopies th T.tyPaths
    mapTyPaths := T.mapTyPaths ++ theoryLocalPaths th T.mapTyPaths
    optionTyPaths := T.optionTyPaths ++ theoryLocalPaths th T.optionTyPaths
    listTyPaths := T.listTyPaths ++ theoryLocalPaths th T.listTyPaths
    fsetTyPaths := T.fsetTyPaths ++ theoryLocalPaths th T.fsetTyPaths
    constPaths := T.constPaths ++ theoryLocalCopies th T.constPaths
    emptyMapPaths := T.emptyMapPaths ++ theoryLocalPaths th T.emptyMapPaths
    emptyFsetPaths := T.emptyFsetPaths ++ theoryLocalPaths th T.emptyFsetPaths
    emptyListPaths := T.emptyListPaths ++ theoryLocalPaths th T.emptyListPaths
    nonePaths := T.nonePaths ++ theoryLocalPaths th T.nonePaths
    witnessPaths := T.witnessPaths ++ theoryLocalPaths th T.witnessPaths
    opPaths := T.opPaths ++ theoryLocalCopies th T.opPaths
    distrPaths := T.distrPaths ++ theoryLocalPaths th T.distrPaths
    distrOpPaths := T.distrOpPaths ++ theoryLocalCopies th T.distrOpPaths
    distrTyPaths := T.distrTyPaths ++ theoryLocalPaths th T.distrTyPaths
    absOpPaths := T.absOpPaths ++ theoryLocalCopies th T.absOpPaths
    defOpPaths := T.defOpPaths ++ theoryLocalCopies th T.defOpPaths
    polyOpPaths := T.polyOpPaths ++ theoryLocalCopies th T.polyOpPaths }

-- The theory name is the stem between the directory prefix and the first
-- extension.
#guard envelopeTheoryName "prelude__Logic.ec.json" == "Logic"
#guard envelopeTheoryName "algebra__Bigalg.ec.json" == "Bigalg"

-- A top-level item takes the theory's name, whatever the path behind `Top.`
-- holds: an item of a theory nested in the file's own is qualified by the file's
-- theory as a single-segment one is. A path outside `Top`, and `Top.` with
-- nothing behind it, take nothing.
#guard qualifyTopPath "Logic" "Top.associative" == some "Top.Logic.associative"
#guard qualifyTopPath "Int" "Top.IterOp.iterop" == some "Top.Int.IterOp.iterop"
#guard qualifyTopPath "Logic" "Other.x" == none
#guard qualifyTopPath "Logic" "Top." == none

-- The client's spelling reads back to the one the declaring envelope writes,
-- whatever follows the theory's name. A path under another theory, and the
-- theory's own name with nothing behind it, read back to nothing.
#guard unqualifyTopPath "IntDiv" "Top.IntDiv.edivz" == some "Top.edivz"
#guard unqualifyTopPath "Int" "Top.Int.IterOp.iterop" == some "Top.IterOp.iterop"
#guard unqualifyTopPath "IntDiv" "Top.CoreInt.add" == none
#guard unqualifyTopPath "IntDiv" "Top.IntDiv." == none

-- The two directions invert each other on the paths that have both readings.
#guard ((qualifyTopPath "Int" "Top.IterOp.iterop").bind (unqualifyTopPath "Int"))
  == some "Top.IterOp.iterop"
#guard ((unqualifyTopPath "IntDiv" "Top.IntDiv.edivz").bind
  (qualifyTopPath "IntDiv")) == some "Top.IntDiv.edivz"

-- Only the entries this envelope added are copied, and the copies go behind
-- what is already there.
#guard aliasAddedEntries "Logic" [("Top.old", 1)] [("Top.new", 2), ("Top.old", 1)]
  == [("Top.new", 2), ("Top.old", 1), ("Top.Logic.new", 2)]

-- The qualified-only form carries the same copies behind the table it started
-- from, and the envelope's own bare paths do not cross.
#guard qualifyAddedEntries "IntDiv" [("Top.old", 1)]
    [("Top.new", 2), ("Top.old", 1)]
  == [("Top.old", 1), ("Top.IntDiv.new", 2)]

-- An entry a declaration puts at a qualified path is ahead of every alias, so
-- it wins the lookup.
#guard (List.lookup "Top.Logic.new"
  (aliasAddedEntries "Logic" [("Top.old", 1)]
    [("Top.Logic.new", 3), ("Top.new", 2), ("Top.old", 1)])) == some 3

-- The copies of the reverse direction also go behind what is already there, so
-- an entry at a bare path wins over the copy of an entry under the theory.
#guard theoryLocalCopies "IntDiv" [("Top.IntDiv.edivz", 1), ("Top.CoreInt.add", 2)]
  == [("Top.edivz", 1)]

#guard (List.lookup "Top.edivz"
  ([("Top.edivz", 3)] ++ theoryLocalCopies "IntDiv" [("Top.IntDiv.edivz", 1)]))
  == some 3

-- The ingestion's own entry for EasyCrypt's Euclidean division is keyed at the
-- path a client of `IntDiv.ec` writes, and inside that envelope it is reached at
-- the bare path the envelope writes.
#guard (List.lookup "Top.IntDiv.edivz" ecPrelude.opPaths).isSome
#guard (List.lookup "Top.edivz" ecPrelude.opPaths).isNone
#guard (List.lookup "Top.edivz"
  (unqualifyEnvelopeTheory "IntDiv" ecPrelude).opPaths).isSome
#guard (List.lookup "Top.IntDiv.edivz"
  (unqualifyEnvelopeTheory "IntDiv" ecPrelude).opPaths).isSome

-- A theory the tables hold nothing under leaves them as they are.
#guard (unqualifyEnvelopeTheory "Absent" ecPrelude).opPaths == ecPrelude.opPaths

-- The string-keyed tables read the same way: EasyCrypt's finite maps are
-- declared in `FMap.ec`, whose own envelope writes the type at `Top.fmap`.
#guard (unqualifyEnvelopeTheory "FMap" ecPrelude).mapTyPaths
  == ["Top.FMap.fmap", "Top.fmap"]

-- A prelude envelope's declaration crosses to the corpus's tables at both
-- spellings, the bare one in front and the qualified copy behind.
#guard ((aliasEnvelopeTheory "Logic" ecPrelude
    (ecPrelude.withOpaqueType "Top.zz")).tyPaths.map Prod.fst)
  == (["Top.zz"] ++ ecPrelude.tyPaths.map Prod.fst ++ ["Top.Logic.zz"])

-- Every other envelope's declaration crosses at the qualified spelling alone.
#guard ((qualifyEnvelopeTheory "IntDiv" ecPrelude
    (ecPrelude.withOpaqueType "Top.zz")).tyPaths.map Prod.fst)
  == (ecPrelude.tyPaths.map Prod.fst ++ ["Top.IntDiv.zz"])

/-- The envelope the file `name` of `dir` holds, with an unreadable file, a JSON
parse error and a failed schema guard alike reported as a message. -/
def readEnvelopeOf (dir name : String) : IO (Except String EcExport) := do
  let p := (dir : System.FilePath) / (name : System.FilePath)
  let contents ← readFileOrError p
  return contents.bind (surveyEnvelopeOf p.toString)

/-- The tables every envelope of `dir` is surveyed against: the ingestion's own
prelude, extended with the type and operator declarations of the corpus's prelude
theories — each of those also under the path its theory's name gives it — and
then with the declarations of every other envelope under their theory-qualified
paths alone. An envelope that does not read is skipped, leaving the tables it
would have extended.

The prelude theories are registered in a pass of their own, before the rest, for
two reasons: their declarations are in scope in every other envelope, so their
bare paths belong to the shared tables, and a later envelope's declaration whose
type mentions one of them decodes only once they are there. -/
def surveyCorpusTables (dir : String) (names : List String) :
    IO DecodeTables := do
  let mut T := ecPrelude
  for n in names do
    if isPreludeEnvelope n then
      match ← readEnvelopeOf dir n with
      | .error _ => pure ()
      | .ok e =>
        T := aliasEnvelopeTheory (envelopeTheoryName n) T
          (registerThOperators (registerThTypes T e.items) e.items)
  for n in names do
    if !isPreludeEnvelope n then
      match ← readEnvelopeOf dir n with
      | .error _ => pure ()
      | .ok e =>
        T := qualifyEnvelopeTheory (envelopeTheoryName n) T
          (registerThOperators (registerThTypes T e.items) e.items)
  return T

/-- Survey every `*.json` file of `dir` in this process, in ascending name order,
printing each envelope's report lines and its `SURVEY` tally behind the file's
stem, then the aggregate `SURVEY-ALL` line. Every envelope is surveyed against
the corpus's own declarations as well as the ingestion's tables
(`surveyCorpusTables`), and against those tables read at the path spellings its
own theory writes (`unqualifyEnvelopeTheory`). A file that does not open, does
not parse, or fails the schema guard prints `<stem> ERR envelope: <first line of
the error>` and counts in the aggregate's `envelope err` bucket, and the
remaining files are still surveyed. Returns `0` whatever the tally. A directory
that cannot be read raises, as an unreadable file does under `--survey`. -/
def surveyAllMain (dir : String) : IO UInt32 := do
  let entries ← System.FilePath.readDir dir
  let names := surveyJsonNames (entries.toList.map (·.fileName))
  let T ← surveyCorpusTables dir names
  let mut nFiles := 0
  let mut nBad := 0
  let mut nOk := 0
  let mut nPar := 0
  let mut nTot := 0
  for n in names do
    nFiles := nFiles + 1
    let pfx := surveyFilePrefix n
    match ← readEnvelopeOf dir n with
    | .error m =>
      nBad := nBad + 1
      IO.println s!"{pfx}ERR envelope: {(m.splitOn "\n").headD m}"
    | .ok e =>
      let (ok, par, tot) ←
        surveyPrintEnvelope (unqualifyEnvelopeTheory (envelopeTheoryName n) T)
          pfx e
      IO.println (pfx ++ surveyTallyLine ok par tot)
      nOk := nOk + ok
      nPar := nPar + par
      nTot := nTot + tot
  IO.println (surveyAllTallyLine nFiles nBad nOk nPar nTot)
  return 0

/-! ## The statement mode -/

/-- What the `--statement` flags name: the resolution environment and the
committed form the generated declarations refer to, the imports and opens the
generated module carries, and the three caller-supplied `ShallowCtx` tables. -/
structure StatementOptions where
  /-- The text of the `ProcEnv` the statement is translated against. -/
  rho : String := ""
  /-- The text of the committed form the statement is the reading of. -/
  form : String := ""
  /-- The modules the generated file imports, in the order given. -/
  imports : List String := []
  /-- The namespaces the generated file opens, in the order given. -/
  opens : List String := []
  /-- `ShallowCtx.procNames`: the computation each judgement or probability node
  runs. -/
  procNames : List (String × String) := []
  /-- `ShallowCtx.procFnNames`: each procedure itself, unapplied. -/
  procFnNames : List (String × String) := []
  /-- `ShallowCtx.interfaces`: the interface each module binder ranges over. -/
  interfaces : List (String × String) := []

/-- The `ShallowCtx` the three binding tables make. -/
def StatementOptions.toShallowCtx (o : StatementOptions) : ShallowCtx where
  procNames := o.procNames
  procFnNames := o.procFnNames
  interfaces := o.interfaces

/-- Split a `<key>=<text>` flag argument at its first `=`. The text may carry
further `=` characters, which a printed equation does. -/
def splitBinding (flag s : String) : Except String (String × String) :=
  match s.splitOn "=" with
  | k :: v :: rest => .ok (k, String.intercalate "=" (v :: rest))
  | _ =>
    fail s!"'{flag} {s}': the argument is <key>=<text>, split at the first '='"

/-- Read the flags of the `--statement` mode. -/
def parseStatementFlags : List String → StatementOptions →
    Except String StatementOptions
  | [], o => .ok o
  | "--rho" :: t :: rest, o => parseStatementFlags rest { o with rho := t }
  | "--form" :: t :: rest, o => parseStatementFlags rest { o with form := t }
  | "--import" :: t :: rest, o =>
    parseStatementFlags rest { o with imports := o.imports ++ [t] }
  | "--open" :: t :: rest, o =>
    parseStatementFlags rest { o with opens := o.opens ++ [t] }
  | "--proc" :: t :: rest, o => do
    let b ← splitBinding "--proc" t
    parseStatementFlags rest { o with procNames := o.procNames ++ [b] }
  | "--procfn" :: t :: rest, o => do
    let b ← splitBinding "--procfn" t
    parseStatementFlags rest { o with procFnNames := o.procFnNames ++ [b] }
  | "--iface" :: t :: rest, o => do
    let b ← splitBinding "--iface" t
    parseStatementFlags rest { o with interfaces := o.interfaces ++ [b] }
  | [a], _ => fail s!"the flag '{a}' takes a value"
  | a :: _, _ =>
    fail s!"'{a}' is not a --statement flag: the flags are --rho, --form, \
      --import, --open, --proc, --procfn and --iface"

/-- Decode the `Th_axiom` item `name` of an exporter envelope and print the
generated Lean module holding the imported statement and its shallow reading.
The item is decoded against the envelope's own types, operators, modules and
module types, then closed over the operators it reads. -/
def emitStatementFromJson (T : DecodeTables) (name declName : String)
    (o : StatementOptions) (j : Json) : Except String String := do
  if o.rho.isEmpty then
    fail "--statement takes --rho <text>: the resolution environment the \
      statement is translated against is the caller's"
  else if o.form.isEmpty then
    fail "--statement takes --form <text>: the generated statement is the \
      reading of a committed form, which the caller names"
  else
    let e ← decodeEnvelope j
    let it ← findItem e name
    let f ← decodeAxiom (surveyFormTables T e.items) it
    emitStatementFile e name declName o.rho o.form o.imports o.opens
      f.assembleParams o.toShallowCtx

/-- Read an exporter envelope, decode the named statement, and write the
generated Lean module. -/
def statementMain (inPath item declName outPath : String) (flags : List String) :
    IO UInt32 := do
  let text ← IO.FS.readFile inPath
  match Json.parse text with
  | .error m =>
    IO.eprintln s!"ec2lean: {inPath}: {m}"
    return 1
  | .ok j =>
    match parseStatementFlags flags {} with
    | .error m =>
      IO.eprintln s!"ec2lean: {m}"
      return 1
    | .ok o =>
      match emitStatementFromJson ecPrelude item declName o j with
      | .error m =>
        IO.eprintln s!"ec2lean: {m}"
        return 1
      | .ok out =>
        if outPath == "-" then IO.print out else IO.FS.writeFile outPath out
        return 0

/-- Read an exporter envelope, decode the named item, and write the generated Lean
module. -/
def emitMain (args : List String) : IO UInt32 := do
  match args with
  | ["--survey", inPath] => surveyMain inPath
  | ["--survey-all", dir] => surveyAllMain dir
  | "--statement" :: inPath :: item :: declName :: outPath :: flags =>
    statementMain inPath item declName outPath flags
  | [inPath, kind, item, declName, outPath] =>
    let text ← IO.FS.readFile inPath
    match Json.parse text with
    | .error m =>
      IO.eprintln s!"ec2lean: {inPath}: {m}"
      return 1
    | .ok j =>
      match emitFromJson ecPrelude kind item declName j with
      | .error m =>
        IO.eprintln s!"ec2lean: {m}"
        return 1
      | .ok out =>
        if outPath == "-" then IO.print out else IO.FS.writeFile outPath out
        return 0
  | _ =>
    IO.eprint emitUsage
    return 1

/-! ## Golden tests

The checks below run the survey's theory arm on a synthetic `Th_theory`
envelope item — an inner abstract type and an inner module whose `var` is
declared at it — and match the report lines and tally. They are `#guard`
commands, since the decoders are well-founded recursive and have no
kernel-reducible equations (`AGENTS.md` states why). -/

section SurveyGolden

/-- A `Th_type` item declaring the abstract type `Top.T.t` inside a theory, at
the fully qualified path the exporter writes for it. -/
private def jSurveyThType : Json :=
  Json.mkObj [("kind", Json.str "Th_type"), ("name", Json.str "t"),
              ("path", Json.str "Top.T.t"),
              ("decl", Json.mkObj
                [("params", Json.arr #[]),
                 ("body", Json.mkObj [("kind", Json.str "Abstract")]),
                 ("subtype", Json.null)])]

/-- A `Th_module` item inside the same theory: a module with one `var` at the
theory's abstract type and no procedures. -/
private def jSurveyModule : Json :=
  Json.mkObj
    [("kind", Json.str "Th_module"), ("name", Json.str "M"),
     ("path", Json.str "Top.T.M"),
     ("module", Json.mkObj
       [("name", Json.str "M"), ("params", Json.arr #[]),
        ("body", Json.mkObj
          [("kind", Json.str "ME_Structure"), ("modules", Json.arr #[]),
           ("vars", Json.arr
             #[Json.mkObj [("name", Json.str "g"),
                           ("ty", Json.mkObj
                             [("kind", Json.str "Tconstr"),
                              ("path", Json.str "Top.T.t"),
                              ("args", Json.arr #[])])]]),
           ("procs", Json.arr #[])]),
        ("sig", Json.arr #[])])]

/-- A `Th_theory` item holding the two, at the exporter's envelope shape for a
named theory. -/
private def jSurveyTheory : Json :=
  Json.mkObj [("kind", Json.str "Th_theory"), ("name", Json.str "T"),
              ("path", Json.str "Top.T"), ("mode", Json.str "abstract"),
              ("source", Json.null),
              ("items", Json.arr #[jSurveyThType, jSurveyModule])]

-- The theory arm reports one line per inner item at its full path, then the
-- summary, and tallies the inner items: the module's `var` resolves against
-- the theory's own abstract type.
#guard surveyItemLines (surveyFormTables ecPrelude [jSurveyTheory]) "T"
    "Th_theory" jSurveyTheory
  == (["OK Th_type Top.T.t", "OK Th_module Top.T.M",
       "THEORY T (abstract) 2 ok / 0 param / 0 err"], 2, 0, 2)

-- Theories nest: the inner theory reports under its full path with its own
-- mode, and the outer tally is the inner one.
#guard surveyItemLines
    (surveyFormTables ecPrelude
      [Json.mkObj [("kind", Json.str "Th_theory"), ("name", Json.str "O"),
                   ("path", Json.str "Top.O"), ("mode", Json.str "concrete"),
                   ("source", Json.null),
                   ("items", Json.arr #[jSurveyTheory])]])
    "O" "Th_theory"
    (Json.mkObj [("kind", Json.str "Th_theory"), ("name", Json.str "O"),
                 ("path", Json.str "Top.O"), ("mode", Json.str "concrete"),
                 ("source", Json.null),
                 ("items", Json.arr #[jSurveyTheory])])
  == (["OK Th_type Top.T.t", "OK Th_module Top.T.M",
       "THEORY Top.T (abstract) 2 ok / 0 param / 0 err",
       "THEORY O (concrete) 2 ok / 0 param / 0 err"], 2, 0, 2)

-- A theory item without an `items` array reports one error line and tallies
-- one undecoded item.
#guard (match surveyItemLines (formTables ecPrelude []) "B" "Th_theory"
            (Json.mkObj [("kind", Json.str "Th_theory"),
                         ("name", Json.str "B")]) with
        | ([l], 0, 0, 1) => l.startsWith "ERR Th_theory B:"
        | _ => false)

/-! ### The parametric line

A theory declaring an abstract distribution and asserting it lossless — the shape
of `crypto/PRF.eca`'s `PseudoRF` — reports the declaration and the statement over
it as `PARAM`, and the carrier as `OK`. -/

/-- The type node of `Top.P.t`. -/
private def jSurveyTyT : Json :=
  Json.mkObj [("kind", Json.str "Tconstr"), ("path", Json.str "Top.P.t"),
              ("args", Json.arr #[])]

/-- The type node of `t distr`. -/
private def jSurveyTyDistrT : Json :=
  Json.mkObj [("kind", Json.str "Tconstr"),
              ("path", Json.str "Top.Distr.distr"),
              ("args", Json.arr #[jSurveyTyT])]

/-- The `bool` type node. -/
private def jSurveyTyBool : Json :=
  Json.mkObj [("kind", Json.str "Tconstr"),
              ("path", Json.str "Top.Pervasive.bool"), ("args", Json.arr #[])]

/-- A theory declaring `type t.`, `op d : t distr.` and
`axiom d_ll : is_lossless d.` -/
private def jSurveyParamTheory : Json :=
  Json.mkObj
    [("kind", Json.str "Th_theory"), ("name", Json.str "P"),
     ("path", Json.str "Top.P"), ("mode", Json.str "abstract"),
     ("source", Json.null),
     ("items", Json.arr
       #[Json.mkObj
           [("kind", Json.str "Th_type"), ("name", Json.str "t"),
            ("path", Json.str "Top.P.t"),
            ("decl", Json.mkObj
              [("params", Json.arr #[]),
               ("body", Json.mkObj [("kind", Json.str "Abstract")]),
               ("subtype", Json.null)])],
         Json.mkObj
           [("kind", Json.str "Th_operator"), ("name", Json.str "d"),
            ("path", Json.str "Top.P.d"),
            ("decl", Json.mkObj
              [("tparams", Json.arr #[]), ("ty", jSurveyTyDistrT),
               ("body", Json.mkObj [("kind", Json.str "Abstract")])])],
         Json.mkObj
           [("kind", Json.str "Th_axiom"), ("name", Json.str "d_ll"),
            ("path", Json.str "Top.P.d_ll"),
            ("decl", Json.mkObj
              [("tparams", Json.arr #[]), ("axiom_kind", Json.str "Axiom"),
               ("spec", Json.mkObj
                 [("ty", jSurveyTyBool), ("kind", Json.str "Fapp"),
                  ("f", Json.mkObj
                    [("ty", Json.mkObj
                       [("kind", Json.str "Tfun"), ("dom", jSurveyTyDistrT),
                        ("cod", jSurveyTyBool)]),
                     ("kind", Json.str "Fop"),
                     ("path", Json.str "Top.Distr.is_lossless"),
                     ("targs", Json.arr #[jSurveyTyT])]),
                  ("args", Json.arr
                    #[Json.mkObj
                        [("ty", jSurveyTyDistrT), ("kind", Json.str "Fop"),
                         ("path", Json.str "Top.P.d"),
                         ("targs", Json.arr #[])]])])])]])]

#guard surveyItemLines (surveyFormTables ecPrelude [jSurveyParamTheory]) "P"
    "Th_theory" jSurveyParamTheory
  == (["OK Th_type Top.P.t", "PARAM Th_operator Top.P.d ops=1",
       "PARAM Th_axiom Top.P.d_ll ops=1",
       "THEORY P (abstract) 1 ok / 2 param / 0 err"], 1, 2, 3)

/-! ### The lemma line

A theory declaring an abstract distribution and asserting it lossless, holding an
inner theory whose lemma is the losslessness of a further abstract distribution —
the shape of `crypto/DigitalSignaturesROM.eca`, where the clone
`Top.StatelessROM.UUFKOAROM.UUFKOA` holds the lemma `dmsg_ll` and the axiom it is
proved from is declared one scope out. The nodes below are that export's
spellings: the declared type of `dmsg` is at `Top.Pervasive.distr`, EasyCrypt's
declaration of `'a distr`. -/

/-- The type node of `t distr` at EasyCrypt's declaration of the type. -/
private def jSurveyTyDistrDeclT : Json :=
  Json.mkObj [("kind", Json.str "Tconstr"),
              ("path", Json.str "Top.Pervasive.distr"),
              ("args", Json.arr #[jSurveyTyT])]

/-- The statement `is_lossless d` for the distribution operator declared at
`opPath`. -/
private def jSurveyLosslessSpec (opPath : String) : Json :=
  Json.mkObj
    [("ty", jSurveyTyBool), ("kind", Json.str "Fapp"),
     ("f", Json.mkObj
       [("ty", Json.mkObj
          [("kind", Json.str "Tfun"), ("dom", jSurveyTyDistrDeclT),
           ("cod", jSurveyTyBool)]),
        ("kind", Json.str "Fop"),
        ("path", Json.str "Top.Distr.is_lossless"),
        ("targs", Json.arr #[jSurveyTyT])]),
     ("args", Json.arr
       #[Json.mkObj
           [("ty", jSurveyTyDistrDeclT), ("kind", Json.str "Fop"),
            ("path", Json.str opPath), ("targs", Json.arr #[])]])]

/-- A `Th_operator` item declaring an abstract distribution on `t`. -/
private def jSurveyAbsDistrOp (name path : String) : Json :=
  Json.mkObj
    [("kind", Json.str "Th_operator"), ("name", Json.str name),
     ("path", Json.str path),
     ("decl", Json.mkObj
       [("tparams", Json.arr #[]), ("ty", jSurveyTyDistrDeclT),
        ("body", Json.mkObj [("kind", Json.str "Abstract")])])]

/-- A `Th_axiom` item of `axiom_kind` `ak`, asserting the distribution declared
at `opPath` lossless. -/
private def jSurveyLosslessItem (name path ak opPath : String) : Json :=
  Json.mkObj
    [("kind", Json.str "Th_axiom"), ("name", Json.str name),
     ("path", Json.str path),
     ("decl", Json.mkObj
       [("tparams", Json.arr #[]), ("axiom_kind", Json.str ak),
        ("spec", jSurveyLosslessSpec opPath)])]

/-- The `Th_type` item declaring `Top.P.t`. -/
private def jSurveyThTypeT : Json :=
  Json.mkObj [("kind", Json.str "Th_type"), ("name", Json.str "t"),
              ("path", Json.str "Top.P.t"),
              ("decl", Json.mkObj
                [("params", Json.arr #[]),
                 ("body", Json.mkObj [("kind", Json.str "Abstract")]),
                 ("subtype", Json.null)])]

/-- The inner theory holding the lemma over its own abstract distribution. -/
private def jSurveyLemmaInner : Json :=
  Json.mkObj
    [("kind", Json.str "Th_theory"), ("name", Json.str "Q"),
     ("path", Json.str "Top.P.Q"), ("mode", Json.str "concrete"),
     ("source", Json.null),
     ("items", Json.arr
       #[jSurveyAbsDistrOp "e" "Top.P.Q.e",
         jSurveyLosslessItem "e_ll" "Top.P.Q.e_ll" "Lemma" "Top.P.Q.e"])]

/-- The outer theory, whose axiom is the lemma's premise. -/
private def jSurveyLemmaTheory : Json :=
  Json.mkObj
    [("kind", Json.str "Th_theory"), ("name", Json.str "P"),
     ("path", Json.str "Top.P"), ("mode", Json.str "abstract"),
     ("source", Json.null),
     ("items", Json.arr
       #[jSurveyThTypeT, jSurveyAbsDistrOp "d" "Top.P.d",
         jSurveyLosslessItem "d_ll" "Top.P.d_ll" "Axiom" "Top.P.d",
         jSurveyLemmaInner])]

-- The lemma is surveyed at its assembled statement: the binder for the operator
-- its premise reads is counted beside the binder for the operator its own goal
-- reads, so its line carries `ops=2`.
#guard surveyItemLines (surveyFormTables ecPrelude [jSurveyLemmaTheory]) "P"
    "Th_theory" jSurveyLemmaTheory
  == (["OK Th_type Top.P.t", "PARAM Th_operator Top.P.d ops=1",
       "PARAM Th_axiom Top.P.d_ll ops=1",
       "PARAM Th_operator Top.P.Q.e ops=1",
       "PARAM Th_axiom Top.P.Q.e_ll ops=2",
       "THEORY Top.P.Q (concrete) 0 ok / 2 param / 0 err",
       "THEORY P (abstract) 1 ok / 4 param / 0 err"], 1, 4, 5)

/-- The same theory whose imported axiom reads an operator path in no table. -/
private def jSurveyLemmaTheoryUndecodable : Json :=
  Json.mkObj
    [("kind", Json.str "Th_theory"), ("name", Json.str "P"),
     ("path", Json.str "Top.P"), ("mode", Json.str "abstract"),
     ("source", Json.null),
     ("items", Json.arr
       #[jSurveyThTypeT, jSurveyAbsDistrOp "d" "Top.P.d",
         jSurveyLosslessItem "d_ll" "Top.P.d_ll" "Axiom" "Top.P.absent",
         jSurveyLemmaInner])]

-- An axiom of the scope that does not decode rejects the lemma, and the lemma's
-- line names that axiom: the survey reports the premise as missing rather than
-- reporting a goal stated without it.
#guard (match surveyItemLines
            (surveyFormTables ecPrelude [jSurveyLemmaTheoryUndecodable]) "P"
            "Th_theory" jSurveyLemmaTheoryUndecodable with
        | (ls, 1, 2, 5) =>
          ls.any (fun l => l.startsWith "ERR Th_axiom Top.P.Q.e_ll:"
            && (l.splitOn "Top.P.d_ll").length != 1)
        | _ => false)

end SurveyGolden

/-! ### Module footprints

The checks below run `moduleGlobalsOf` and the restriction reader on the item
shape `FO_UU.ec` exports for its counting functor: a `Th_module` at the path
`Top.CountHx2` taking one module parameter and declaring the two integer
counters `c_hu` and `c_ht`. The same shape carries the three variations the
reader separates — the parameter list emptied, a procedure that does not decode,
a nested module, and a `var` at a type path in no table. -/

section ModuleFootprints

/-- The `int` type node, at EasyCrypt's path for it. -/
private def jFootTyInt : Json :=
  Json.mkObj [("kind", Json.str "Tconstr"),
              ("path", Json.str "Top.Pervasive.int"), ("args", Json.arr #[])]

/-- The `unit` type node, at EasyCrypt's path for it. -/
private def jFootTyUnit : Json :=
  Json.mkObj [("kind", Json.str "Tconstr"),
              ("path", Json.str "Top.Pervasive.unit"), ("args", Json.arr #[])]

/-- A module `var` declaration of the name `nm` at the type node `ty`. -/
private def jFootVar (nm : String) (ty : Json) : Json :=
  Json.mkObj [("name", Json.str nm), ("ty", ty)]

/-- The parameter a counting functor binds: a module at a module type declaring
no procedure. -/
private def jFootParam : Json :=
  Json.mkObj
    [("name", Json.str "H"),
     ("modtype", Json.mkObj
       [("kind", Json.str "ModuleType"),
        ("name", Json.str "Top.KEMROMx2.POracle_x2"),
        ("params", Json.arr #[]), ("args", Json.arr #[]),
        ("sig", Json.mkObj
          [("params", Json.arr #[]), ("procs", Json.arr #[])])])]

/-- A procedure `init` whose body assigns to a global of another module, at a
path no table holds. -/
private def jFootProcAbsentGlobal : Json :=
  Json.mkObj
    [("name", Json.str "init"),
     ("sig", Json.mkObj
       [("args", Json.arr #[]), ("argty", jFootTyUnit), ("ret", jFootTyUnit)]),
     ("def", Json.mkObj
       [("kind", Json.str "FBdef"), ("locals", Json.arr #[]),
        ("body", Json.arr
          #[Json.mkObj
              [("kind", Json.str "Sasgn"),
               ("lv", Json.mkObj
                 [("kind", Json.str "LvVar"),
                  ("pv", Json.mkObj
                    [("kind", Json.str "PVglob"),
                     ("xpath", Json.str "Top.Absent./c")]),
                  ("ty", jFootTyInt)]),
               ("rhs", Json.mkObj
                 [("ty", jFootTyInt), ("kind", Json.str "Eint"),
                  ("value", Json.str "0")])]]),
        ("ret", Json.null)])]

/-- A `Th_module` item at the path `Top.CountHx2`, with the parameter list
`params`, the nested-module list `mods`, the `var` list `vars` and the procedure
list `procs`. -/
private def jFootModule (params mods vars procs : Array Json) : Json :=
  Json.mkObj
    [("kind", Json.str "Th_module"), ("name", Json.str "CountHx2"),
     ("path", Json.str "Top.CountHx2"),
     ("module", Json.mkObj
       [("name", Json.str "CountHx2"), ("params", Json.arr params),
        ("body", Json.mkObj
          [("kind", Json.str "ME_Structure"), ("modules", Json.arr mods),
           ("vars", Json.arr vars), ("procs", Json.arr procs)]),
        ("sig", Json.arr #[])])]

/-- The two integer counters the exported item declares. -/
private def jFootCounters : Array Json :=
  #[jFootVar "c_hu" jFootTyInt, jFootVar "c_ht" jFootTyInt]

/-- The exported item: a functor over one parameter, declaring the two
counters. -/
private def jFootFunctor : Json :=
  jFootModule #[jFootParam] #[] jFootCounters #[]

/-- The same declarations under no parameter, with a procedure that does not
decode. -/
private def jFootProcFail : Json :=
  jFootModule #[] #[] jFootCounters #[jFootProcAbsentGlobal]

/-- The same declarations beside a nested module. -/
private def jFootNesting : Json :=
  jFootModule #[] #[Json.mkObj [("name", Json.str "N")]] jFootCounters #[]

/-- The same item with its `var` at a type path in no table. -/
private def jFootAbsentTy : Json :=
  jFootModule #[] #[]
    #[jFootVar "m"
        (Json.mkObj [("kind", Json.str "Tconstr"),
                     ("path", Json.str "Top.PROM.flag"),
                     ("args", Json.arr #[])])] #[]

/-- The names the two counters occupy. -/
private def jFootCounterNames : List String :=
  ["Top.CountHx2./c_hu", "Top.CountHx2./c_ht"]

-- A functor declares a footprint, and `decodeStructure` rejects it, so the
-- footprint is read without the parameter list.
#guard (decodeStructure ecPrelude 0 jFootFunctor).toOption.isNone

#guard (match moduleGlobalsOf ecPrelude 0 jFootFunctor with
        | .ok (p, gs) =>
          p == "Top.CountHx2" && gs.map (·.name) == jFootCounterNames
            && gs.map (·.id) == [0, 1]
        | _ => false)

-- The footprint is read at the base it is given, so two modules decoded in turn
-- hold disjoint locations.
#guard (match moduleGlobalsOf ecPrelude 7 jFootFunctor with
        | .ok (_, gs) => gs.map (·.id) == [7, 8]
        | _ => false)

-- A module whose procedures do not decode declares the same footprint: the
-- reader passes an empty procedure list, so the `var` declarations are what it
-- reads.
#guard (decodeStructure ecPrelude 0 jFootProcFail).toOption.isNone

#guard (match moduleGlobalsOf ecPrelude 0 jFootProcFail with
        | .ok (p, gs) => p == "Top.CountHx2" && gs.map (·.name) == jFootCounterNames
        | _ => false)

-- A nested module is rejected: `glob M` of a nesting module covers the nested
-- state, which the `var` list understates.
#guard (moduleGlobalsOf ecPrelude 0 jFootNesting).toOption.isNone

-- A `var` at a type path in no table has no location, so the module declares no
-- footprint the reader can give.
#guard (moduleGlobalsOf ecPrelude 0 jFootAbsentTy).toOption.isNone

/-- A module binder quantified with the restriction `{-Top.CountHx2}`, at the
exporter's shape for a `use_restr`. -/
private def jFootRestr : Json :=
  Json.mkObj
    [("restr", Json.mkObj
       [("mpaths", Json.mkObj
           [("neg", Json.arr #[Json.str "Top.CountHx2"]), ("pos", Json.null)]),
        ("xpaths", Json.mkObj
           [("neg", Json.arr #[]), ("pos", Json.null)])])]

-- The restriction resolves against the tables the scope's items extend: the
-- footprint it names is the counters', and the module it names is a functor.
#guard (match restrGlobals
            (surveyExtendTables (formTables ecPrelude []) [jFootFunctor])
            jFootRestr with
        | .ok (some gs) => gs.map (·.name) == jFootCounterNames
        | _ => false)

-- The same restriction against a scope holding no such item names a module the
-- table has no footprint for.
#guard (match restrGlobals (formTables ecPrelude []) jFootRestr with
        | .error m =>
          m.startsWith "ec-import: the restricting module 'Top.CountHx2'"
        | _ => false)

-- Two modules in one scope hold disjoint locations, and the scope reports where
-- the next range starts.
#guard (let F := surveyExtendTables (formTables ecPrelude [])
                   [jFootFunctor, jFootProcFail]
        F.modGlobals.flatMap (fun e => e.2.map (·.id)) == [0, 1, 2, 3]
          && F.nextLoc == 4)

-- A scope inside a theory continues from the enclosing scope rather than
-- reusing its locations.
#guard (let outer := surveyExtendTables (formTables ecPrelude []) [jFootFunctor]
        let inner := surveyExtendTables outer [jFootProcFail]
        inner.modGlobals.flatMap (fun e => e.2.map (·.id)) == [2, 3, 0, 1])

end ModuleFootprints

/-! ### The directory mode's line shapes

The checks below pin the three pure pieces the directory mode is assembled from:
which entries of a listing it reads and in what order, the column it puts an
envelope's lines behind, and the two tally lines. What they do not reach is the
reading itself — that a listing comes from `readDir`, that each name is opened
relative to the directory, and that an unopenable file is caught rather than
raised are checked only by running the mode. -/

section SurveyDirectory

-- Only `*.json` entries are read, and the listing is sorted here, since
-- `readDir` reports the filesystem's own order. `String` ordering puts an
-- uppercase initial before a lowercase one.
#guard surveyJsonNames
    ["b.json", "notes.txt", "a.json", "Zed.json", "sub", "x.json.bak"]
  == ["Zed.json", "a.json", "b.json"]

#guard surveyJsonNames [] == []

-- The column is the file name without its final extension. A corpus file name
-- carries the source theory's own extension, which stays.
#guard surveyFilePrefix "algebra__Monoid.eca.json" == "algebra__Monoid.eca "

#guard surveyFilePrefix "otp.expected.json" == "otp.expected "

-- A name with no extension is its own stem.
#guard surveyFilePrefix "corpus" == "corpus "

-- The column goes in front of every line of the envelope, the `THEORY` and
-- `SURVEY` lines included.
#guard surveyPrefixed "m.eca " ["OK Th_type Top.T.t", "THEORY T (abstract) 1 ok"]
  == ["m.eca OK Th_type Top.T.t", "m.eca THEORY T (abstract) 1 ok"]

-- The empty prefix is what `--survey` passes, and it leaves the lines alone.
#guard surveyPrefixed "" ["OK Th_type Top.T.t"] == ["OK Th_type Top.T.t"]

-- The error bucket of a tally is what is left of the total.
#guard surveyTallyLine 3 2 7 == "SURVEY 3 ok / 2 param / 2 err"

#guard surveyTallyLine 0 0 0 == "SURVEY 0 ok / 0 param / 0 err"

#guard surveyTallyLine 4 0 4 == "SURVEY 4 ok / 0 param / 0 err"

-- The aggregate counts files and undecodable envelopes beside the item buckets:
-- a file that yields no items is not a file whose items fail to decode.
#guard surveyAllTallyLine 97 1 272 4 7050
  == "SURVEY-ALL 97 files / 1 envelope err / 272 ok / 4 param / 6774 err"

#guard surveyAllTallyLine 0 0 0 0 0
  == "SURVEY-ALL 0 files / 0 envelope err / 0 ok / 0 param / 0 err"

end SurveyDirectory

/-! ## The statement flags

The checks below pin what the `--statement` flags parse to and which argument
lists are rejected. The generated file itself is checked byte for byte in
`EmitCheck.lean`. -/

section StatementFlags

-- A binding splits at its first `=`, so the text may carry further ones, which
-- a printed lambda and a printed equation both do.
#guard splitBinding "--proc" "Top.OTP0./main=lowerClosedGame (otpGame false)"
  == .ok ("Top.OTP0./main", "lowerClosedGame (otpGame false)")

#guard splitBinding "--iface" "A=fun _ _ => x = y"
  == .ok ("A", "fun _ _ => x = y")

#guard (match splitBinding "--proc" "Top.OTP0./main" with
        | .error m => m.startsWith "ec-import: '--proc Top.OTP0./main'"
        | _ => false)

-- The flags fill the four text fields and the three tables, in the order given.
#guard (match parseStatementFlags
            ["--rho", "otpEnv", "--form", "otpEquivForm", "--import", "M",
             "--open", "N", "--proc", "p=t", "--procfn", "q=u",
             "--iface", "A=I"] {} with
        | .ok o =>
          o.rho == "otpEnv" && o.form == "otpEquivForm" && o.imports == ["M"]
            && o.opens == ["N"] && o.procNames == [("p", "t")]
            && o.procFnNames == [("q", "u")] && o.interfaces == [("A", "I")]
        | _ => false)

-- A repeated flag appends, and the generated file carries the imports in the
-- order the command line gives them.
#guard (match parseStatementFlags ["--import", "M", "--import", "N"] {} with
        | .ok o => o.imports == ["M", "N"]
        | _ => false)

#guard (match parseStatementFlags ["--nope", "x"] {} with
        | .error m => m.startsWith "ec-import: '--nope' is not a --statement flag"
        | _ => false)

#guard (match parseStatementFlags ["--rho"] {} with
        | .error m => m.startsWith "ec-import: the flag '--rho' takes a value"
        | _ => false)

-- The environment and the form are named, not defaulted: a statement whose
-- resolution environment the caller did not give has no generated file.
#guard (match emitStatementFromJson ecPrelude "l" "d" {} Json.null with
        | .error m => m.startsWith "ec-import: --statement takes --rho"
        | _ => false)

#guard (match emitStatementFromJson ecPrelude "l" "d" { rho := "ρ" } Json.null with
        | .error m => m.startsWith "ec-import: --statement takes --form"
        | _ => false)

end StatementFlags

end CatCrypt.Crypto.EasyCryptImport

/-- The entry point `lean --run` calls, which is `emitMain` on the command line's
arguments. -/
def main (args : List String) : IO UInt32 :=
  CatCrypt.Crypto.EasyCryptImport.emitMain args


# catcrypt-easycrypt — EasyCrypt importer for CatCrypt

> **Under construction.** The exporter's schema and the accepted fragment are
> both still changing. The schema version is pinned exactly, so an upgrade of the
> exporter requires a matching change here. Expect breaking changes between
> revisions.

Decodes the output of [`ec2json`](https://github.com/spitters/ec-export) — an
EasyCrypt typed-AST exporter — into an intrinsically typed Lean AST, lowers that
AST to `SPComp`, the semantic model CatCrypt's pRHL rules and advantage lemmas
are stated over, and translates an imported EasyCrypt judgement into a CatCrypt
proposition.

An imported statement is a Lean goal to prove or a hypothesis to assume — never
a theorem and never an axiom. An EasyCrypt proof is not a Lean proof, so no
proof crosses the boundary.

```
  M.ec            EasyCrypt source
   │  ec2json     a separate project; links EasyCrypt's own ecLib out of tree
   ▼
  M.json          schema "catcrypt-ec-export", version 5, compared for equality
   │  Json.lean       programs:   EcTy / EcExpr / EcStmt / EcModule / EcGame
   │  FormJson.lean   statements: EcTerm / EcProb / EcForm
   ▼
  Lean AST
   ├── Emit.lean ───────▶ a committed .lean literal with a provenance header
   ├── Lower.lean ──────▶ an SPComp program
   └── FormToProp.lean ─▶ a CatCrypt Prop — the imported goal
```

## Trust

**The exporter, both decoders and the statement translation are unverified, and
they sit in the trust base of every imported definition.** No theorem relates
EasyCrypt's semantics to CatCrypt's. A theorem proved about an imported game is
a theorem about the Lean game; its relation to the `.ec` source holds modulo the
exporter and the decoder, and a mistranslated formula produces a well-formed
goal about the wrong thing.

[`docs/TRUST.md`](docs/TRUST.md) states what bounds that exposure — exact schema
pinning, absent field defaults, rejection by construct name, total decoders,
committed literals checked against the emitter — and the three points at which
the total lowering answers with a value where a partial function would fail.

## Build

Lean 4.30.0 (`lean-toolchain`). The dependencies are declared in
`lakefile.lean`: [CatCrypt-core](https://github.com/spitters/CatCrypt-core) for
`SPComp`, the heap, non-uniform sampling and the pRHL and pHL rule sets,
[hax-lean](https://github.com/spitters/hax-lean) for the JSON size measure the
decoders recurse on, and mathlib4.

```
lake exe cache get
lake build CatCrypt.Crypto.EasyCryptImport.All
```

`All.lean` is the import manifest. Building it forces every module of the
importer, including the worked examples and the emitter, and runs every golden
`#guard`.

## Emitting a program

A program is imported by committing the printed AST as Lean source and proving
theorems about that literal.

```
lake env lean --run CatCrypt/Crypto/EasyCryptImport/EmitMain.lean \
  <export.json> <game|module|functor> <item-name> <decl-name> <out.lean>
```

`<out.lean>` of `-` prints to standard output. The generated declaration lands
in the namespace `CatCrypt.Crypto.EasyCryptImport.Generated`. The command line
decodes against EasyCrypt's boolean and unit prelude only; a source using a
finite scalar type or a further uniform distribution needs extended dispatch
tables, so call `emitFromJson` from Lean instead.

A statement is imported without committing a literal: `formTables` builds the
decoding tables from the export's own modules, `importAxiom` decodes a named
lemma to an `EcForm`, and `importedProp` translates it against a resolution
environment binding the procedures the statement names.

## Documentation

| | |
|---|---|
| [`docs/FRAGMENT.md`](docs/FRAGMENT.md) | What imports, what does not, and why each construct is rejected |
| [`docs/TRUST.md`](docs/TRUST.md) | The trust boundary: what is unverified, what bounds it, where the lowering degrades |
| [`docs/DESIGN.md`](docs/DESIGN.md) | The decode-lower-translate pipeline, the module map, the repository layout |
| [`CatCrypt/Crypto/EasyCryptImport/README.md`](CatCrypt/Crypto/EasyCryptImport/README.md) | The importer directory: the worked examples and the commands, for a reader already in the tree |
| [`CatCrypt/Crypto/EasyCryptImport/AGENTS.md`](CatCrypt/Crypto/EasyCryptImport/AGENTS.md) | Maintenance: fixtures and their mirror, regeneration, invariants, open work |

The exporter is <https://github.com/spitters/ec-export>, cloned as the sibling
`../ec-export`; it is not part of this repository, and this package accepts its
schema version 5 exactly. EasyCrypt: <https://www.easycrypt.info/>.

## License

MIT — see [LICENSE](LICENSE). Third-party attribution is in [NOTICE](NOTICE).

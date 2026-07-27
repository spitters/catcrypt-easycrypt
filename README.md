# catcrypt-easycrypt

An importer that brings EasyCrypt developments into Lean 4 as CatCrypt objects.
An `.ec` source file becomes an EasyCrypt typed AST, that AST becomes JSON, the
JSON becomes a Lean AST, and the Lean AST becomes either a committed Lean
literal (a program) or a CatCrypt `Prop` (a statement). An imported program
lowers to `SPComp`, the semantic model CatCrypt's pRHL rules and advantage
lemmas are stated over; an imported lemma arrives as a goal for a human to
close.

Imported statements are goals, never theorems and never axioms. An EasyCrypt
proof is not a Lean proof, so no proof crosses the boundary.

```
  M.ec                     EasyCrypt source
    │  ec2json             links EasyCrypt's own ecLib out of tree
    ▼
  M.json                   schema "catcrypt-ec-export", version 4 (pinned exactly)
    │  Json.lean           programs: EcTy / EcExpr / EcStmt / EcModule / EcGame
    │  FormJson.lean       statements: EcTerm / EcProb / EcForm
    ▼                      total decoders, no field defaults
  Lean AST
    ├── Emit.lean ──────▶  committed .lean literal + provenance header
    ├── Lower.lean ─────▶  SPComp program
    └── FormToProp.lean ▶  a CatCrypt Prop — the imported goal
```

`ec2json` is a separate OCaml project, cloned as the sibling `../ec-export`. It
is not part of this repository.

## What is here

| Path | Contents |
|---|---|
| `CatCrypt/Crypto/EasyCryptImport/` | the importer: the AST, the two decoders, the lowering, the statement translation, the emitter, and the import manifest `All.lean` |
| `CatCrypt/Crypto/EasyCryptImport/Examples/` | the worked examples, and the emitter's committed output |
| `CatCrypt/Crypto/EasyCryptImport/*.expected.json` | the exporter fixtures the golden `#guard`s read with `include_str` |
| `CatCrypt/{Core,NonUniform}/` | re-export shims giving the `CatCrypt.*` module names for the `CatCryptCore.*` modules the importer imports |
| `scripts/ec-fixture-sync.sh` | the fixture-mirror check against the exporter's own goldens |

`CatCrypt/Crypto/EasyCryptImport/README.md` documents the pipeline, the module
roles, the imported fragment and the rejected constructs in full; `AGENTS.md`
beside it holds the editing notes and invariants.

## Dependencies

| Package | What this package uses it for |
|---|---|
| [CatCrypt-core](https://github.com/spitters/CatCrypt-core) | `SPComp` and sub-distributions, the generic heap and `Location`, non-uniform sampling, the pRHL and pHL rule sets, `Advantage` and `sdist` — the targets the lowering and the statement translation land on |
| [hax-lean](https://github.com/spitters/hax-lean) | `HaxLean.JsonSize`, the JSON size measure both decoders recurse on, which is what makes them total `def`s rather than `partial def`s |
| [mathlib4](https://github.com/leanprover-community/mathlib4) | `Countable`, `Fintype` and `ℝ≥0∞` |

`catcryptCore` is a local path dependency (`../CatCrypt-core`); `lakefile.lean`
records the git-dependency line that replaces it at publication.

## The imported fragment

Programs cover `unit`, `bool`, a finite scalar type `fin n`, products, `int` and
finite maps; the expression layer over them; the `EcDistr` distribution
operators (`duniform` at a finite code, `dunit`, `dmap`, `dcond`, `dlet`, the
independent product, `dscale`, `drestrict`, `dexcepted`); local assignment,
sampling, global read and write, the conditional, the bounded loop, and calls;
concrete modules with global state, module types, functors of any number of
parameters, and abstract modules as `ModuleImpl` parameters. Statements cover
the first-order skeleton with quantifiers over a type code, a memory, a
probability parameter or a module type, probabilities `Pr[q(arg) @ &m : ev]`,
and the procedure-level `hoare`, `bd_hoare` and `equiv` judgements. Module
restrictions (`A{-M}`, `islossless`, `={glob A}`) are emitted as explicit side
hypotheses on the imported statement.

Every construct outside the fragment is rejected by name, with a decode error
carrying the construct and the reason: unbounded `while`, uniform sampling at a
non-finite code, complexity and cost annotations, statement-level judgements,
higher-order quantification, general real terms, signed subtraction of
probabilities, and the others listed in the importer's own README. None is
silently degraded to something weaker that merely typechecks.

## The trust boundary

**Unverified, and in the trust base of every imported definition:** the
exporter, both decoders, and the statement translation. No theorem relates
EasyCrypt's semantics to CatCrypt's. A theorem proved about an imported game is
a theorem about the Lean game; its relation to the `.ec` source holds modulo the
exporter and the decoder. The translation of a formula is a definition of intent
— it says which CatCrypt proposition the importer takes an EasyCrypt judgement
to mean — and a mistranslation would produce a well-formed goal about the wrong
thing.

What bounds the exposure:

- **Schema pinning.** The envelope's schema name and version are compared for
  exact equality, so exporter drift surfaces as a version mismatch or an unknown
  node discriminator, not as a misparse.
- **No field defaults.** A missing, mistyped or unrecognised field is a decode
  error, never a plausible-looking value.
- **Loud rejection.** The statement fixture's rejections are checked as
  rejections, so a change that let one of them decode to something merely
  well-typed fails the build.
- **Total decoders.** Every decoder is a `def`, not a `partial def`, recursing
  on a JSON size measure.
- **Committed literals are the emitter's output.** For each generated file a
  `#guard` compares the emitter's text with the committed file. A hand edit to a
  generated file, or emitter drift, fails the build.
- **Provenance headers.** A generated file records its source file, a digest of
  that source, the schema and version, the EasyCrypt build, and the theory root.
- **Statements are goals.** A generated statement is a `def … : Prop`. The
  importer states no imported theorem and introduces no axiom.

What those do not cover. The lowering is total, and at three points it answers
with a value where a partial function would raise an error:

- **An unresolved call returns the default value.** `ProcEnv` is total: a
  qualified name the caller did not bind resolves to `SPComp.pure default`
  (`Modules.lean`). A statement resolved against an environment missing one of
  the procedures it names is a well-formed goal about a program that returns
  `default` at that call.
- **A call reached at fuel zero is a no-op.** `lowerStmts` bounds argument-free
  call nesting by a `fuel` argument the caller supplies, and a `call` reached at
  `fuel = 0` lowers to nothing (`Lower.lean`). A fuel below the game's call depth
  drops the rest of the inlining.
- **A valuation read at the wrong type code is the default value.** `Env` is
  dynamically typed, so `Env.read t x` where `x` holds a value of another code
  returns `default` (`Lower.lean`).

All three are properties of the lowering rather than of the decoder: the fuel and
the resolution environment are what the caller supplies. A well-formed import
supplies a fuel at least the game's call depth and a binding for every qualified
name the game mentions.

## Building

```
lake build CatCrypt.Crypto.EasyCryptImport.All
```

`All.lean` is the import manifest: building it forces every module of the
importer, including the worked examples and the emitter, and runs every golden
`#guard`.

Emit a program as committed Lean:

```
lake env lean --run CatCrypt/Crypto/EasyCryptImport/EmitMain.lean \
  <export.json> <game|module> <item-name> <decl-name> <out.lean>
```

The generated declaration lands in the namespace
`CatCrypt.Crypto.EasyCryptImport.Generated`.

## Fixture mirror check

The golden `#guard`s read the exporter's JSON with `include_str`, which needs a
path inside this repository, so each exercised fixture is committed here as well
as in the exporter's `tests/`. Compare the two copies with

```
bash scripts/ec-fixture-sync.sh
```

which fails when a mirrored fixture differs from the exporter's golden, when it
has no `.ec` source to regenerate it from, or when no `include_str` reads it. It
looks for the exporter at `../ec-export`; override with `EC_EXPORT_DIR`. With no
exporter checkout it reports that and exits 0.

## License

MIT — see [LICENSE](LICENSE). Third-party attribution is in [NOTICE](NOTICE).

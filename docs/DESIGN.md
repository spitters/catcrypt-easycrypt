# Design

The decode-lower-translate pipeline, the module map, and the repository layout.

## The pipeline

```
  M.ec                                    EasyCrypt source
    │
    │  ec2json          links EasyCrypt's own ecLib out of tree; no patch to
    ▼                   the EasyCrypt sources; exports after typechecking
  M.json                schema "catcrypt-ec-export", version 10 (pinned exactly)
    │
    │  Json.lean        programs:   EcTy / EcExpr / EcStmt / EcModule / EcGame
    │  FormJson.lean    statements: EcTerm / EcProb / EcForm
    ▼                   total decoders, no field defaults
  Lean AST
    ├── Emit.lean, EmitMain.lean ──▶  committed .lean literal + provenance header
    │                                 (proofs run against the literal)
    ├── Lower.lean ───────────────▶  SPComp program
    └── FormToProp.lean ──────────▶  a CatCrypt Prop — the imported goal
```

### Export

`ec2json` is a separate OCaml project, cloned as the sibling `../ec-export`. It
links EasyCrypt as a library rather than patching it: EasyCrypt's `src/dune`
publishes `easycrypt.ecLib`, so an out-of-tree project reaches the typed AST
directly. It exports after typechecking, because the elaborated AST carries what
the Lean side needs and the surface syntax does not — the type at every
expression node, resolved operator paths, the global-versus-local distinction
for program variables, and module restrictions.

### Decode

Two decoders read one envelope: `Json.lean` for programs and `FormJson.lean` for
statements. Both are `def`s recursing on `HaxLean.JsonSize`, the JSON size
measure, so a malformed input is a decode error rather than a hang, and every
field access is an `Except` error naming the field and the node. The envelope's
schema name and version are compared for exact equality before anything else is
read. The dispatch tables — the operator and distribution paths a source's
prelude uses — are a parameter of the decoders, extended per source through
`DecodeTables`.

The decoded AST is intrinsically typed: `EcTy` is the type universe, `EcExpr t`
an expression at a code, `EcTerm t` a statement-layer term, so an ill-typed
export has no AST value to decode to.

### Lower

`Lower.lean` sends a decoded program to `SPComp`. A local variable is a
meta-level valuation entry (`Env`, keyed by a source name and an optional
uniqueness stamp), so a local assignment is a functional rebinding; a
module-scoped `var` is a `GLocation` on the CatCrypt heap. `evalDistr` sends a
distribution expression to an `SDistr`, with the general sampling arm going
through `NonUniform.sampleFrom`. A qualified call resolves through `ProcEnv`,
the ambient environment the caller supplies; an argument-free intra-game call is
inlined under a caller-supplied depth bound. Both of those parameters are where
the lowering can answer with a default rather than fail — see
[`TRUST.md`](TRUST.md).

### Translate

`FormToProp.lean` sends a decoded formula to a CatCrypt `Prop`, resolved against
a `FormEnv`: the procedures the statement names, the images of the functors it
applies, and the bindings of its own quantifiers. Module restrictions become
explicit side hypotheses (`RespectsLocs`, `RespectsOn`, `ProcLossless`) rather
than conditions encoded in the module type. The result is a `def … : Prop` — a
goal to prove or a hypothesis to assume.

### Emit

The decoders are well-founded recursive, so a decoded value has no
kernel-reducible equations and cannot be evaluated inside a proof. A proof about
an imported program therefore runs against a committed Lean literal that
`Emit.lean` printed, and `EmitCheck.lean` holds each committed file to the
emitter's current output. The constraint and the rejected alternatives are in
[`CatCrypt/Crypto/EasyCryptImport/AGENTS.md`](../CatCrypt/Crypto/EasyCryptImport/AGENTS.md).

## Modules

| File | Role |
|---|---|
| `Ty.lean` | the type universe `EcTy` and its interpretation, with the `Countable` / `Inhabited` / `DecidableEq` instances a heap cell and equality tests require, and `isFin`, the predicate marking the codes uniform sampling and the `Location` view of a cell are stated against |
| `Ast.lean` | program syntax: typed expressions, typed distribution expressions, statements, globals, procedures, interfaces, modules, functors, games |
| `Modules.lean` | what an imported module is on the CatCrypt side (`ModuleImpl`), and how a qualified call resolves (`ProcEnv`) |
| `FunctorN.lean` | functors of several parameters: the parameter list, the curried lowering, and the decoder |
| `Lower.lean` | the lowering of the AST to `SPComp`, with `evalDistr` sending a distribution expression to an `SDistr` and the general sampling arm going through `NonUniform.sampleFrom` |
| `Restrictions.lean` | `RespectsLocs`, `RespectsOn` and `ProcLossless`, the predicates module restrictions and footprints are emitted as |
| `Form.lean` | statement syntax: the term, probability and formula layers |
| `Json.lean` | the program decoder, with golden `#guard`s over an exporter fixture |
| `FormJson.lean` | the statement decoder, with golden `#guard`s over an exporter fixture |
| `FormToProp.lean` | the translation of a formula to a CatCrypt proposition |
| `Emit.lean` | printing an AST value as Lean source, with a provenance header |
| `EmitMain.lean` | the `ec2lean` command-line entry point |
| `EmitCheck.lean` | the checks that the committed generated files are the emitter's output |
| `All.lean` | the import manifest; building it forces every module and every `#guard` |

## Repository layout

| Path | Contents |
|---|---|
| `CatCrypt/Crypto/EasyCryptImport/` | the importer: the AST, the two decoders, the lowering, the statement translation, the emitter, and the import manifest `All.lean` |
| `CatCrypt/Crypto/EasyCryptImport/Examples/` | the worked examples, and the emitter's committed output |
| `CatCrypt/Crypto/EasyCryptImport/*.expected.json` | the exporter fixtures the golden `#guard`s read with `include_str` |
| `CatCrypt/{Core,NonUniform}/` | re-export shims giving the `CatCrypt.*` module names for the `CatCryptCore.*` modules the importer imports |
| `docs/` | this document, the fragment, and the trust boundary |
| `scripts/ec-fixture-sync.sh` | the fixture-mirror check against the exporter's own goldens |

## Dependencies

| Package | What this package uses it for |
|---|---|
| [CatCrypt-core](https://github.com/spitters/CatCrypt-core) | `SPComp` and sub-distributions, the generic heap and `Location`, non-uniform sampling, the pRHL and pHL rule sets, `Advantage` and `sdist` — the targets the lowering and the statement translation land on |
| [hax-lean](https://github.com/spitters/hax-lean) | `HaxLean.JsonSize`, the JSON size measure both decoders recurse on, which is what makes them total `def`s rather than `partial def`s |
| [mathlib4](https://github.com/leanprover-community/mathlib4) | `Countable`, `Fintype` and `ℝ≥0∞` |

The `CatCrypt` library glob spans the importer subtree together with the
`CatCryptCore.*` re-export shims, because a `require` on `catcryptCore` supplies
the `CatCryptCore.*` module names alone while a consumer's imports name
`CatCrypt.Crypto.EasyCryptImport.*`.

## The CatCrypt targets

`CatCryptCore.Relational.Rules` (pRHL), `CatCryptCore.Unary.Judgment` and
`CatCryptCore.Unary.Rules` (pHL), `CatCryptCore.Crypto.Advantage`, and
`CatCryptCore.Crypto.EasyCryptBridge`.

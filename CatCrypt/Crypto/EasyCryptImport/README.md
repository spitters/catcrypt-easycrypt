# `EasyCryptImport/` — importing EasyCrypt developments into CatCrypt

This directory imports EasyCrypt games and lemmas into Lean. A `.ec` source file
becomes an EasyCrypt typed AST, that AST becomes JSON, the JSON becomes a Lean
AST, and the Lean AST becomes either a committed Lean literal (a program) or a
CatCrypt `Prop` (a statement). An imported program lowers to `SPComp`, the
semantic model CatCrypt's pRHL rules and advantage lemmas are stated over; an
imported lemma arrives as a goal for a human to close.

Imported statements are goals, never theorems and never axioms. An EasyCrypt
proof is not a Lean proof, so no proof crosses the boundary.

The exporter, both decoders and the statement translation are unverified, and
they sit in the trust base of every imported definition. No theorem relates
EasyCrypt's semantics to CatCrypt's. "The trust boundary" below states what that
leaves open and what bounds it.

## The pipeline

```
  M.ec                                    EasyCrypt source
    │
    │  ec2json          links EasyCrypt's own ecLib out of tree; zero patches
    ▼                   to the EasyCrypt sources; exports after typechecking
  M.json                schema "catcrypt-ec-export", version 4 (pinned exactly)
    │
    │  Json.lean        programs: EcTy / EcExpr / EcStmt / EcModule / EcGame
    │  FormJson.lean    statements: EcTerm / EcProb / EcForm
    ▼                   total decoders, no field defaults
  Lean AST
    ├── Emit.lean, EmitMain.lean ──▶  committed .lean literal + provenance header
    │                                 (proofs run against the literal)
    ├── Lower.lean ───────────────▶  SPComp program
    └── FormToProp.lean ──────────▶  a CatCrypt Prop — the imported goal
```

`ec2json` is a separate OCaml project (clone it as the sibling `../ec-export`).
It links EasyCrypt as a library rather than patching it: EasyCrypt's `src/dune`
publishes `easycrypt.ecLib`, so an out-of-tree project reaches the typed AST
directly. It exports after typechecking, because the elaborated AST carries what
the Lean side needs and the surface syntax does not — the type at every
expression node, resolved operator paths, the global-versus-local distinction for
program variables, and module restrictions.

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

## What imports

### Programs

| Layer | Fragment |
|---|---|
| Types | `unit`, `bool`, a finite scalar type (`fin n`, of cardinality `n`, interpreted as `Fin n`), products, `int`, and finite maps (`map a b`, an association list). `EcTy.isFin` marks the finite subset — `unit`, `bool`, `fin n`, and a product of two finite codes — which is where uniform sampling and a `Location` live |
| Expressions | variables, literals, negation, conjunction, exclusive-or, decidable equality at any type code, pair construction and projection, wrapping addition on `fin n`, integer addition and comparison, and the finite-map operations (bind a key, test membership, look up with a default). Disjunction and implication decode through their de Morgan images |
| Distributions | the uniform distribution at a finite code, `dunit`, `dmap`, `dcond`, `dlet`, the independent product ``(`*`)``, `dscale`, `drestrict`, and `dexcepted` (`d \ X`), which is `dcond` at the negated predicate — its own EasyCrypt definition. A distribution operator whose argument is a function carries the binder's identity — its source name together with EasyCrypt's uniqueness stamp — and the body is evaluated in the local valuation extended at that identity |
| Statements | local assignment, uniform sampling at a finite code, sampling from a distribution expression, global read and write at any code, the conditional, the bounded loop `for i = 0 to n-1`, an argument-free intra-game call (inlined under a depth bound), and a call `x <@ q(a)` at a signature resolved against the ambient environment |
| Memory | a local variable is a meta-level valuation entry keyed by its identity — a program variable by its source name, a bound identifier by that name together with its uniqueness stamp — so a local assignment is functional rebinding and a binder cannot capture an occurrence of another identifier of its name; a module-scoped `var` is an `EcGlobal` at a CatCrypt `GLocation`, read and written by `SPComp.gget` / `SPComp.gset`, at every type code. At a finite code that cell is also a `Location` read and written by `SPComp.get` / `SPComp.set` (`lowerStmts_load_finLoc`, `lowerStmts_store_finLoc`) |
| Modules | concrete modules with global state, module types, functors of any number of parameters (a curried Lean function on `ModuleImpl`s, one argument per parameter), and abstract modules — an adversary or oracle given only by its interface — as `ModuleImpl` parameters, so an imported game quantified over all adversaries is a Lean `∀ (A : ModuleImpl I), …` |

### Statements

| Layer | Fragment |
|---|---|
| Terms | logical variables, literals, the expression fragment above, a module global read at a memory (`g{&m}`), and the result of the enclosing judgement (`res{1}`, `res{2}`, `res`) |
| Probabilities | `Pr[q(arg) @ &m : ev]`, constants, a probability parameter, sum, product, absolute difference |
| Formulas | the first-order skeleton, quantifiers over a type code, a memory, a probability parameter or a module type, term and memory equality, agreement of two memories on a module's footprint (`={glob M}`), `if`, `let` |
| Judgements | the procedure-level `hoare`, `bd_hoare` and `equiv`, and probability comparisons |

A distinguishing bound translates structurally, to an absolute difference of two
probabilities at the memory the source names — not to `Advantage`, `AdvantageA`
or `sdist`, each of which would change the statement (respectively by fixing the
initial heap, by post-composing an unmentioned distinguisher, and by taking a
supremum over distinguishers and heaps). Two named bridges in `FormToProp.lean`
say what extra quantification reaches those forms.

### Module restrictions

EasyCrypt's `A{-M}` and `islossless` are emitted as explicit side hypotheses on
the imported statement, not dropped and not encoded in the module type:

| EasyCrypt | Emitted hypothesis |
|---|---|
| `A{-M}` | `ModuleRespectsLocs (globLocs M.globals) A` — run from two heaps agreeing outside `M`'s footprint, each procedure returns equal values and leaves heaps that still agree outside it |
| `islossless A.f` | `ProcLossless (A.proc "f")` — the output sub-distribution has total mass one |
| `glob A`, for a statement that names it | `ModuleRespectsOn L A` at a bound footprint `L` — run from two heaps agreeing *on* `L`, each procedure returns equal values and leaves heaps that still agree on it |

The predicates are satisfiable and compositional: a heap-independent procedure
respects every footprint and lives on every footprint, and each is closed under
sequencing, so a functor over a restricted adversary inherits the restriction.

`declare module A <: I{-M}` is legal only inside an EasyCrypt section, and the
top-level environment does not bind it. Closing the section generalises the
statements that used `A` over it, so a restricted abstract module reaches the
importer as the module binder of a generalised formula: `EcForm.allModRestr`,
whose translation quantifies over `ModuleImpl I` under the `ModuleRespectsLocs`
hypothesis. `islossless A.f` over such a binder is `EcForm.lossless`. The names
the section leaves unbound are listed in the export's `section_local`.

An abstract module declares no globals, so a statement that names `glob A` needs
the set of locations `A` reads and writes as a second bound variable. Such a
binder is `EcForm.allModRestrOn` (or `EcForm.allModOn` when unrestricted): it
quantifies a module `M` and a footprint `L`, with `L` disjoint from the
restricting module's footprint, with `M` living on `L`, and with the
`ModuleRespectsLocs` hypothesis the plain binder carries. `={glob A}` is then
`agreeOn L`, the precondition the source writes — a relation that agreement
outside the restricting module's footprint implies. A concrete module's
`={glob M}` never reaches this path: EasyCrypt's `Fglob` node carries a module
identifier, which is always a binder, and the typechecker expands a concrete
module's footprint into one equality per declared `var` before the export.

## What does not import

Every construct below is rejected by name, with a decode error carrying the
construct and the reason. None is silently degraded to something weaker that
merely typechecks.

| Construct | Reason |
|---|---|
| The distribution operators outside `EcDistr` (`dnull`, `dbiased`, `dbin`, `duniform` over a list, `dlist`, `dfun`, `dopt`, `dfold`, `dinter`) | a distribution operator outside the ingestion's `distrOpPaths` table cannot decode to a sample. `dbiased` and `dbin` take a real-valued argument in an expression position, and reals reach the importer only as probabilities; the rest need a list, an option or a function type, none of which `EcTy` has |
| A distribution operator's function argument given other than as a one-binder lambda | `EcDistr`'s binder is a variable name; a predicate supplied as an operator, a composition, or a lambda of several binders has no image |
| Unbounded `while` | it carries a runtime guard and no bound; the AST's only loop is the statically bounded one |
| Uniform sampling at a non-finite code | `SPComp.sample` is uniform over its carrier, so `EcStmt.sample` and `EcDistr.uniform` each carry a proof that the code is finite and the decoder rejects a uniform sample at `int` or at a map. A non-uniform distribution at a non-finite code is in the fragment, since `sampleFrom` needs no finiteness |
| Complexity and cost annotations | there is no `SPComp`-level query counter or running time to state them against. An imported concrete-security statement that depends on `q_H` or on a running time loses that dependence |
| Statement-level judgements (`hoare{ s }`, `equiv{ s₁ ~ s₂ }`) and assertions over procedure locals | their assertions range over local variables, and locals are meta-level in the lowering, so there is nothing for such an assertion to denote |
| Expectation-Hoare and eager/lazy judgements | CatCrypt has no corresponding judgement |
| Higher-order quantification over operators or distributions, and `glob M` in value position | the quantifiers range over a type code, a memory, a probability or a module type; a footprint is available as one side of a comparison, not as a value |
| General real terms, including a quotient bound such as `q / 2^n` | reals appear only as probabilities |
| Signed subtraction of probabilities | probabilities translate into `ℝ≥0∞`, where subtraction is truncated, so a difference EasyCrypt allows to be negative has no faithful image. The bound shapes EasyCrypt statements use, `\|Pr[A] − Pr[B]\| ≤ ε` and `Pr[A] ≤ Pr[B] + ε`, are in the fragment |
| A module defined as an application of a functor, `module G = F(M)` or `module G (X : I) = F(X, M)` | its body is an `ME_Alias` whose target is the applied module path as a string, with no body behind it; the export's `arity` says how many of the node's parameters the alias binds itself and how many are the target's residual ones. The image a statement names is supplied by the caller through `FormEnv.functorImages` |
| Two parameters of one functor sharing a source name, `module F (P : I) (P : J)` | EasyCrypt permits it, and a call inside the body is the cross-path `P./p`, which carries no stamp; binding both under that prefix would make one shadow the other |
| Pattern matching, `let` over a tuple pattern, tuple expressions of arity above two, an identifier reduced to a name without its uniqueness stamp | each has no image in the AST, and truncating a stamp would make two distinct binders of the same source name alias. A tuple *type* of any arity decodes, as the right-nested binary product `t₁ × (t₂ × (… × tₙ))`; `Etuple` and `Eproj` stay binary. A procedure binds every formal of `sig.args`, each taking its component of the right-nested argument at call entry |

## Running the pipeline

Export. The exporter needs the `easycrypt` opam switch, and `-rectypes`, because
EasyCrypt builds `ecLib` with it.

```
eval $(opam env --switch=easycrypt --set-switch)
dune build                                    # in ../ec-export
./_build/default/bin/ec2json.exe -o tests/otp.expected.json tests/otp.ec
```

An unsupported construct is exported as an explicit node, reported on stderr, and
makes the exit code non-zero unless `--allow-unsupported` is given.

Emit a program as committed Lean.

```
lake env lean --run CatCrypt/Crypto/EasyCryptImport/EmitMain.lean \
  <export.json> <game|module> <item-name> <decl-name> <out.lean>
```

`<out.lean>` of `-` prints to standard output. The generated declaration lands in
the namespace `CatCrypt.Crypto.EasyCryptImport.Generated`. The command line
decodes against EasyCrypt's boolean and unit prelude only; a source using a
finite scalar type or a further uniform distribution needs extended dispatch
tables, so call `emitFromJson` from Lean instead.

Import a statement. `formTables` builds the decoding tables from the export's own
modules, `importAxiom` decodes a named lemma to an `EcForm`, and `importedProp`
translates it against a resolution environment binding the procedures the
statement names. `Examples/OTPEquivImport.lean` is the worked shape.

Build and check.

```
lake build CatCrypt.Crypto.EasyCryptImport.All
```

This forces every module of the importer, including the examples, and runs every
golden `#guard`.

The `#guard`s read the exporter's JSON with `include_str`, so each exercised
fixture is committed here as well as in the exporter's `tests/`. Compare the two
copies with

```
bash scripts/ec-fixture-sync.sh
```

which fails when a mirrored fixture differs from the exporter's golden, when it
has no `.ec` source to regenerate it from, or when no `include_str` reads it.

## The trust boundary

**Unverified, and in the trust base of every imported definition:** the exporter,
both decoders, and the statement translation. No theorem relates EasyCrypt's
semantics to CatCrypt's. A theorem proved about an imported game is a theorem
about the Lean game; its relation to the `.ec` source holds modulo the exporter
and the decoder. The translation of a formula is a definition of intent — it says
which CatCrypt proposition the importer takes an EasyCrypt judgement to mean —
and a mistranslation would produce a well-formed goal about the wrong thing.

What bounds the exposure:

- **Schema pinning.** The envelope's schema name and version are compared for
  exact equality. Exporter drift surfaces as a version mismatch or an unknown
  node discriminator, not as a misparse.
- **No field defaults.** A missing, mistyped or unrecognised field is a decode
  error, never a plausible-looking value.
- **Loud rejection.** Every construct outside the fragment is an error naming the
  construct. The statement fixture's rejections are checked as rejections, so a
  change that let one of them decode to something merely well-typed fails the
  build.
- **Total decoders.** Every decoder is a `def`, not a `partial def`, recursing on
  a JSON size measure.
- **Committed literals are the emitter's output.** For each generated file a
  `#guard` compares the emitter's text with the committed file, read by
  `include_str`. A hand edit to a generated file, or emitter drift, fails the
  build.
- **Provenance headers.** A generated file records its source file, a digest of
  that source, the schema and version, the EasyCrypt build, and the theory root,
  and states that the exporter and the decoder are in its trust base. The
  EasyCrypt-build field is `n/a` in the exporter's present output, so it
  identifies no installation: an EasyCrypt upgrade is caught by the goldens
  failing on a shifted uniqueness stamp, not by the header.
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

The available evidence for the translation is definitional agreement with
independently proved theorems: in `Examples/FormImport.lean` an imported form's
translation is by `rfl` the statement of a theorem proved from the CatCrypt pRHL
rules alone, and `Examples/OTPEquivImport.lean` does the same for a form decoded
from an exporter fixture rather than written by hand.

## Worked examples

| Example | What it carries end to end |
|---|---|
| `Examples/OTPImport.lean` | the one-time pad as an `EcGame`, lowered to `SPComp Bool`, with perfect indistinguishability as pRHL and then as zero distinguishing advantage |
| `Examples/QFoldImport.lean` | a `q`-round accumulator: the bounded loop and the argument-free call, coupled with the relational loop rule |
| `Examples/ModuleImport.lean` | a concrete module with global state, an adversary parameter, and a functor, with `A{-Otp}` as an emitted `RespectsLocs` hypothesis that the proof consumes |
| `Examples/FormImport.lean` | three statements written as `EcForm` literals, translated, and closed |
| `Examples/OTPEquivImport.lean` | one exporter fixture carrying two games and three statements, decoded, pinned by `#guard`, translated, and closed |
| `Examples/HoareImport.lean` | one exporter fixture carrying a module with global state and four Hoare judgements, decoded, pinned by `#guard`, with the `hoare` judgement translated and closed |
| `Examples/RandomOracleImport.lean` | a lazily-sampled random oracle whose query log is an `EcGlobal` at the code `map int bool`, a type with no `Fintype` instance, with the cached, fresh, uniform-answer and two-query-consistency results proved about the lowered procedure, and an imported `hoare` judgement whose precondition reads that log |
| `Examples/RestrictedImport.lean` | one exporter fixture carrying a section-declared adversary restricted away from a module's memory, with `A{-Otp}` and `islossless A.guess` as emitted hypotheses that two proved theorems consume |
| `Examples/AdversaryEquivImport.lean` | one export carrying three `equiv` judgements over adversary-using experiments, with `={glob A}`, `={glob Otp}` and their conjunction as preconditions; the abstract footprint is a bound variable and its hypothesis carries the coupling through the adversary call |
| `Examples/FunctorGlobImport.lean` | one export carrying an `equiv` preconditioned on `={glob F(A)}`, the footprint of a functor image, which reaches the export as an equality of two tuples mixing the abstract parameter's footprint with the concrete globals the body reads; the componentwise image is the form the two-conjunct source `={glob A, glob Otp}` produces, and both components carry part of the proof |
| `Examples/FunctorImport.lean` | one exporter fixture carrying two functors over one module type, decoded to `EcFunctor`s and pinned by `#guard`, with the statement about the application `Exp(Neg(A))` translated and closed |
| `Examples/Functor2Import.lean` | one exporter fixture carrying a functor of two parameters over two module types, decoded to an `EcFunctorN` and pinned by `#guard`, with two statements translated and closed: one about `Pair(A, B)` at two abstract arguments, whose two `islossless` hypotheses each discharge the call to their own argument, and one about `Pair(A, Key)`, where the second argument is concrete and its losslessness is proved rather than assumed. The same fixture carries a functor whose two parameters share a source name, checked as a rejection |
| `Examples/NonUniformImport.lean` | a game sampling from `dbool \ (fun b => !b)`, the `dexcepted` distribution, with the conditioning identified as a point mass, the lowered game proved constant, and its success probability proved to be one; one exporter fixture carries the uniform distribution, `dunit`, `dmap`, `dcond` and `dexcepted` |
| `Examples/DistrBindImport.lean` | one exporter fixture carrying five games: two whose lambda binder and program variable share a source name, proved to denote different distributions and to be told apart by the binder's uniqueness stamp; and one each for `dlet`, the independent product ``(`*`)`` and `dscale (drestrict …)`, with each lowered game's distribution proved |
| `Examples/OTPGenerated.lean`, `Examples/OTPArgGenerated.lean`, `Examples/NegGenerated.lean` | the emitter's committed output for a game, a module and a functor |

`Examples/OTPEquivImport.lean` also records where the imported precondition sits.
EasyCrypt has no whole-memory equality: `={glob}` is not surface syntax, and
`={glob M}` for a concrete `M` is expanded by the typechecker into one equality
per `var` of `M`, degenerating to `tt = tt` when `M` declares none. The strongest precondition an
EasyCrypt `equiv` over two global-free games can carry is therefore `true`, so
the imported judgement is *incomparable* to the hand-written coupling of
`Examples/OTPImport.lean` — weaker in the precondition and weaker in the
postcondition. The file resolves this by proving one coupling with the
precondition left as a parameter, from which both statements follow.

## Cross-references

- The exporter's coverage, its own golden tests, and its regeneration commands:
  `../ec-export/README.md`.
- Editing notes, invariants and the open work-list: `AGENTS.md` in this
  directory.
- The CatCrypt targets the translation lands on: `CatCryptCore.Relational.Rules`
  (pRHL), `CatCryptCore.Unary.Judgment` (pHL), `CatCryptCore.Crypto.Advantage`,
  and `CatCryptCore.Crypto.EasyCryptBridge`.

# `EasyCryptImport/` — the importer

> **Under construction.** The exporter's schema and the accepted fragment are
> both still changing. The schema version is pinned exactly, so an upgrade of the
> exporter requires a matching change here.

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
EasyCrypt's semantics to CatCrypt's.

The repository root [`README.md`](../../../README.md) is the index. The
reference documents are [`docs/FRAGMENT.md`](../../../docs/FRAGMENT.md) (what
imports and what is rejected), [`docs/TRUST.md`](../../../docs/TRUST.md) (the
trust boundary and the three points at which the lowering degrades), and
[`docs/DESIGN.md`](../../../docs/DESIGN.md) (the pipeline and the module map).
[`AGENTS.md`](AGENTS.md) beside this file carries the editing notes, the
invariants and the open work.

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

`Examples/OTPEquivImport.lean` also records where the imported precondition
sits. EasyCrypt has no whole-memory equality: `={glob}` is not surface syntax,
and `={glob M}` for a concrete `M` is expanded by the typechecker into one
equality per `var` of `M`, degenerating to `tt = tt` when `M` declares none. The
strongest precondition an EasyCrypt `equiv` over two global-free games can carry
is therefore `true`, so the imported judgement is *incomparable* to the
hand-written coupling of `Examples/OTPImport.lean` — weaker in the precondition
and weaker in the postcondition. The file resolves this by proving one coupling
with the precondition left as a parameter, from which both statements follow.

## Commands

Build the importer, the examples and every golden `#guard`:

```
lake build CatCrypt.Crypto.EasyCryptImport.All
```

Import a statement: `formTables` builds the decoding tables from the export's
own modules, `importAxiom` decodes a named lemma to an `EcForm`, and
`importedProp` translates it against a resolution environment binding the
procedures the statement names. `Examples/OTPEquivImport.lean` is the worked
shape.

Import a program by emitting a committed literal: the `EmitMain.lean` command
line is in the root [`README.md`](../../../README.md), and the regeneration
commands for the files under `Examples/` are in [`AGENTS.md`](AGENTS.md).

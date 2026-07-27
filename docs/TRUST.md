# Trust boundary

What an imported definition rests on, what bounds the exposure, and where the
lowering answers with a value rather than failing.

## What is unverified

**The exporter, both decoders and the statement translation are unverified, and
they sit in the trust base of every imported definition.** No theorem relates
EasyCrypt's semantics to CatCrypt's.

A theorem proved about an imported game is a theorem about the Lean game; its
relation to the `.ec` source holds modulo the exporter and the decoder. The
translation of a formula is a definition of intent — it says which CatCrypt
proposition the importer takes an EasyCrypt judgement to mean — and a
mistranslation would produce a well-formed goal about the wrong thing.

## What bounds the exposure

- **Schema pinning.** The envelope's schema name and version are compared for
  exact equality. Exporter drift surfaces as a version mismatch or an unknown
  node discriminator, not as a misparse.
- **No field defaults.** A missing, mistyped or unrecognised field is a decode
  error, never a plausible-looking value.
- **Loud rejection.** Every construct outside the fragment is an error naming
  the construct. The statement fixture's rejections are checked as rejections,
  so a change that let one of them decode to something merely well-typed fails
  the build.
- **Total decoders.** Every decoder is a `def`, not a `partial def`, recursing
  on a JSON size measure.
- **Committed literals are the emitter's output.** For each generated file a
  `#guard` compares the emitter's text with the committed file, read by
  `include_str`. A hand edit to a generated file, or emitter drift, fails the
  build.
- **Provenance headers.** A generated file records its source file, a digest of
  that source, the schema and version, the EasyCrypt build, and the theory root,
  and states that the exporter and the decoder are in its trust base.
- **Statements are goals.** A generated statement is a `def … : Prop`. The
  importer states no imported theorem and introduces no axiom.

### The EasyCrypt-build field

The header's EasyCrypt-build field is the envelope's `ec_hash`, which reads
`dune-build-info` and remains `n/a` under an opam install — every installation
the exporter is expected to run on — so that field identifies no installation.
The exporter now also emits `ec_theories_digest`, a digest over the theory
sources of the installation, which does fingerprint it; the decoder does not
read that field into the header. An EasyCrypt upgrade therefore shows up in the
envelope's theory digest on the export side, and here in the goldens failing on
a shifted uniqueness stamp.

## Where the lowering degrades silently

The lowering is total, and at three points it answers with a value where a
partial function would fail:

- **An unresolved call returns the default value.** `ProcEnv` is total: a
  qualified name the caller did not bind resolves to `SPComp.pure default`
  (`Modules.lean`). A statement resolved against an environment missing one of
  the procedures it names is a well-formed goal about a program that returns
  `default` at that call.
- **A call reached at fuel zero is a no-op.** `lowerStmts` bounds argument-free
  call nesting by a `fuel` argument the caller supplies, and a `call` reached at
  `fuel = 0` lowers to nothing (`Lower.lean`). A fuel below the game's call
  depth drops the rest of the inlining.
- **A valuation read at the wrong type code is the default value.** `Env` is
  dynamically typed, so `Env.read t x` where `x` holds a value of another code
  returns `default` (`Lower.lean`).

All three are properties of the parameters the caller supplies — the fuel and
the resolution environment — rather than of the decoder. A well-formed import
supplies a fuel at least the game's call depth and a binding for every qualified
name the game mentions.

## Evidence for the translation

The available evidence is definitional agreement with independently proved
theorems. In `Examples/FormImport.lean` an imported form's translation is by
`rfl` the statement of a theorem proved from the CatCrypt pRHL rules alone, and
`Examples/OTPEquivImport.lean` does the same for a form decoded from an exporter
fixture rather than written by hand.

The exporter's side of the boundary — its exhaustive-match and loud-failure
discipline, and what it does not export — is `../ec-export/docs/COVERAGE.md`.

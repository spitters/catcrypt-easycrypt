# `EasyCryptImport/` — Agent notes

Editing notes for the EasyCrypt importer. `README.md` in this directory describes
what the importer is and how to run it; this file carries the anti-patterns, the
gotchas, the invariants, and the open work.

## Anti-patterns

- **DO NOT let a decoder default on malformed input.** Every field access is an
  `Except` error naming the field and the node. A default value turns exporter
  drift into a plausible-looking AST, which is how a vacuous import gets made.
- **DO NOT map an out-of-fragment construct to something that merely
  typechecks.** A construct CatCrypt cannot express has no AST constructor at
  all, and the decoder rejects it by name. Mapping `while` to a bounded loop with
  a guessed bound, or a non-uniform distribution to a uniform sample, produces a
  Lean goal about a different program than the source.
- **DO NOT state an imported lemma as a `theorem` or an `axiom`.** An imported
  statement is a `def … : Prop`. An EasyCrypt proof is not a Lean proof;
  asserting the statement would import the claim while pretending to import the
  evidence.
- **DO NOT hand-edit a file under `Examples/` whose header says it is
  generated.** `EmitCheck.lean` compares the committed text with the emitter's
  output; regenerate it with `EmitMain.lean` instead. The regeneration commands
  are in `EmitMain.lean`'s docstring.
- **DO NOT patch EasyCrypt to make the exporter work.** The exporter links
  `easycrypt.ecLib` out of tree. A patched EasyCrypt would make the trust base
  a fork rather than a release.
- **DO NOT reach for `rfl`, `decide` or `simp` on a decoder application.** See
  the next section.

## Gotchas

### `#guard`, not `rfl` — and why the emitter exists

The decoders are well-founded recursive on a JSON size measure, so they have no
kernel-reducible equations. A decoded value cannot be evaluated inside a proof:
`rfl`, `decide` and `simp` all fail on `decodeGame …`, and only `#guard`, which
runs the compiled function, can check the decoder's output. The intrinsically
typed `EcTerm` family carries no `DecidableEq` instance either, so a statement
golden is matched as a fully concrete pattern rather than compared for equality.

The consequence is the reason `Emit.lean` exists: **a proof about an imported
artifact goes through a committed Lean literal**, not through the decoder. The
pipeline runs the decoder at tool time, commits the printed AST, and proves
theorems about the literal, which the kernel does reduce. This mirrors how
`haxpipeT` commits Lean for the Rust frontend.

A fuel-indexed, `rfl`-reducible decoder is the rejected alternative: it puts a
fuel parameter in every statement about an imported artifact, and a fuel
exhaustion is a silent wrong answer rather than a decode error. Do not reopen
this without a reason that addresses both.

### The JSON fixtures are duplicated; `scripts/ec-fixture-sync.sh` compares them

`otp.expected.json`, `otpequiv.expected.json`, `forms.expected.json`,
`hoare.expected.json`, `restr.expected.json`, `functor.expected.json`,
`functor2.expected.json`, `advequiv.expected.json`, `globimg.expected.json`,
`nonunif.expected.json`, `distrbind.expected.json`, `ints.expected.json`,
`maps.expected.json` and `loops.expected.json`
exist twice: in the exporter's
`tests/` directory and in this directory. The Lean side needs a local path because it reads them with
`include_str`. When regenerating a fixture, regenerate **both copies**; a stale
copy stays invisible to the golden `#guard`s, which keep passing against the old
bytes.

`bash scripts/ec-fixture-sync.sh` is what makes that drift loud. It checks three
things: every mirrored golden is byte-equal to the exporter's, traces to an `.ec`
source beside that golden, and is read by an `include_str` here. It reads
`../ec-export` (override with `EC_EXPORT_DIR`) and reports a skip when the
exporter is not checked out. It is not wired into CI.

The exporter's other two fixtures (`globals.expected.json`,
`unsupported.expected.json`) exercise the export side only and have no copy here;
the script reports them as export-side-only rather than failing.

### An EasyCrypt upgrade invalidates the fixtures

An exported identifier carries a uniqueness stamp, which is EasyCrypt's own
identifier tag: a counter over every identifier the process creates, including
those from the required theories. It is reproducible for a fixed EasyCrypt
installation, and only its distinctness carries meaning — but it appears
verbatim in the goldens. **After an EasyCrypt upgrade, regenerate the fixtures
(both copies) and rebuild the Lean guards.** A stamp shift fails the statement
goldens, whose binder resolution reads stamps.

### The rot guard is the only importer

Nothing in `CatCrypt.Crypto` imports this directory. The example modules have no
importer of their own, so `CatCrypt.Crypto.EasyCryptImport.All` is what keeps
them from rotting when the AST, the lowering, the emitter or the CatCrypt core
they target changes. That target is in the CI rot-guard list
(`.github/workflows/ci.yml`); keep it there, and add any new module of this
directory to `All.lean`. Building `All.lean` is also what runs every golden
`#guard`; `All.lean`'s docstring lists the modules that carry them.

### The LSP on `FormJson.lean` and `FormToProp.lean`, and what a blank answer means

Interactive proof-state queries against these two kill the Lean LSP backend —
`lean_goal` on `FormToProp.lean` closes the connection. It is the elaboration a
goal query forces that does not fit; do not retry a dropped call.

**Diagnostics are a different matter, and a blank answer has two causes.**
Against a freshly built tree, `lean_diagnostic_messages` on both files answers
normally and runs their `#guard`s. What looks like a drop —
`success: false` with an empty `items` and an empty `failed_dependencies` — is
the signature of a module whose *imports* are out of date, which is the state
every file downstream of an edited one is in until the next build. So a blank
answer says "rebuild the import", not "this file cannot be checked", and the two
are told apart by whether anything the file imports has been edited.

The consequence for an editing order: a file whose imports are untouched can be
verified through the LSP even while its siblings are dirty, so edit leaves-last
— `Ty.lean`, then `Ast.lean`/`Params.lean`, then `Form.lean`/`Json.lean`, then
`FormToProp.lean`/`FormJson.lean` — and check each one before moving down. What
is left unverifiable that way is checked against a scratch module that *copies*
the new declarations instead of importing them, since its own imports are then
clean.

`FormJson.lean` and `Json.lean` are the two largest files here. Prefer adding a
decoder arm over restructuring the dispatch chain: it is a `String`-keyed
`if`-chain because each arm's field reads must supply the size-measure decrease
proofs — that is what the named match hypotheses are for — and reshaping the
chain re-opens all of them.

## Invariants a future editor must not break

1. **Totality.** Every decoder is a `def`. A `partial def` would make a decode
   loop a hang rather than an error, and would remove the size-measure discipline
   that bounds what the recursion consumes.
2. **Exact schema pinning.** The envelope's schema name and version are compared
   for equality, not for compatibility. Do not add a version range or a
   best-effort upgrade path; bump `schemaVersion` and regenerate.
3. **Rejection is by construct name.** A decode error names the construct and
   says why it has no image. The statement fixture checks rejections *as*
   rejections, so widening the fragment means adding a constructor and a target,
   not relaxing a check.
4. **Type codes stay `Countable`, and finiteness stays a predicate.**
   `EcTy.interp` must carry `Countable`, `Inhabited`, `DecidableEq` and
   `Nonempty`, because a `GLocation` and equality tests require them. Finiteness
   is `EcTy.isFin` plus `EcTy.fintypeOfIsFin`, not a universal instance, and two
   constructs need it: `EcStmt.sample` and `EcDistr.uniform`, each of which is
   uniform on its carrier, takes the proof as an argument, and is rejected by the
   decoder at `int` or at a map. Do not widen that by giving a non-finite code a
   `Fintype`, and do not add a code without the four countable-side instances.
   `EcStmt.sampleD` needs no finiteness, since `NonUniform.sampleFrom` takes an
   arbitrary `SDistr`.
5. **One representation of a global.** `EcGlobal` carries a code and no
   finiteness proof, and denotes the `GLocation` that `EcStmt.load` / `.store`
   and `EcTerm.glob` all read. `EcGlobal.finLoc` is the `Location` view of that
   same cell at a finite code, available for stating a result in the
   finite-typed vocabulary (`lowerStmts_load_finLoc`,
   `lowerStmts_store_finLoc`, `evalTerm_glob_finLoc`); it is a view, justified by
   `Heap.gget_ofLocation` / `Heap.gset_ofLocation`, not a second global type. Do
   not reintroduce a finite-typed global alongside it: a program and a statement
   must mention the same globals, and a second type is what stopped an imported
   statement from naming a countable-typed one.
6. **Structural translation of bounds.** A distinguishing bound translates to an
   absolute difference of two probabilities at the memory the form names. Do not
   route it through `Advantage`, `AdvantageA` or `sdist` — each silently
   strengthens or weakens the statement (fixed initial heap; an unmentioned
   post-composed distinguisher; a supremum over distinguishers and heaps). The
   two named bridges in `FormToProp.lean` are the sanctioned way to reach those
   forms, and they make the extra quantification explicit.
7. **Restrictions are hypotheses, not encodings.** `A{-M}` and `islossless` stay
   as `RespectsLocs` / `ProcLossless` side conditions on the imported statement.
   Encoding them in `ModuleImpl` would make every module carry a proof
   obligation, and would still not express what EasyCrypt's module system
   enforces.
8. **A generated file is byte-equal to the emitter's output.** `emitExpr` prints
   a named argument for every index the result type does not determine; changing
   that printing changes every committed literal, so regenerate them in the same
   change.

## An abstract module reaches the export only through a binder

`ME_Decl`, the module body of an abstract module, is unreachable from the
exporter's top-level lookup, and this is a property of EasyCrypt rather than a
gap in the export. `module A <: T` at the top level is rejected with "use declare
for abstract module"; `declare module A <: T` outside a section is rejected with
"declare module are only allowed inside section"; and a section-local `declare
module` is gone from the environment once the section closes. What survives is
the generalisation: closing the section rewrites every statement that used `A`
into `forall (A <: T{-M}), …`, and the restriction rides on that binder's `gty`,
which is where `jmod_restr` is exercised and where `bindBinder` reads it.

Do not add an exporter path that snapshots the section environment to reach
`ME_Decl` directly. The generalised statement already carries everything the
importer needs — the interface, the restriction, and the hypotheses the section's
`declare axiom`s became — and a section-local module has no top-level path to
name it by.

## `Fglob` always names a module binder, never a concrete module

EasyCrypt's `Fglob` node carries an `EcIdent.t`, so the module it names is a
binder — an abstract module. A concrete module's `={glob M}` is expanded by the
typechecker before the export, into one equality per declared `var` of `M`, each
of which decodes through `EcTerm.glob`. So the reachable footprint comparison is
`EcForm.memEqOnMod`, against the footprint a binder carries, and
`EcForm.memEqOn`, against a list of declared globals, is the arm
`decodeGlobEq` falls back to when the identifier resolves in `modGlobals`
instead. `Examples/AdversaryEquivImport.lean` carries all three shapes from an
export.

`={glob F(A)}` for a functor image is a fourth shape: its footprint mixes the
abstract parameter's, which stays a `Fglob`, with the concrete globals the body
reads, which are expanded, so the export carries an equality of two `Ftuple`s.
`globTupleEqPair` intercepts it — a `glob M` read in a component is what tells it
from an equality of two data tuples, since `glob M` has no type code — and
`decodeGlobTupleEq` compares the components pairwise, each by the decoder its own
shape already has, conjoining them in the tuple's order. That image is the form
`={glob A, glob M}` produces, which is what makes the two source spellings of one
precondition have one image; `Examples/FunctorGlobImport.lean` carries both
spellings from an export and checks them against a single shape predicate. Do not
route the tuple to `agreeOn (L ∪ globLocs gs)` instead: `agreeOn` compares raw
`Finmap` lookups where the expanded component compares `Heap.gget` values, so the
union is a strictly stronger precondition and hence a weaker imported statement.

Since an abstract module declares no globals, the footprint is a **second bound
variable of the module quantifier** — `EcForm.allModOn` and
`EcForm.allModRestrOn`, chosen over the plain binders exactly when the body's
`EcForm.namesGlobOf` says the statement names `glob A`. The hypothesis
`ModuleRespectsOn L M` is what says `M` lives on `L`; do not replace the
precondition `agreeOn L` with `agreeOff` of the restricting module's footprint,
which is a stronger relation and so gives a weaker imported statement.

## `EcForm.memEq` has no exporter source

`EcForm.memEq` — the two memories are equal — cannot be produced by any decoder,
and no `.ec` source produces it. EasyCrypt has no whole-memory equality: `={glob}`
is a parse error, and `={glob M}` names one module's footprint. The constructor
is reached from hand-written `EcForm` literals, which is how
`Examples/FormImport.lean` uses it: a relational judgement about heap-carrying
programs needs whole-heap equality on both sides, and that shape has no exporter
source.

The precondition an imported judgement carries is not the one a hand-written
coupling assumes, and the two do not order. EasyCrypt has no whole-memory term:
`={glob M}` is typechecker-expanded into one equality per declared `var` of `M`,
so for a global-free module it degenerates to `true`. An imported `equiv` over
global-free games therefore carries the precondition `true` and a results-only
postcondition, while a hand-written CatCrypt coupling assumes `eqPre` and
concludes `eqPost` — results **and** final heaps equal. The two are
**incomparable**: the imported one applies to more initial pairs and concludes
less, so neither is an instance of the other.

State the coupling at a parametric precondition and both fall out.
`CatCryptCore.Relational.Frame.r_frame_of_preservesNothing` frames **any**
precondition across computations that modify nothing, which a global-free game
is; `Examples/OTPEquivImport.lean` is the worked instance. `r_frame_local` is not
the lemma to reach for: it wants `DependsOn Frame L` with `L : LocSet =
Finset Nat`, and `eqPre` has no finite footprint.

## A global read is not matchable in a `#guard`; read it back instead

`EcTerm.glob g m : EcTerm g.ty` is indexed by a **projection out of its own
field**, not by a field. Any `match` that reaches it at a fixed index — a pattern
under `EcForm.holds`, a pattern under `EcForm.eqT` whose sibling operand fixes the
index, or a function on `EcTerm .bool` — makes the dependent pattern matcher solve
`EcTy.bool = g.ty` with `g` a fresh variable, and it fails with "Dependent
elimination failed". `EcStmt.store g e` types `e` at `g.ty` and `EcProcAt s` types
`ret` at `s.res`, so those two fields have the same problem.

The way through is a recognizer whose own `match` **quantifies** the index, which
turns the same equation into an assignment. Four exist and the golden `#guard`s use
them: `EcTerm.globRead`, `EcTerm.litValue` (`Form.lean`), `EcExpr.litValue`,
`EcExpr.varName` (`Ast.lean`), with `isGlobReadAt` and `isBoolLit` in
`FormJson.lean` wrapping the first pair for a guard. Reach for one of these rather
than weakening a guard to a wildcard; if a new leaf needs the same treatment, add
the recognizer beside them.

## A distribution binder is keyed by its whole identity; a module binder by its name

`Env` is keyed by `EcVarId`, a source name together with an `Option Nat` stamp. A
program variable — `PVloc`: a formal parameter, a declared local, an assignment
target — has no stamp; an `EcIdent`, which is what a distribution operator's lambda
binder and its occurrences are, carries the stamp the exporter writes, and
`getStampedIdent` reads both fields. `EcVarId.ofName` is the program-variable
identity and `Coe String EcVarId` is that function, so every `String` variable name
in the AST — `EcStmt.assign`'s target, `EcProcAt.param`, `EcTerm.var`,
`FormEnv.bindVar` — reaches the valuation through it, while `EcExpr.var` and the
four distribution binders carry the identity itself.

The two namespaces therefore cannot alias, which is what `Env.read_update_stamped`
says: extending the valuation at a stamped identifier leaves the program variable
of that identifier's source name readable. `Examples/DistrBindImport.lean` carries
the export the property is about — a lambda binder written with a program
variable's source name — and states it as `lowerClosedGame_freeGame`, over a binder
of *any* source name, together with `freeGame_shadowed_ne_boundGame`, the two games
a name-keyed valuation identifies and which denote different distributions.

Two other binders are still read by their source name alone, and each rejects a
collision rather than resolving one. A logical variable of a formula is bound by
name in `FormJson.lean`, which rejects a binding whose name another live stamp
already carries. A module binder — a functor's parameter, an abstract module — is
named by the cross-path a call writes, which carries no stamp; the section below
on functor parameters is where that lands.

## A functor's parameters are told apart by their source names only

The export lists a functor's parameters in declaration order, each an identifier
together with the module type it must implement, and a call to the parameter `X`'s
procedure `p` inside the body is the cross-path `X./p`. The name is therefore the
whole of what a call resolves against, and `lowerParamsX` binds each parameter
with `ProcEnv.bindModuleX` under its own name — `xqualify`, not `qualify`, since a
decoded body writes cross-paths. Binding one parameter under the wrong prefix
leaves its calls resolving against `ProcEnv.empty`, which answers with the default
value rather than failing.

EasyCrypt does not reject two parameters of the same source name, and the export
then carries two `params` entries named alike while the body's call stays the bare
cross-path. `decodeParamsN` rejects that, for the reason the distribution-binder
section above gives: the name is read without its stamp, so one binder would
shadow the other and the export says nothing about which the call means.

`EcParams`, `EcFunctorN`, its lowering and its decoder sit together in
`FunctorN.lean` rather than split across `Ast.lean` / `Lower.lean` / `Json.lean`
the way `EcFunctor` is.

The lowering is curried — `EcParamsFn` builds the type
`ModuleImpl I₁ → … → ModuleImpl Iₙ → ModuleImpl body.interface` — so that
application is Lean application and a functor of one parameter is definitionally
`Lower.lowerFunctorX` (`lowerFunctorNX_toN`). A single argument holding a tuple of
modules is the rejected alternative: the tuple is a nested product to build and
destructure at every call site, it has no partial application, and it makes the
one-parameter case a different function from the existing one.

## An abstract operator is a parameter; a finiteness assertion is not a hypothesis

A theory-level `op f : T.` without a definition (`Th_operator` with body kind
`Abstract`) registers in `DecodeTables.absOpPaths` at the signature its type gives
it, a read of it decodes to `EcTerm.opApp`, and `EcForm.allOp` quantifies the
statement over the realization. The realization environment is `OpEnv`
(`Params.lean`): `ProcEnv` with the monad deleted, so arity rides on `EcSig`'s
right-nested product and nullary constants, abstract predicates (`s.res = bool`)
and abstract distributions (`s.res = distr t`) are one mechanism. Adding a shape
means extending `decodeThOperatorAbstract`, not adding an AST node.

Two rules on it:

- **`OpEnv` is total, so the binders are what keep a statement away from the
  default.** An unbound path answers with the canonical inhabitant of its result
  code, which is not the operator's meaning. `EcForm.opsOf` collects the operators
  a statement reads without binding, `EcForm.assembleParams` binds exactly those,
  and a `#guard` per statement checks `opsOf` of the assembled form is empty. Do
  not emit a statement without that check.
- **Do not import `Top.Finite.finite_type` or a `card` axiom as a `Finite` /
  `Fintype` / `Nonempty` hypothesis on a fixed-carrier opaque code.** At the `Int`
  carrier such a claim is refutable, so a theory carrying it has an unsatisfiable
  hypothesis set and every imported statement of that theory holds vacuously —
  the shape that made nine `SurfaceDeps` `*_extracted_uc` theorems assert nothing.
  A finiteness assertion stays a decode rejection while the carrier is fixed; the
  route that makes it a theorem rather than an assumption is a cardinality
  parameter (`EcTy.fin n` at a variable `n`), which also gives `card = n` by
  `Fintype.card_fin`.

An imported `axiom` and an imported `lemma` are different roles, and
`decl.axiom_kind` is the discriminator: an `Axiom` item is a hypothesis the
theory's statements are proved under, so its image is a proposition at a supplied
realization (`importedPropWithOps`), while a `Lemma` item is a goal, whose image
closes over its operators (`importedProp` of the assembled form). Closing an
`Axiom` item over its operators states something the theory does not:
`Examples/PRFParamImport.lean` carries both readings of one item and the proof
that the closed one is refutable. A theory whose imported hypotheses are exhibited
at one realization — that module's `PRFData.pointMassLaws` — is a theory whose
statements are not vacuous; a theory without such a witness has no such assurance.

## A subtype's inhabitation is a proof, never an instance you postulate

`subtype t = {x : c | P x}` exports as a `Th_type` whose `decl.subtype` carries the
carrier, the predicate, and (schema 8) `nonempty`, a `{path, axiom_kind}` reference
to the `exists x, P x` obligation the declaration's `Top.Subtype` clone left in the
environment. There is no witness in the export and there cannot be one: EasyCrypt
keeps the obligation's statement and discards its proof.

Three rules follow, and each is enforced by a decoder or a code shape.

- **Never postulate `Inhabited` or `Nonempty` for a decoded type.** At an empty
  subtype such an instance proves `False`, and every theorem of the file is then
  worthless. `interpInhabited` stays total and constructive: `EcTy.intRange lo hi`
  carries `lo < hi` and its inhabitant is `⟨lo, _⟩`, so a code that cannot be built
  cannot enter `EcTy` in the first place.
- **A declaration whose `nonempty` does not resolve is a decode rejection.**
  `decodeThTypeSubtype` checks the reference before it looks at the predicate, and
  its message names what assuming inhabitation would cost. 16 of the corpus's 30
  integer-carrier declarations are in this class (a clone-copied `tydecl` whose own
  namespace holds no obligation); they stay rejected.
- **The code is a function of the theory's parameters.** Every corpus predicate
  bounds its carrier by a *declared operator* (`{x : int | 0 <= x < p}` for
  `op p : int.`), so no closed `EcTy` denotes the subtype and the decoder produces
  the declaration — carrier, range, obligation path — rather than a code. The code
  is supplied at the instantiation with `DecodeTables.withSubtype`, and its `lo <
  hi` is discharged from the theory's imported hypotheses (`axiom ge2_p : 2 <= p.`)
  by `omega`. `Examples/ZModPSubtypeImport.lean` is the worked case. Do not add a
  branch that registers the bare carrier under the subtype's name: a statement at
  the carrier is a statement about a different type.

`axiom_kind: "Lemma"` on the reference does not say the obligation was discharged —
the exporter runs with proof checking off, and an `admit` is indistinguishable from
a proof — so the reference locates the statement and the Lean proof is the
evidence.

## Widening the distribution fragment

`EcDistr` covers the uniform distribution, `dunit`, `dmap`, `dcond`, `dlet`,
``(`*`)``, `dscale` and `drestrict`, and `dexcepted` reaches it as `dcond` at the
negated predicate — the definition `Dexcepted.ec` gives it. Adding an operator
means all four of: a constructor in `Ast.lean`, an arm of `evalDistr` in
`Lower.lean` against a definition of the `SDistr` it denotes, an `EcDistrOpKind`
and a `decodeDistr` arm in `Json.lean` with the operator's theory path in
`ecPrelude`, and an `emitDistr` arm with a round-trip `#guard` in
`EmitCheck.lean`. The theory paths are qualified by the inner theory an operator
sits in — `Top.Distr.MUnit.dunit`, `Top.Distr.DConditional.dcond` — so read the
path off an export rather than guessing it from the source name; ``(`*`)`` exports
as `` Top.Distr.`*` ``, backquotes included.

`dlet` is the arm with a second recursive position under a binder, and
`decodeLambdaHeader` is what serves it: it returns the binder, the body node and
the proof that the body is smaller on the `jsonSize` measure, so `decodeDistr` can
descend into the body. `decodeLambda1` is that header followed by `decodeExpr`.
Reach for the header rather than opening a mutual block.

The operators outside the fragment are `dnull`, `dbiased`, `dbin`, `duniform`
over a list, `dlist`, `dfun`, `dopt`, `dfold` and `dinter`. `dbiased` and `dbin`
take a real-valued argument in an expression position and `EcExpr` has no real
code — reals reach the importer only as probabilities, at the statement layer. The
rest need a list, an option or a function type, none of which `EcTy` has.
`dnull`'s image (a sub-distribution of mass zero) exists, and it is excluded
because it names a distribution no EasyCrypt game samples from.

## Open work

- **`EcForm.memEq` is unreachable from any decoder.** See the section above; it
  is exercised only from hand-written literals. `EcForm.memEqOn`, the footprint
  comparison against declared globals, is in the same position: `Fglob` names a
  binder, so the reachable comparison is `EcForm.memEqOnMod`.
- **A module defined as an application of a functor does not decode.** `module G
  = F(M)` and `module G (X : I) = F(X, M)` both export with the body kind
  `ME_Alias`, and the alias carries the applied path as a string with no body
  behind it, so `decodeStructureBody` rejects the node by its body kind. Decoding
  one means resolving the target path against the export's own items, which is a
  name-resolution pass the decoder does not have. The image a *statement* names is
  a separate matter and is already supplied by the caller through
  `FormEnv.functorImages`.
- **`Emit.lean` has no `EcFunctorN` arm.** `emitFunctor` prints an `EcFunctor`, so
  a committed literal exists for a functor of one parameter only; a functor of
  several parameters is reached through the decoder and through a hand-written
  literal in an example, not through the emitter.
- **A functor image is named by the caller, not by the decoder.** A statement
  that applies a functor to the module it binds names the image `F(A)` by a path
  of its own, and nothing in the exported statement carries the body behind that
  path. The image is supplied through `FormEnv.functorImages`: instantiating the
  module binder applies a caller-supplied extension to the resolution
  environment, which is where the image's procedures are bound. With a decoded
  functor that extension is the functor applied to `ProcEnv.moduleX` at the
  binder's name, rather than a hand-written game.
- **The exporter repository has no CI.** Its golden tests are run by hand, and
  `scripts/ec-fixture-sync.sh` is not wired into this repository's CI either, so
  a change there is caught here only when somebody runs one of the two.
- **Complexity and cost annotations have no target.** There is no `SPComp`-level
  query counter or running time, so an imported concrete-security statement that
  depends on `q_H` or on a running time loses that dependence. This is a gap in
  what can be stated, not a hypothesis that could be supplied.

## Cross-references

- Fragment, pipeline, commands, trust boundary: `README.md` in this directory.
- Exporter coverage, its unsupported-node list, and its golden regeneration:
  `../ec-export/README.md`.
- The pRHL and pHL rules an imported goal is closed with:
  `CatCryptCore.Relational.Rules`, `CatCryptCore.Unary.Rules`.
- The tactic surface available for closing imported goals:
  `CatCrypt/Tactics/AGENTS.md`.

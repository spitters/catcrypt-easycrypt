# Fragment

What imports, what does not, and why each rejected construct has no image.

This describes the **decoder**: what a JSON export produced by `ec-export` turns
into, node by node. The AST is wider in places than the decoder reaches, and
where the two differ it is the decoder that says what an import can produce.

The accepted fragment is smaller than what the exporter emits. Every construct
outside it is rejected by name, with a decode error carrying the construct and
the reason. None is silently degraded to something weaker that merely
typechecks.

## Programs

| Layer | Fragment |
|---|---|
| Types | `unit` and `bool` (`Top.Pervasive.unit` / `.bool`), `int` (`Top.Pervasive.int`), a tuple type of any arity above one (an arity above two decodes as the right-nested binary product), a finite scalar type of a cardinality the ingestion's table records (`fin n`, interpreted as `Fin n`), a finite map (`Top.FMap.fmap` at its two type arguments, interpreted as an association list), `option` and `list` at any decoded argument, and an abstract type declaration (`type t.`), which decodes as an opaque code at a fixed carrier — distinct declared paths stay distinct codes, and a theorem about the imported program is a theorem at that instantiation. `EcTy.isFin` marks the finite subset — `unit`, `bool`, `fin n`, products of finite codes, and `option` of a finite code — which is where uniform sampling and a `Location` live. `fset` at any decoded element code (interpreted as `Finset`, so set equality decodes at the quotient and two insertion orders are equal; emission prints a canonical representative sorted by printed form); and a parameter-free `Concrete` type alias, registered at its decoded right-hand code. A subtype declaration is rejected: the export carries the carrier and the predicate but no inhabitation witness, and a predicate over an abstract constant has no code-level decision procedure — importing the bare carrier under the subtype's name would quantify theorems over a strictly larger type. Any other type path is rejected by path |
| Expressions | a local variable read; a boolean, unit, integer or finite-scalar literal; the empty finite map (`Top.FMap.empty`); negation, conjunction and exclusive-or; decidable equality at any type code; pair construction and projection; wrapping addition on `fin n`; integer addition (`Top.CoreInt.add`) and comparison (`Top.CoreInt.le`); binding a key in a finite map (`_.[_<-_]`) and testing membership (`Top.FMap.dom`, which is what `k \in m` unfolds to). Disjunction and implication decode through their de Morgan images, and the strict integer order (`Top.CoreInt.lt`) through the negation of the reversed `≤` |
| Map lookup | `m.[k]` returns an option and `EcTy` has no option code, so it decodes only inside `oget m.[k]` or `odflt d m.[k]`, each to `EcExpr.mapGetD`. `oget`'s default is the value type's canonical inhabitant, which fixes the value EasyCrypt leaves open as `witness`; `odflt`'s is the one the source writes. The lookup on its own, and `oget` of anything else, are rejected |
| Distributions | the uniform distribution at a finite code, `dunit`, `dmap`, `dcond`, `dlet`, the independent product ``(`*`)``, `dscale`, `drestrict`, and `dexcepted` (`d \ X`), which is `dcond` at the negated predicate — its own EasyCrypt definition. A distribution operator whose argument is a function carries the binder's identity — its source name together with EasyCrypt's uniqueness stamp — and the body is evaluated in the local valuation extended at that identity |
| Statements | local assignment, uniform sampling at a finite code, sampling from a distribution expression, global read and write at any code, the conditional, the bounded `while` idiom below, an argument-free intra-module call (inlined under a depth bound), and a call `x <@ q(a)` at a signature resolved against the ambient environment |
| Memory | a local variable is a meta-level valuation entry keyed by its identity — a program variable by its source name, a bound identifier by that name together with its uniqueness stamp — so a local assignment is functional rebinding and a binder cannot capture an occurrence of another identifier of its name; a module-scoped `var` is an `EcGlobal` at a CatCrypt `GLocation`, read and written by `SPComp.gget` / `SPComp.gset`, at every type code. At a finite code that cell is also a `Location` read and written by `SPComp.get` / `SPComp.set` (`lowerStmts_load_finLoc`, `lowerStmts_store_finLoc`) |
| Modules | concrete modules with global state, module types, functors of any number of parameters (a curried Lean function on `ModuleImpl`s, one argument per parameter), and abstract modules — an adversary or oracle given only by its interface — as `ModuleImpl` parameters, so an imported game quantified over all adversaries is a Lean `∀ (A : ModuleImpl I), …` |

## Loops

EasyCrypt has no `for`, and `EcStmt.forN n body` carries an iteration count and
no counter, so a `Swhile` node decodes only at the shape whose iteration count
the block around it determines. All four conditions are required:

| Condition | |
|---|---|
| the guard is `i < n` | `i` a program variable, `n` an integer literal |
| the statement immediately before the loop is `i <- c` | `c` an integer literal |
| the last statement of the body is `i <- i + 1` | or `i <- 1 + i` |
| no other statement of the body writes `i` | and every one of them has a write set the statement itself determines |

The image is `i <- c` followed by `EcStmt.forN (n - c).toNat body`, with the
increment left in the body: the loop runs the body once per value of `i` in
`[c, n)` and leaves `i` at `max c n`, which is what the source does. When
`c ≥ n` the count is zero, as the guard is.

A loop that differs in any one respect is a decode error naming that respect.
Each of these is rejected: a guard whose bound is a program variable; a guard
under `<=`, which runs one iteration more than the recognised `<`; a loop whose
preceding statement assigns to another variable, or is not an integer-literal
assignment at all, or does not exist because the loop opens its block; a body
whose last statement is not the increment; a body that writes the counter
anywhere else; and a body containing an argument-free `call`, which runs a
procedure body in the caller's valuation, so the call site does not determine
whether the counter is among its writes.

## Statements

| Layer | Fragment |
|---|---|
| Terms | logical variables, literals — including an integer literal at the `int` code — a module global read at a memory (`g{&m}`), and the result of the enclosing judgement (`res{1}`, `res{2}`, `res`). The boolean operators, equality, pairs and projections, `if` and `let` are terms; integer arithmetic is not, so `res = 0` is a term and `res + 1 = 1` is not |
| Probabilities | `Pr[q(arg) @ &m : ev]`, constants, a probability parameter, sum, product, absolute difference |
| Formulas | the first-order skeleton, quantifiers over a type code, a memory, a probability parameter or a module type, term and memory equality, agreement of two memories on a module's footprint (`={glob M}`), `if`, `let` |
| Judgements | the procedure-level `hoare`, `bd_hoare` and `equiv`, and probability comparisons |

A distinguishing bound translates structurally, to an absolute difference of two
probabilities at the memory the source names — not to `Advantage`, `AdvantageA`
or `sdist`, each of which would change the statement (respectively by fixing the
initial heap, by post-composing an unmentioned distinguisher, and by taking a
supremum over distinguishers and heaps). Two named bridges in `FormToProp.lean`
say what extra quantification reaches those forms.

## Module restrictions

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

## Rejected constructs

| Construct | Reason |
|---|---|
| The distribution operators outside `EcDistr` (`dnull`, `dbiased`, `dbin`, `duniform` over a list, `dlist`, `dfun`, `dopt`, `dfold`, `dinter`) | a distribution operator outside the ingestion's `distrOpPaths` table cannot decode to a sample. `dbiased` and `dbin` take a real-valued argument in an expression position, and reals reach the importer only as probabilities; the rest need a list, an option or a function type, none of which `EcTy` has |
| A distribution operator's function argument given other than as a one-binder lambda | `EcDistr`'s binder is a variable name; a predicate supplied as an operator, a composition, or a lambda of several binders has no image |
| A `while` loop outside the idiom above | `EcStmt.forN` carries an iteration count, and outside that shape the guard, the body and the statement before the loop do not determine one |
| The finite-map lookup `m.[k]` on its own | it returns an option, and `EcTy` has no option code; it decodes under `oget` or `odflt`, whose result is a value |
| Integer arithmetic in a formula term | `EcTerm` has no integer addition or comparison; an integer literal is a term, and an applied integer operator is rejected by path |
| Uniform sampling at a non-finite code | `SPComp.sample` is uniform over its carrier, so `EcStmt.sample` and `EcDistr.uniform` each carry a proof that the code is finite and the decoder rejects a uniform sample at `int` or at a map. A non-uniform distribution at a non-finite code is in the fragment, since `sampleFrom` needs no finiteness |
| Complexity and cost annotations | there is no `SPComp`-level query counter or running time to state them against. An imported concrete-security statement that depends on `q_H` or on a running time loses that dependence |
| Statement-level judgements (`hoare{ s }`, `equiv{ s₁ ~ s₂ }`) and assertions over procedure locals | their assertions range over local variables, and locals are meta-level in the lowering, so there is nothing for such an assertion to denote |
| Expectation-Hoare and eager/lazy judgements | CatCrypt has no corresponding judgement |
| Higher-order quantification over operators or distributions, and `glob M` in value position | the quantifiers range over a type code, a memory, a probability or a module type; a footprint is available as one side of a comparison, not as a value |
| General real terms, including a quotient bound such as `q / 2^n` | reals appear only as probabilities |
| Signed subtraction of probabilities | probabilities translate into `ℝ≥0∞`, where subtraction is truncated, so a difference EasyCrypt allows to be negative has no faithful image. The bound shapes EasyCrypt statements use, `\|Pr[A] − Pr[B]\| ≤ ε` and `Pr[A] ≤ Pr[B] + ε`, are in the fragment |
| A module defined as an application of a functor, `module G = F(M)` or `module G (X : I) = F(X, M)` | its body is an `ME_Alias` whose target is the applied module path as a string, with no body behind it; the export's `arity` says how many of the node's parameters the alias binds itself and how many are the target's residual ones. The image a statement names is supplied by the caller through `FormEnv.functorImages` |
| Two parameters of one functor sharing a source name, `module F (P : I) (P : J)` | EasyCrypt permits it, and a call inside the body is the cross-path `P./p`, which carries no stamp; binding both under that prefix would make one shadow the other |
| Pattern matching, `let` over a tuple pattern, tuple expressions of arity above two (tuple types decode; the expression and projection forms stay binary), procedures with more than one formal parameter, an identifier reduced to a name without its uniqueness stamp | each has no image in the AST, and truncating a stamp would make two distinct binders of the same source name alias |

Widening the fragment means adding a constructor and a target, not relaxing a
check: [`CatCrypt/Crypto/EasyCryptImport/AGENTS.md`](../CatCrypt/Crypto/EasyCryptImport/AGENTS.md)
records what each addition touches, and the exporter's own coverage — what
reaches this decoder at all — is `../ec-export/docs/COVERAGE.md`.

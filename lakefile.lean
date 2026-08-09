import Lake
open Lake DSL

package catcryptEasycrypt where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib CatCrypt where
  -- Module root `CatCrypt.*`, the same root the importer occupies in the CatCrypt
  -- development, so a consumer's `import CatCrypt.Crypto.EasyCryptImport.*` lines
  -- resolve unchanged. The glob spans every module in this package: the importer
  -- subtree `CatCrypt/Crypto/EasyCryptImport/`, and the `CatCryptCore.*` re-export
  -- shims it imports (`CatCrypt/Core/GenHeap`,
  -- `CatCrypt/NonUniform/{Conditional,Product,UnaryRules}`). A `require` on
  -- `catcryptCore` supplies the `CatCryptCore.*` module names alone, so the shims
  -- that carry the `CatCrypt.*` names are part of this library.
  globs := #[.submodules `CatCrypt]
  -- `-E <kind>` reports Lean messages of that kind as errors. `hasSorry` is the
  -- kind Lean attaches to a declaration whose proof term reaches `sorryAx`, so
  -- building this library refuses such a declaration outright and no separate
  -- step has to read the build's output. The word in a comment, a docstring or a
  -- string literal carries no such message and is unaffected, and a declaration
  -- that reaches `sorryAx` through a tactic carries one even though the word
  -- appears nowhere in its source.
  moreLeanArgs := #["-E", "hasSorry"]

-- The CatCrypt methodology basis: `SPComp`, sub-distributions, the pRHL and pHL
-- rule sets, `Advantage`, the generic heap, and non-uniform sampling — the targets
-- the lowering and the statement translation land on.
--
require catcryptCore from git
  "https://github.com/spitters/CatCrypt-core.git" @ "0.1.0-alpha.5"

-- `HaxLean.JsonSize`: the JSON size measure the two decoders recurse on, which is
-- what makes them total `def`s rather than `partial def`s.
require «hax-lean» from git
  "https://github.com/spitters/hax-lean.git" @ "v0.1.0-alpha.1"

-- mathlib LAST so its proofwidgets/aesop versions win on conflicts;
-- this is required for `lake exe cache get` to find oleans.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.30.0"

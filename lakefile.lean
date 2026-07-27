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

-- The CatCrypt methodology basis: `SPComp`, sub-distributions, the pRHL and pHL
-- rule sets, `Advantage`, the generic heap, and non-uniform sampling — the targets
-- the lowering and the statement translation land on.
--
require catcryptCore from git
  "https://github.com/spitters/CatCrypt-core.git" @ "0.1.0-alpha.2"

-- `HaxLean.JsonSize`: the JSON size measure the two decoders recurse on, which is
-- what makes them total `def`s rather than `partial def`s.
require «hax-lean» from git
  "https://github.com/spitters/hax-lean.git" @ "v0.1.0-alpha.1"

-- mathlib LAST so its proofwidgets/aesop versions win on conflicts;
-- this is required for `lake exe cache get` to find oleans.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.30.0"

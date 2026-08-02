/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.EasyCryptImport.Json

/-!
# Generated EasyCrypt import: Neg

This file is generated from an EasyCrypt export by `emitFile`
(`CatCrypt/Crypto/EasyCryptImport/Emit.lean`). Regenerate it rather than
editing it.

* source: `tests/functor.ec`
* source_digest: `38fe427f5f4d6e55efc2bd6a03dd2cd8`
* schema: `catcrypt-ec-export` version 10
* EasyCrypt build: `n/a`
* theory root: `Top`

The EasyCrypt exporter that produced the JSON and the ingestion that
decoded it are unverified, and both are in the trust base of the
declarations below: no theorem relates the source file to the AST literal
here.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.EasyCryptImport.Generated

/-- The procedures the imported module `Neg` declares. -/
def negFunctorBodyProcs : List (String × SigProc) :=
  [
    ("guess",
      { sig := (EcSig.mk EcTy.bool EcTy.bool)
        proc := EcProcAt.mk ["c"]
          [ (EcStmt.callProc "P./guess" (EcSig.mk EcTy.bool EcTy.bool) (EcExpr.var EcTy.bool "c") "b") ]
          (EcExpr.bnot (EcExpr.var EcTy.bool "b")) })
  ]

/-- The imported EasyCrypt module `Neg`. -/
def negFunctorBody : EcModule where
  name := "Neg"
  interface :=
    { names := ["guess"]
      sig := fun p => (sigProcOf negFunctorBodyProcs p).sig }
  globals := []
  procs := fun p => (sigProcOf negFunctorBodyProcs p).proc

/-- The imported EasyCrypt functor `Neg`. -/
def negFunctor : EcFunctor where
  name := "Neg"
  paramName := "P"
  paramInterface := (interfaceOfSigs [("guess", (EcSig.mk EcTy.bool EcTy.bool))])
  body := negFunctorBody

end CatCrypt.Crypto.EasyCryptImport.Generated

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.EasyCryptImport.Ast

/-!
# Generated EasyCrypt import: OTP0

This file is generated from an EasyCrypt export by `emitFile`
(`CatCrypt/Crypto/EasyCryptImport/Emit.lean`). Regenerate it rather than
editing it.

* source: `tests/otp.ec`
* source_digest: `e73f3b1113795b06a4132a39950a0a3d`
* schema: `catcrypt-ec-export` version 4
* EasyCrypt build: `n/a`
* theory root: `Top`

The EasyCrypt exporter that produced the JSON and the ingestion that
decoded it are unverified, and both are in the trust base of the
declarations below: no theorem relates the source file to the AST literal
here.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.EasyCryptImport.Generated

/-- The imported EasyCrypt game `OTP0`. -/
def otp0Game : EcGame where
  name := "OTP0"
  locals := ["k", "c"]
  procs := []
  body :=
    [ (EcStmt.sample EcTy.bool "k"),
      (EcStmt.assign EcTy.bool "c" (EcExpr.bxor (EcExpr.var EcTy.bool "k") (EcExpr.lit (t := EcTy.bool) false))) ]
  ret := (EcExpr.var EcTy.bool "c")

end CatCrypt.Crypto.EasyCryptImport.Generated

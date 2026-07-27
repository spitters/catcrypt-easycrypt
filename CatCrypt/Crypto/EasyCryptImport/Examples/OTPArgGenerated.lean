/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.EasyCryptImport.Json

/-!
# Generated EasyCrypt import: OTPArg

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

/-- The procedures the imported module `OTPArg` declares. -/
def otpArgModuleProcs : List (String × SigProc) :=
  [
    ("main",
      { sig := (EcSig.mk EcTy.unit EcTy.bool)
        proc := EcProcAt.mk "_"
          [ (EcStmt.callProc "Top.OTPArg./enc" (EcSig.mk EcTy.bool EcTy.bool) (EcExpr.lit (t := EcTy.bool) true) "r") ]
          (EcExpr.var EcTy.bool "r") }),
    ("enc",
      { sig := (EcSig.mk EcTy.bool EcTy.bool)
        proc := EcProcAt.mk "m"
          [ (EcStmt.sample EcTy.bool "k"),
            (EcStmt.ite (EcExpr.var EcTy.bool "m") [(EcStmt.assign EcTy.bool "c" (EcExpr.bxor (EcExpr.var EcTy.bool "k") (EcExpr.lit (t := EcTy.bool) true)))] [(EcStmt.assign EcTy.bool "c" (EcExpr.var EcTy.bool "k"))]) ]
          (EcExpr.var EcTy.bool "c") })
  ]

/-- The imported EasyCrypt module `OTPArg`. -/
def otpArgModule : EcModule where
  name := "OTPArg"
  interface :=
    { names := ["main", "enc"]
      sig := fun p => (sigProcOf otpArgModuleProcs p).sig }
  globals := []
  procs := fun p => (sigProcOf otpArgModuleProcs p).proc

end CatCrypt.Crypto.EasyCryptImport.Generated

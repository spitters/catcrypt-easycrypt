/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.EasyCryptImport.Examples.OTPEquivImport

/-!
# Generated EasyCrypt import: otp_equiv

This file is generated from an EasyCrypt export by `emitStatementFile`
(`CatCrypt/Crypto/EasyCryptImport/EmitForm.lean`). Regenerate it rather
than editing it.

* source: `tests/otpequiv.ec`
* source_digest: `e13d8a393739592d16eae1c89d887ddd`
* schema: `catcrypt-ec-export` version 10
* EasyCrypt build: `n/a`
* theory root: `Top`

The EasyCrypt exporter that produced the JSON and the ingestion that
decoded it are unverified, and both are in the trust base of the
declarations below: no theorem relates the source file to the AST literal
here.

The statement itself is not asserted: an EasyCrypt proof is not a Lean
proof. The declarations below are the imported proposition and its shallow
reading, together with the equation between the two.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.EasyCryptImport.Generated

open CatCrypt.Crypto.EasyCryptBridge

/-- The imported statement, as the translation defines it. -/
noncomputable def otpEquivStatement : Prop :=
  importedProp OTPEquivImport.otpEnv OTPEquivImport.otpEquivForm

/-- The shallow reading of that statement, derived from the form. -/
theorem otpEquivStatement_eq :
    otpEquivStatement =
      pRHL (fun _ _ => True) (lowerClosedGame (OTPImport.otpGame false)) (lowerClosedGame (OTPImport.otpGame true)) (fun r₁ _ r₂ _ => r₁ = r₂) :=
  rfl

end CatCrypt.Crypto.EasyCryptImport.Generated

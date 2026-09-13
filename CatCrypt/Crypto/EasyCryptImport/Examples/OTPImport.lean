/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.EasyCryptImport.Lower
import CatCryptCore.Relational.Rules
import CatCryptCore.Crypto.Advantage
import CatCryptCore.Crypto.EasyCryptBridge
import CatCryptCore.Prob.XorBij

/-!
# Worked example: importing the one-time-pad indistinguishability game

This module carries one EasyCrypt-style game through the importer end to end: it
encodes the one-time pad as an `EcGame`, lowers it to `SPComp Bool`, and proves
perfect indistinguishability of the two message variants — first as a pRHL
judgment `rHoare eqPre G₀ G₁ eqPost`, then lifted to zero distinguishing
advantage via `advantage_zero_of_rHoare`.

The imported EasyCrypt game (both variants share the shape, differing only in the
literal message `m`):
```
module OTP(m : bool) = {
  proc main() : bool = {
    var k, c : bool;
    k <$ {0,1};
    c <- k ^ m;
    return c;
  }
}
```
The claim re-proved in CatCrypt is that `OTP(m₀).main` and `OTP(m₁).main` are pRHL
equal, hence indistinguishable — the one-time-secrecy statement. It re-proves in
CatCrypt exactly as the native `CatCrypt.Examples.OTP.otp_indcpa_coupling` does:
the uniform key masks the message, so `xor`-by-`(m₀ ^ m₁)` couples the two games.

The game is closed — it calls no module — so it lowers with the empty resolution
environment, `lowerClosedGame`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.EasyCryptImport.OTPImport

open CatCrypt.Core CatCrypt.Prob CatCrypt.Relational CatCrypt.Crypto
open CatCrypt.Prob.XorBij
open CatCrypt.Crypto.EasyCryptBridge

attribute [local implicit_reducible] EcTy.isFin

/-- The imported one-time-pad game for a fixed message bit `m`:
sample the key `k`, set the ciphertext `c := k ^ m`, and return `c`. -/
def otpGame (m : Bool) : EcGame where
  name := "OTP"
  locals := ["k", "c"]
  body :=
    [ EcStmt.sample .bool "k",
      EcStmt.assign .bool "c" (EcExpr.bxor (EcExpr.var .bool "k") (EcExpr.lit m)) ]
  ret := EcExpr.var .bool "c"

/-- The lowered game is the one-time-pad ciphertext family `k ← {0,1}; return k ^ m`.
This identifies the importer's structural output with the hand-written `SPComp`
form, so the coupling reasoning applies to the imported game unchanged. -/
theorem lowerGame_otpGame (m : Bool) :
    lowerClosedGame OpEnv.empty (otpGame m)
      = SPComp.bind (SPComp.sample Bool) (fun k => SPComp.pure (xor k m)) := by
  simp only [lowerClosedGame, lowerGame, otpGame, lowerStmts_sample, lowerStmts_assign,
    lowerStmts_nil, evalExpr, Env.read_update_same, SPComp.bind_assoc, SPComp.pure_bind,
    sampleFin_bool]

/-- **Perfect indistinguishability of the imported games** (pRHL): the two lowered
one-time-pad games — encrypting `m₀` versus `m₁` — are pRHL-equal. The uniform key
masks the message, so `xor`-by-`(m₀ ^ m₁)` is a coupling of the two runs. -/
theorem otpImport_coupling (m₀ m₁ : Bool) :
    pRHL eqPre (lowerClosedGame OpEnv.empty (otpGame m₀)) (lowerClosedGame OpEnv.empty (otpGame m₁)) eqPost := by
  rw [lowerGame_otpGame, lowerGame_otpGame]
  apply rHoare_bij_step (boolXorBij (xor m₀ m₁))
  intro a
  apply rHoare_ret
  intro h₁ h₂ hpre
  refine ⟨?_, hpre⟩
  rw [boolXorBij_apply]
  cases a <;> cases m₀ <;> cases m₁ <;> rfl

/-- **Zero distinguishing advantage** for the imported one-time-pad games: every
distinguisher `A` has advantage exactly `0`, obtained from the pRHL equality
`otpImport_coupling` via `advantage_zero_of_rHoare`. This is the imported form of
one-time secrecy. -/
theorem otpImport_advantage_zero (m₀ m₁ : Bool) (A : Bool → SPComp Bool) :
    AdvantageA (lowerClosedGame OpEnv.empty (otpGame m₀)) (lowerClosedGame OpEnv.empty (otpGame m₁)) A = 0 :=
  advantage_zero_of_rHoare _ _ (otpImport_coupling m₀ m₁) A

end CatCrypt.Crypto.EasyCryptImport.OTPImport

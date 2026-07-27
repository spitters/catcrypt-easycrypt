/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.EasyCryptImport.FormToProp
import CatCrypt.Crypto.EasyCryptImport.Examples.OTPImport
import CatCrypt.Crypto.EasyCryptImport.Examples.ModuleImport
import CatCryptCore.Unary.Rules

/-!
# Worked example: imported statements as Lean goals

This module carries three EasyCrypt statements through the statement layer: each
is written as an `EcForm` literal, translated with `importedProp`, and then shown
to be the proposition it is meant to be.

```
equiv[OTP0.main ~ OTP1.main : ={glob} ==> ={res} /\ ={glob}]

forall &m, `|Pr[OTP0.main() @ &m : res] - Pr[OTP1.main() @ &m : res]| = 0%r

hoare[Otp.enc : true ==> res = Otp.k ^ m]
```

Each imported statement is a `def … : Prop` — a goal. The `theorem`s beside them
are the Lean proofs of those goals, which is the workflow the importer is for: the
exporter produces the goal, a human closes it.

For the first statement the evidence is sharper than a proof. `otpEquivGoal_eq`
holds by `rfl`: the translation of the imported form is *definitionally* the
statement of `OTPImport.otpImport_coupling`, a theorem proved from the CatCrypt
pRHL rules without reference to the statement layer. Since the translation is
unverified (`FormToProp.lean`), a definitional match against an independently
stated and proved theorem is the strongest available evidence that the translation
of `equiv`, of `={glob}` and of `={res}` lands where it should.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.EasyCryptImport.FormImport

open CatCrypt.Core CatCrypt.Prob CatCrypt.Relational CatCrypt.Unary CatCrypt.Crypto
open CatCrypt.Crypto.EasyCryptBridge
open CatCrypt.Crypto.EasyCryptImport.OTPImport
open CatCrypt.Crypto.EasyCryptImport.ModuleImport
open scoped ENNReal

/-! ## The resolution environment

The two one-time-pad variants of `Examples/OTPImport.lean` are registered as
argument-free `bool`-returning procedures, which is how a statement refers to a
game: `OTP0.main` and `OTP1.main`. -/

/-- The signature of an argument-free game: `proc main() : bool`. -/
def mainSig : EcSig := ⟨.unit, .bool⟩

/-- The environment a statement about the two one-time-pad games resolves
against. -/
noncomputable def otpEnv (m₀ m₁ : Bool) : ProcEnv :=
  (ProcEnv.empty.bindProc "OTP0.main" (s := mainSig)
      (fun _ => lowerClosedGame (otpGame m₀))).bindProc "OTP1.main" (s := mainSig)
      (fun _ => lowerClosedGame (otpGame m₁))

theorem otpEnv_zero (m₀ m₁ : Bool) :
    otpEnv m₀ m₁ "OTP0.main" mainSig () = lowerClosedGame (otpGame m₀) := rfl

theorem otpEnv_one (m₀ m₁ : Bool) :
    otpEnv m₀ m₁ "OTP1.main" mainSig () = lowerClosedGame (otpGame m₁) := rfl

/-! ## An imported equiv judgement -/

/-- The imported form of `equiv[OTP0.main ~ OTP1.main : ={glob} ==> ={res} /\ ={glob}]`. -/
def otpEquivForm : EcForm :=
  .equiv "OTP0.main" mainSig (.lit (t := .unit) ())
         "OTP1.main" mainSig (.lit (t := .unit) ())
    (.memEq (.side .left) (.side .right))
    (.and (.eqT (.res .bool .left) (.res .bool .right))
          (.memEq (.side .left) (.side .right)))

/-- The imported statement, as a goal. -/
noncomputable def otpEquivGoal (m₀ m₁ : Bool) : Prop :=
  importedProp (otpEnv m₀ m₁) otpEquivForm

/-- The translated goal is definitionally the pRHL judgement
`OTPImport.otpImport_coupling` states. -/
theorem otpEquivGoal_eq (m₀ m₁ : Bool) :
    otpEquivGoal m₀ m₁
      = pRHL eqPre (lowerClosedGame (otpGame m₀)) (lowerClosedGame (otpGame m₁)) eqPost :=
  rfl

/-- The imported goal, closed. -/
theorem otpEquivGoal_holds (m₀ m₁ : Bool) : otpEquivGoal m₀ m₁ :=
  otpEquivGoal_eq m₀ m₁ ▸ otpImport_coupling m₀ m₁

/-! ## An imported probability bound -/

/-- The imported form of
`forall &m, `|Pr[OTP0.main() @ &m : res] - Pr[OTP1.main() @ &m : res]| = 0%r`. -/
def otpPrDiffForm : EcForm :=
  .allMem "m"
    (EcForm.prDiffCmp .eq "OTP0.main" (.lit (t := .unit) ())
      "OTP1.main" (.lit (t := .unit) ()) (.named "m") (.const 0))

/-- The imported statement, as a goal. -/
noncomputable def otpPrDiffGoal (m₀ m₁ : Bool) : Prop :=
  importedProp (otpEnv m₀ m₁) otpPrDiffForm

/-- The translated goal is the absolute difference of the two games'
probabilities of returning `true`, at every initial memory. The `Pr[… : res]`
nodes land on `prTrue` through `transProb_prTrueOf`. -/
theorem otpPrDiffGoal_eq (m₀ m₁ : Bool) :
    otpPrDiffGoal m₀ m₁
      = ∀ h : Heap, absDiff (prTrue (lowerClosedGame (otpGame m₀)) h)
          (prTrue (lowerClosedGame (otpGame m₁)) h) = 0 := by
  simp only [otpPrDiffGoal, importedProp, otpPrDiffForm, EcForm.prDiffCmp, transForm,
    transProb_absDiff, transProb_prTrueOf, cmpRel]
  rfl

/-- The two lowered games are equal as computations: the pRHL equality of
`OTPImport.otpImport_coupling` is an equality of the underlying distributions at
every heap. -/
theorem lowerGame_otp_eq (m₀ m₁ : Bool) :
    lowerClosedGame (otpGame m₀) = lowerClosedGame (otpGame m₁) :=
  congrFun (pRHL_eq_implies_prog_eq (fun _ : Unit => lowerClosedGame (otpGame m₀))
    (fun _ => lowerClosedGame (otpGame m₁)) (fun _ => otpImport_coupling m₀ m₁)) ()

/-- The imported goal, closed. -/
theorem otpPrDiffGoal_holds (m₀ m₁ : Bool) : otpPrDiffGoal m₀ m₁ := by
  simp only [otpPrDiffGoal_eq, lowerGame_otp_eq m₀ m₁, absDiff_self, implies_true]

/-! ## An imported Hoare judgement

The module `Otp` of `Examples/ModuleImport.lean` has the global `var k : bool`, so
a statement about it can read that global at a memory. This is the only kind of
program variable a form can mention: `Otp.k` is a heap cell, while a
procedure-local variable is not heap state at all (`FormToProp.lean`). -/

/-- The imported form of `hoare[Otp.enc : true ==> res = Otp.k ^ m]`: the
ciphertext `Otp.enc` returns is the key stored in `Otp.k` masked with the
message. `Otp.k` is read at the judgement's final memory. -/
def encHoareForm (m : Bool) : EcForm :=
  .hoare (qualify "Otp" "enc") ⟨.bool, .bool⟩ (.lit (t := .bool) m) .tru
    (.eqT (.res .bool .cur) (.bxor (.glob kGlobal (.side .cur)) (.lit (t := .bool) m)))

/-- The imported statement, as a goal. -/
noncomputable def encHoareGoal (m : Bool) : Prop := importedProp baseEnv (encHoareForm m)

/-- The translated goal is the pHL judgement about the lowered procedure
`Otp.enc`. -/
theorem encHoareGoal_eq (m : Bool) :
    encHoareGoal m
      = pHoare (fun _ => True) (otpImpl.proc "enc" m)
          (fun r h' => r = xor (h'.get kLoc) m) := by
  show pHoare (fun _ => True) (otpImpl.proc "enc" m)
      (fun r h' => r = xor (h'.gget kGlobal.loc) m) = _
  simp only [show ∀ h : Heap, h.gget kGlobal.loc = h.get kLoc from
    fun h => Heap.gget_ofLocation h kLoc]

/-- The imported goal, closed. -/
theorem encHoareGoal_holds (m : Bool) : encHoareGoal m := by
  rw [encHoareGoal_eq, otpImpl_enc]
  exact pHoare_bind (Mid := fun v h => v = h.get kLoc) (pHoare_get (fun _ _ => rfl))
    (fun _ => pHoare_ret (fun _ hv => by rw [hv]))

end CatCrypt.Crypto.EasyCryptImport.FormImport

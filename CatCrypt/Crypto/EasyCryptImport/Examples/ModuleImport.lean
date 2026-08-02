/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.EasyCryptImport.Lower
import CatCrypt.Crypto.EasyCryptImport.Restrictions
import CatCryptCore.Crypto.Advantage
import CatCryptCore.Crypto.EasyCryptBridge
import CatCryptCore.Prob.XorBij

/-!
# Worked example: a module, a functor, and an adversary parameter

This module carries an EasyCrypt experiment built from all three module-layer
constructs through the importer end to end: a **concrete module** with global
state, an **abstract module** (the adversary) the experiment is quantified over,
and a **functor** over that adversary. The imported source is

```
module type ADV = { proc guess(c : bool) : bool }

module Otp = {
  var k : bool
  proc init()        : unit = { k <$ {0,1}; }
  proc enc(m : bool) : bool = { kk <- k; return kk ^ m; }
  proc clear()       : unit = { k <- false; }
}

module Exp(A : ADV{-Otp}, m : bool) = {
  proc main() : bool = {
    Otp.init();
    c <@ Otp.enc(m);
    b <@ A.guess(c);
    Otp.clear();
    return b;
  }
}

module Flip(A : ADV) = { proc guess(c : bool) : bool = { b <@ A.guess(c); return !b; } }
```

`Otp.k` is a module global, so it is a `Location` in the CatCrypt heap;
`Otp.init` writes it and `Otp.enc` reads it. `Exp` is a functor over the
adversary: `expImport` is the Lean function from a `ModuleImpl advInterface` to
the lowered game, and every statement below quantifies over that parameter.

## The emitted side hypothesis

EasyCrypt writes the adversary as `A : ADV{-Otp}`: the module system forbids `A`
from touching `Otp`'s memory. CatCrypt has no type-level home for that
restriction, so the importer emits it as an explicit hypothesis
`RespectsLocs otpLocs (A.proc "guess")` on the generated statement
(`Restrictions.lean`). The hypothesis carries the proof: the coupling leaves the
two runs with *different* keys in `Otp.k`, and an adversary free to read that
location would distinguish the two experiments immediately.

`expImport_advantage_zero` is the imported claim: for every adversary of the
interface `ADV` that respects `Otp`'s footprint, the experiments encrypting `m₀`
and `m₁` are perfectly indistinguishable. `flipImport_advantage_zero` applies it
to the functor image `Flip(A)`, whose restriction follows from `A`'s by
`RespectsLocs.map`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.EasyCryptImport.ModuleImport

open CatCrypt.Core CatCrypt.Prob CatCrypt.Relational CatCrypt.Crypto CatCrypt.Unary
open CatCrypt.Prob.XorBij
open CatCrypt.Crypto.EasyCryptBridge

/-! ## The concrete module `Otp` -/

/-- `Otp`'s single global `var k : bool`, at a stable heap location id. -/
def kGlobal : EcGlobal := { name := "Otp.k", id := 90001, ty := .bool }

/-- The `Location` `Otp.k` occupies: its code is finite, so the cell its
`EcGlobal` denotes is also a finite-typed location. -/
def kLoc : Location := kGlobal.finLoc rfl

/-- `Otp`'s memory footprint — the image of EasyCrypt's `glob Otp`. -/
def otpLocs : LocSet := {kGlobal.id}

/-- The module type of `Otp`. -/
def otpInterface : EcInterface where
  names := ["init", "enc", "clear"]
  sig := fun p =>
    match p with
    | "init" => ⟨.unit, .unit⟩
    | "enc" => ⟨.bool, .bool⟩
    | "clear" => ⟨.unit, .unit⟩
    | _ => ⟨.unit, .unit⟩

/-- The imported concrete module `Otp`. -/
def otpModule : EcModule where
  name := "Otp"
  interface := otpInterface
  globals := [kGlobal]
  procs := fun p =>
    match p with
    | "init" =>
        { params := ["u"]
          body := [.sample .bool "k", .store kGlobal (.var .bool "k")]
          ret := .lit () }
    | "enc" =>
        { params := ["m"]
          body := [.load kGlobal "k"]
          ret := .bxor (.var .bool "k") (.var .bool "m") }
    | "clear" =>
        { params := ["u"]
          body := [.store kGlobal (.lit false)]
          ret := .lit () }
    | _ => { params := ["u"], body := [], ret := .lit default }

/-- `otpLocs` is the footprint computed from the module's own `var`
declarations. -/
theorem otpLocs_eq_globLocs : globLocs otpModule.globals = otpLocs := by
  simp [globLocs, otpModule, otpLocs]

theorem kGlobal_mem_otpLocs : kLoc.id ∈ otpLocs := Finset.mem_singleton_self _

/-- The lowered module: a record of `SPComp` procedures sharing `Otp.k`. -/
noncomputable def otpImpl : ModuleImpl otpInterface := lowerModule ProcEnv.empty 0 otpModule

/-! ## The adversary interface -/

/-- The module type `ADV`: one procedure `guess : bool -> bool`. -/
def advInterface : EcInterface where
  names := ["guess"]
  sig := fun _ => ⟨.bool, .bool⟩

/-- An adversary of the interface `ADV` that echoes the ciphertext it is handed
and never touches the heap. -/
noncomputable def echoAdv : ModuleImpl advInterface where
  proc := fun _ c => SPComp.pure c

/-- `echoAdv` satisfies the emitted `A{-Otp}` restriction and `islossless`, so
the hypotheses of the statements below are inhabited. -/
theorem echoAdv_respects : RespectsLocs otpLocs (echoAdv.proc "guess") :=
  respectsLocs_of_isPure _ _ (fun c => SPComp.pure_isPure c)

theorem echoAdv_lossless : ProcLossless (echoAdv.proc "guess") :=
  fun c => lossless_pure c

/-! ## The experiment -/

/-- The imported experiment `Exp(A)` for the message bit `m`. The adversary is
called through the qualified name `A.guess`, so the resolution environment
decides which module answers it. -/
def expGame (m : Bool) : EcGame where
  name := "Exp"
  locals := ["c", "b"]
  body :=
    [ .callProc (qualify "Otp" "init") ⟨.unit, .unit⟩ (.lit ()) "u",
      .callProc (qualify "Otp" "enc") ⟨.bool, .bool⟩ (.lit m) "c",
      .callProc (qualify "A" "guess") ⟨.bool, .bool⟩ (.var .bool "c") "b",
      .callProc (qualify "Otp" "clear") ⟨.unit, .unit⟩ (.lit ()) "u" ]
  ret := .var .bool "b"

/-- The environment resolving `Otp`'s procedures. -/
noncomputable def baseEnv : ProcEnv := ProcEnv.empty.bindModule "Otp" otpImpl

/-- The environment of the experiment: `Otp` bound concretely, the adversary
bound to the module parameter `A`. -/
noncomputable def expEnv (A : ModuleImpl advInterface) : ProcEnv :=
  baseEnv.bindModule "A" A

/-- The experiment as a family indexed by the adversary module: the imported
form of `Exp(A)`, universally quantified over `A` in the statements below. -/
noncomputable def expImport (A : ModuleImpl advInterface) (m : Bool) : SPComp Bool :=
  lowerGame (expEnv A) (expGame m) 0

/-! ## The functor -/

/-- The body of the functor `Flip(A)`: call the parameter's `guess` and negate. -/
def flipModule : EcModule where
  name := "Flip"
  interface := advInterface
  globals := []
  procs := fun _ =>
    { params := ["c"]
      body := [.callProc (qualify "A" "guess") ⟨.bool, .bool⟩ (.var .bool "c") "b"]
      ret := .bnot (.var .bool "b") }

/-- The imported functor `Flip(A : ADV) : ADV`. -/
def flipFunctor : EcFunctor where
  name := "Flip"
  paramName := "A"
  paramInterface := advInterface
  body := flipModule

/-- The functor as a Lean function on module records. -/
noncomputable def flipImpl (A : ModuleImpl advInterface) : ModuleImpl advInterface :=
  lowerFunctor ProcEnv.empty 0 flipFunctor A

/-! ## Closed forms of the lowered procedures -/

/-- Reading a variable across an update of a different variable. -/
private theorem read_past (x y : String) (h : y ≠ x) (env : Env) (v : EcVal) :
    (env.update x v).read .bool y = env.read .bool y :=
  Env.read_update_ne env .bool x y v (by simpa using h)

theorem otpImpl_init (u : Unit) :
    otpImpl.proc "init" u
      = SPComp.bind (SPComp.sample Bool)
          (fun k => SPComp.bind (SPComp.set kLoc k) (fun _ => SPComp.pure ())) := by
  show SPComp.bind
      (lowerStmts ProcEnv.empty [] 0
        [EcStmt.sample .bool "k", EcStmt.store kGlobal (EcExpr.var .bool "k")]
        (emptyEnv.update "u" ⟨EcTy.unit, u⟩))
      (fun env => SPComp.pure (evalExpr (EcExpr.lit (t := .unit) ()) env)) = _
  simp only [lowerStmts_sample, lowerStmts_store_finLoc (g := kGlobal) (hfin := rfl),
    lowerStmts_nil, sampleFin_bool, SPComp.bind_assoc, SPComp.pure_bind, evalExpr]
  rfl

theorem otpImpl_enc (a : Bool) :
    otpImpl.proc "enc" a
      = SPComp.bind (SPComp.get kLoc) (fun k => SPComp.pure (xor k a)) := by
  show SPComp.bind
      (lowerStmts ProcEnv.empty [] 0 [EcStmt.load kGlobal "k"]
        (emptyEnv.update "m" ⟨EcTy.bool, a⟩))
      (fun env => SPComp.pure
        (evalExpr (EcExpr.bxor (EcExpr.var .bool "k") (EcExpr.var .bool "m")) env)) = _
  simp only [lowerStmts_load_finLoc (g := kGlobal) (hfin := rfl), lowerStmts_nil,
    SPComp.bind_assoc, SPComp.pure_bind, evalExpr, Env.read_update_same,
    read_past "k" "m" (by decide)]
  rfl

theorem otpImpl_clear (u : Unit) :
    otpImpl.proc "clear" u
      = SPComp.bind (SPComp.set kLoc false) (fun _ => SPComp.pure ()) := by
  show SPComp.bind
      (lowerStmts ProcEnv.empty [] 0 [EcStmt.store kGlobal (EcExpr.lit (t := .bool) false)]
        (emptyEnv.update "u" ⟨EcTy.unit, u⟩))
      (fun env => SPComp.pure (evalExpr (EcExpr.lit (t := .unit) ()) env)) = _
  simp only [lowerStmts_store_finLoc (g := kGlobal) (hfin := rfl), lowerStmts_nil,
    SPComp.bind_assoc, SPComp.pure_bind, evalExpr]
  rfl

theorem flipImpl_guess (A : ModuleImpl advInterface) (c : Bool) :
    (flipImpl A).proc "guess" c
      = SPComp.bind (A.proc "guess" c) (fun b => SPComp.pure (!b)) := by
  show SPComp.bind
      (lowerStmts (ProcEnv.empty.bindModule "A" A) [] 0
        [EcStmt.callProc (qualify "A" "guess") ⟨.bool, .bool⟩ (EcExpr.var .bool "c") "b"]
        (emptyEnv.update "c" ⟨EcTy.bool, c⟩))
      (fun env => SPComp.pure (evalExpr (EcExpr.bnot (EcExpr.var .bool "b")) env)) = _
  simp only [lowerStmts_callProc, lowerStmts_nil, SPComp.bind_assoc, SPComp.pure_bind,
    evalExpr, Env.read_update_same]
  rfl

/-! ## Call resolution in the experiment -/

theorem expEnv_init (A : ModuleImpl advInterface) :
    expEnv A (qualify "Otp" "init") ⟨.unit, .unit⟩ = otpImpl.proc "init" := rfl

theorem expEnv_enc (A : ModuleImpl advInterface) :
    expEnv A (qualify "Otp" "enc") ⟨.bool, .bool⟩ = otpImpl.proc "enc" := rfl

theorem expEnv_clear (A : ModuleImpl advInterface) :
    expEnv A (qualify "Otp" "clear") ⟨.unit, .unit⟩ = otpImpl.proc "clear" := rfl

theorem expEnv_guess (A : ModuleImpl advInterface) :
    expEnv A (qualify "A" "guess") ⟨.bool, .bool⟩ = A.proc "guess" := rfl

/-- The lowered experiment in closed form: sample the key, store it, hand the
one-time-pad ciphertext to the adversary, clear the key, and return the
adversary's bit. -/
theorem expImport_eq (A : ModuleImpl advInterface) (m : Bool) :
    expImport A m
      = SPComp.bind (SPComp.sample Bool) (fun k =>
          SPComp.bind (SPComp.set kLoc k) (fun _ =>
            SPComp.bind (A.proc "guess" (xor k m)) (fun b =>
              SPComp.bind (SPComp.set kLoc false) (fun _ => SPComp.pure b)))) := by
  simp only [expImport, lowerGame, expGame, lowerStmts_callProc, lowerStmts_nil,
    expEnv_init, expEnv_enc, expEnv_guess, expEnv_clear, evalExpr, otpImpl_init, otpImpl_enc,
    otpImpl_clear, EcTy.interp, SPComp.bind_assoc, SPComp.pure_bind, bind_set_get,
    Env.read_update_same, read_past "u" "b" (by decide)]
  rfl

/-! ## Security -/

/-- **Perfect indistinguishability of the imported experiment** (pRHL): for any
adversary that respects `Otp`'s footprint, the runs on `m₀` and on `m₁` are pRHL
equal. The fresh uniform key masks the message, so `xor`-by-`(m₀ ^ m₁)` couples
the two runs; the restriction hypothesis is what carries the coupling through
the adversary call, and clearing `Otp.k` afterwards turns agreement outside the
footprint into heap equality. -/
theorem expImport_coupling (A : ModuleImpl advInterface)
    (hA : RespectsLocs otpLocs (A.proc "guess")) (m₀ m₁ : Bool) :
    pRHL eqPre (expImport A m₀) (expImport A m₁) eqPost := by
  rw [expImport_eq, expImport_eq]
  apply rHoare_bij_step (boolXorBij (xor m₀ m₁))
  intro k
  have hc : xor ((boolXorBij (xor m₀ m₁)) k) m₁ = xor k m₀ := by
    cases k <;> cases m₀ <;> cases m₁ <;> simp [boolXorBij_apply]
  rw [hc]
  refine rHoare_set_step (Φ' := agreeOff otpLocs) kLoc k _ (fun h₁ h₂ hpre => ?_) ?_
  · exact agreeOff_set otpLocs kLoc kGlobal_mem_otpLocs
      (agreeOff_of_eq hpre) _ _
  · refine rHoare_bind (hA (xor k m₀)) (fun b₁ b₂ => ?_)
    refine rHoare_set_step (Φ' := fun h₁ h₂ => b₁ = b₂ ∧ h₁ = h₂) kLoc false false
      (fun h₁ h₂ hpre => ⟨hpre.1, heap_eq_of_agreeOff_singleton kLoc hpre.2 false⟩) ?_
    exact rHoare_ret (fun _ _ hh => ⟨hh.1, hh.2⟩)

/-- **Zero distinguishing advantage** for the imported experiment: every
adversary respecting `Otp`'s footprint, and every post-distinguisher, has
advantage exactly `0`. -/
theorem expImport_advantage_zero (A : ModuleImpl advInterface)
    (hA : RespectsLocs otpLocs (A.proc "guess")) (m₀ m₁ : Bool) (D : Bool → SPComp Bool) :
    AdvantageA (expImport A m₀) (expImport A m₁) D = 0 :=
  advantage_zero_of_rHoare _ _ (expImport_coupling A hA m₀ m₁) D

/-- **Termination of the imported experiment**: EasyCrypt's `islossless A.guess`,
emitted as the hypothesis `ProcLossless (A.proc "guess")`, gives losslessness of
`Exp(A).main` — sampling, heap writes and `return` are lossless, so the only way
the experiment could lose mass is through the adversary. -/
theorem expImport_lossless (A : ModuleImpl advInterface)
    (hA : ProcLossless (A.proc "guess")) (m : Bool) :
    isLossless (expImport A m) := by
  rw [expImport_eq]
  refine lossless_bind (lossless_sample (α := Bool)) (fun k => ?_)
  refine lossless_bind (lossless_set kLoc k) (fun _ => ?_)
  refine lossless_bind (hA _) (fun b => ?_)
  exact lossless_bind (lossless_set kLoc false) (fun _ => lossless_pure b)

/-- The functor image inherits the restriction: `Flip(A)` only sequences a call
to `A` with a pure negation, so it respects `Otp`'s footprint whenever `A`
does. -/
theorem flipImpl_respects (A : ModuleImpl advInterface)
    (hA : RespectsLocs otpLocs (A.proc "guess")) :
    RespectsLocs otpLocs ((flipImpl A).proc "guess") :=
  fun c => (flipImpl_guess A c) ▸ hA.map (fun b : Bool => !b) c

/-- The imported claim composed with the functor: the experiment is secure
against `Flip(A)` for every restricted `A`. -/
theorem flipImport_advantage_zero (A : ModuleImpl advInterface)
    (hA : RespectsLocs otpLocs (A.proc "guess")) (m₀ m₁ : Bool) (D : Bool → SPComp Bool) :
    AdvantageA (expImport (flipImpl A) m₀) (expImport (flipImpl A) m₁) D = 0 :=
  expImport_advantage_zero (flipImpl A) (flipImpl_respects A hA) m₀ m₁ D

end CatCrypt.Crypto.EasyCryptImport.ModuleImport

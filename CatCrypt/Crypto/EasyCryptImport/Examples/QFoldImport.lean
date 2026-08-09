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
# Worked example: a q-fold one-time-pad experiment with a loop and a procedure call

This module carries one EasyCrypt-style game that uses **both** a bounded loop and
a **procedure call** through the importer end to end: it encodes a `q`-round
one-time-pad accumulator as an `EcGame` whose `main` calls a `step` procedure `q`
times in a bounded loop, lowers it to `SPComp Bool`, and proves perfect
indistinguishability of the two message variants — first as a pRHL judgment, then
lifted to zero distinguishing advantage.

The imported EasyCrypt game (the two variants differ only in the literal message
`m`):
```
module QFoldOTP(m : bool) = {
  var acc, k : bool
  proc step() : unit = {
    k   <$ {0,1};
    acc <- acc ^ k ^ m;
  }
  proc main() : bool = {
    var i : int;
    acc <- false;
    i <- 0;
    while (i < q) {
      step();
      i <- i + 1;
    }
    return acc;
  }
}
```
EasyCrypt writes bounded loops as `while`: a counter given its initial value by
the statement before the loop, a guard `i < q`, and a body whose last statement
increments the counter and which writes it nowhere else. The decoder recognises
this idiom when the bound is an integer literal and decodes it to the `forN`
loop form, which carries the iteration count and no counter; here `q` stands for
that literal, matching the Lean game's parameter `q : Nat`.

Each round masks the accumulator with a fresh uniform bit, so after any number of
rounds `acc` is uniform independently of `m`; the two variants are therefore pRHL
equal and indistinguishable.

The proof exercises the loop and argument-free-call lowering directly:

* `lowerGame_qfold` reduces the lowered game to a clean `SPComp.foldM` over the
  loop step — witnessing that `forN` lowers to `SPComp.foldM` and that `call step`
  inlines to the sampling step (`loopStep_eq`);
* `qfold_coupling` couples the two `q`-fold games with `rHoare_foldM`, the
  relational loop rule, using the per-round XOR bijection `boolXorBij (m₀ ^ m₁)`;
* `qfold_advantage_zero` lifts this to `AdvantageA = 0` via
  `advantage_zero_of_rHoare`.

`acc` and `k` are game-local variables, so they live in the valuation `Env` and
the game never touches the heap; a module-scoped `var` would instead be an
`EcGlobal` at a heap cell (see `Examples/ModuleImport.lean`).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.EasyCryptImport.QFoldImport

open CatCrypt.Core CatCrypt.Prob CatCrypt.Relational CatCrypt.Crypto
open CatCrypt.Prob.XorBij
open CatCrypt.Crypto.EasyCryptBridge

/-- The body of the `step` procedure for message bit `m`: sample a fresh key `k`
and fold it into the accumulator, `acc <- acc ^ k ^ m`. -/
def stepBody (m : Bool) : List EcStmt :=
  [ EcStmt.sample .bool "k",
    EcStmt.assign .bool "acc"
      (EcExpr.bxor (EcExpr.bxor (EcExpr.var .bool "acc") (EcExpr.var .bool "k"))
        (EcExpr.lit m)) ]

/-- The procedure table of the q-fold game: a single procedure `step`. -/
def qfoldProcs (m : Bool) : List (String × List EcStmt) := [("step", stepBody m)]

/-- The imported q-fold one-time-pad game for message bit `m` and round count `q`:
initialise `acc := false`, then call `step` `q` times in a bounded loop, and
return `acc`. -/
def qfoldGame (m : Bool) (q : Nat) : EcGame where
  name := "QFoldOTP"
  locals := ["acc", "k"]
  procs := qfoldProcs m
  body :=
    [ EcStmt.assign .bool "acc" (EcExpr.lit false),
      EcStmt.forN q [EcStmt.call "step"] ]
  ret := EcExpr.var .bool "acc"

/-- The initial valuation for the loop: every variable unassigned, `acc` set to `b`. -/
def accEnv (b : Bool) : Env := (emptyEnv OpEnv.empty).update "acc" ⟨.bool, b⟩

/-- One lowered round: sample `k`, rebind `k` and then `acc := acc ^ k ^ m`. This
is the semantic content of a single `call step`. -/
noncomputable def stepFn (m : Bool) (e : Env) : SPComp Env :=
  SPComp.bind (SPComp.sample Bool)
    (fun k => SPComp.pure ((e.update "k" ⟨.bool, k⟩).update "acc"
      ⟨.bool, xor (xor (e.read .bool "acc") k) m⟩))

/-- The loop step `call step` lowers (at call-depth bound `1`) to `stepFn m`: the
procedure call is inlined to its sampling body. -/
theorem loopStep_eq (m : Bool) (e : Env) :
    lowerStmts ProcEnv.empty (qfoldProcs m) 1 [EcStmt.call "step"] e = stepFn m e := by
  have hpb : procBody (qfoldProcs m) "step" = stepBody m := by
    simp [procBody, qfoldProcs]
  rw [lowerStmts_call_succ, hpb]
  simp only [stepBody, lowerStmts_sample, lowerStmts_assign, lowerStmts_nil,
    SPComp.bind_pure, evalExpr, Env.read_update_same, stepFn]
  rfl

/-- The lowered q-fold game is a clean `SPComp.foldM` of the sampling step,
followed by reading out the accumulator bit. This identifies the importer's
output with a hand-written fold, so the relational loop rule applies. -/
theorem lowerGame_qfold (m : Bool) (q : Nat) :
    lowerClosedGame OpEnv.empty (qfoldGame m q) 1
      = SPComp.bind (SPComp.foldM (accEnv false) (List.replicate q (stepFn m)))
          (fun e => SPComp.pure (e.read .bool "acc")) := by
  have hfn : (fun e => lowerStmts ProcEnv.empty (qfoldProcs m) 1 [EcStmt.call "step"] e)
      = stepFn m := by
    funext e; exact loopStep_eq m e
  simp only [lowerClosedGame, lowerGame, qfoldGame, lowerStmts_assign, lowerStmts_forN,
    lowerStmts_nil, evalExpr, SPComp.bind_pure, accEnv]
  rw [hfn]

/-- The loop invariant coupling the two runs: the accumulators agree and the heaps
agree. -/
private def Inv : Env → Env → RPre :=
  fun e₁ e₂ h₁ h₂ => e₁.read .bool "acc" = e₂.read .bool "acc" ∧ h₁ = h₂

/-- **Perfect indistinguishability of the imported q-fold games** (pRHL): the two
lowered games — folding `m₀` versus `m₁` over `q` rounds — are pRHL equal. Each
round's fresh uniform key masks the message, so the XOR bijection
`boolXorBij (m₀ ^ m₁)` couples the two runs round by round; `rHoare_foldM` lifts
the per-round coupling over the whole loop. -/
theorem qfold_coupling (m₀ m₁ : Bool) (q : Nat) :
    pRHL eqPre (lowerClosedGame OpEnv.empty (qfoldGame m₀ q) 1) (lowerClosedGame OpEnv.empty (qfoldGame m₁ q) 1)
      eqPost := by
  rw [lowerGame_qfold, lowerGame_qfold]
  apply rHoare_bind (Ψ := fun e₁ h₁ e₂ h₂ =>
    e₁.read .bool "acc" = e₂.read .bool "acc" ∧ h₁ = h₂)
  · -- the loop: rHoare over `foldM`
    refine rHoare_conseq (Φ := Inv (accEnv false) (accEnv false)) ?_ (fun _ _ _ _ h => h)
      (rHoare_foldM (Inv := Inv)
        (List.replicate q (stepFn m₀)) (List.replicate q (stepFn m₁))
        (by simp) ?_ (accEnv false) (accEnv false))
    · intro h₁ h₂ hpre
      exact ⟨rfl, hpre⟩
    · -- each round preserves the invariant, via the per-round XOR bijection
      intro i hi a₁ a₂
      simp only [List.getElem_replicate, stepFn]
      apply rHoare_bij_step (boolXorBij (xor m₀ m₁))
      intro k
      apply rHoare_ret
      intro h₁ h₂ hpre
      obtain ⟨hacc, hh⟩ := hpre
      refine ⟨?_, hh⟩
      simp only [Env.read_update_same, boolXorBij_apply]
      rw [hacc]
      generalize a₂.read .bool "acc" = a
      cases a <;> cases k <;> cases m₀ <;> cases m₁ <;> rfl
  · -- read out the accumulator: equal accumulators give equal outputs
    intro e₁ e₂
    apply rHoare_ret
    intro h₁ h₂ hpre
    exact ⟨hpre.1, hpre.2⟩

/-- **Zero distinguishing advantage** for the imported q-fold games: every
distinguisher `A` has advantage exactly `0`, obtained from the pRHL equality
`qfold_coupling` via `advantage_zero_of_rHoare`. -/
theorem qfold_advantage_zero (m₀ m₁ : Bool) (q : Nat) (A : Bool → SPComp Bool) :
    AdvantageA (lowerClosedGame OpEnv.empty (qfoldGame m₀ q) 1) (lowerClosedGame OpEnv.empty (qfoldGame m₁ q) 1) A
      = 0 :=
  advantage_zero_of_rHoare _ _ (qfold_coupling m₀ m₁ q) A

end CatCrypt.Crypto.EasyCryptImport.QFoldImport

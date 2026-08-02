/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.EasyCryptImport.Lower
import CatCryptCore.Relational.Rules
import CatCryptCore.Crypto.Advantage
import CatCryptCore.Crypto.EasyCryptBridge
import CatCryptCore.Crypto.ForkingLemma

/-!
# Worked example: importing a game that samples from a non-uniform distribution

This module carries an EasyCrypt game whose sampling instruction reads a
`dexcepted` distribution through the importer, and proves what the conditioning
gives: a sample from `dbool` conditioned to avoid `false` is the constant `true`,
so the imported game returns `true` with probability one.

The imported EasyCrypt game:
```
module Excepted = {
  proc main() : bool = {
    var x : bool;
    x <$ dbool \ (fun b => !b);
    return x;
  }
}
```
`d \ X` is EasyCrypt's `dexcepted`: sample `d`, conditioned on avoiding `X`. Here
`X` is `fun b => !b`, so the sample avoids `false`, and the surviving outcome
`true` carries all the mass.

`Dexcepted.ec` proves that a rejection-sampling `while` loop has the distribution
`d \ X`. The importer has no unbounded loop, and importing the distribution form
is what makes that loop unnecessary: the distribution the loop implements is the
one the AST samples from directly.

The game is closed — it calls no module — so it lowers with the empty resolution
environment, `lowerClosedGame`. The exporter fixture `nonunif.expected.json`
carries this source; the golden `#guard`s of `Json.lean` decode it, and the check
beside `exceptedGame` below matches the hand-written literal against the same
shape.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.EasyCryptImport.NonUniformImport

open CatCrypt.Core CatCrypt.Prob CatCrypt.Relational CatCrypt.Crypto
open CatCrypt.Crypto.EasyCryptBridge CatCrypt.Crypto.ForkingLemma
open CatCrypt.NonUniform
open scoped ENNReal

/-! ## The distribution -/

/-- The distribution expression `dbool \ (fun b => !b)` at the lambda binder `k`,
as the decoder produces it: conditioning on the negation of the avoided
predicate. -/
def dboolExceptFalse (k : EcVarId) : EcDistr .bool :=
  EcDistr.cond (EcDistr.uniform .bool) k (EcExpr.bnot (EcExpr.bnot (EcExpr.var .bool k)))

/-- **Conditioning a uniform sample on a predicate met by one value is a point
mass.** Every value of a finite code has positive weight under the uniform
distribution, so `condition_eq_pure` applies whenever the predicate the body
evaluates to admits a single value. -/
theorem evalDistr_cond_uniform_eq_pure (t : EcTy) (h : t.isFin = true) (x : EcVarId)
    (p : EcExpr .bool) (env : Env) (a : t.interp)
    (hunique : ∀ b : t.interp, evalExpr p (env.update x ⟨t, b⟩) = true → b = a)
    (ha : evalExpr p (env.update x ⟨t, a⟩) = true) :
    evalDistr (EcDistr.cond (EcDistr.uniform t h) x p) env = SDistr.pure a := by
  letI := t.fintypeOfIsFin h
  rw [evalDistr_cond, evalDistr_uniform]
  refine condition_eq_pure _ _ a hunique ha ?_
  rw [SDistr.uniform_apply_some]
  simp

/-- **The excepted distribution is a point mass.** Sampling `dbool` conditioned to
avoid `false` gives `true` with probability one: `false` is the only outcome the
predicate removes, and the surviving outcome has positive weight. -/
theorem evalDistr_dboolExceptFalse (k : EcVarId) (env : Env) :
    evalDistr (dboolExceptFalse k) env
      = (SDistr.pure true : SDistr (EcTy.bool).interp) :=
  evalDistr_cond_uniform_eq_pure .bool rfl k _ env true
    (fun b hb => by simpa [evalExpr, Env.read_update_same] using hb)
    (by simp [evalExpr, Env.read_update_same])

/-! ## The imported games -/

/-- The imported game that samples from the excepted distribution and returns the
sample, at the lambda binder `k`. -/
def exceptedGame (k : EcVarId) : EcGame where
  name := "Excepted"
  locals := ["x"]
  body := [EcStmt.sampleD .bool "x" (dboolExceptFalse k)]
  ret := EcExpr.var .bool "x"

-- The game the theorems below are about is the shape the golden `#guard`s of
-- `Json.lean` match `importGame ecPrelude "Excepted" nonunifExport` against, at
-- the same source name and at a stamped binder the body's occurrence is.
#guard (match exceptedGame ⟨"b", some 7⟩ with
        | { name := "Excepted", locals := ["x"], procs := [],
            body := [.sampleD .bool "x"
                       (.cond (.uniform _ _) k
                         (.bnot (.bnot (.var .bool z))))],
            ret := .var .bool "x" } => k.stamp.isSome && k == z
        | _ => false)

/-- The imported game that samples from the point mass `dunit true` and returns
the sample. -/
def pointGame : EcGame where
  name := "Point"
  locals := ["x"]
  body := [EcStmt.sampleD .bool "x" (EcDistr.point (EcExpr.lit (t := .bool) true))]
  ret := EcExpr.var .bool "x"

/-- The excepted game's body binds `x` to `true`. -/
theorem lowerStmts_exceptedBody (k : EcVarId) (env : Env) :
    lowerStmts ProcEnv.empty [] 0 [EcStmt.sampleD .bool "x" (dboolExceptFalse k)] env
      = SPComp.pure (env.update "x" ⟨.bool, true⟩) := by
  rw [lowerStmts_sampleD, evalDistr_dboolExceptFalse, sampleFrom_pure,
    SPComp.pure_bind, lowerStmts_nil]

/-- The point-mass game's body binds `x` to `true`. -/
theorem lowerStmts_pointBody (env : Env) :
    lowerStmts ProcEnv.empty [] 0
        [EcStmt.sampleD .bool "x" (EcDistr.point (EcExpr.lit (t := .bool) true))] env
      = SPComp.pure (env.update "x" ⟨.bool, true⟩) := by
  rw [lowerStmts_sampleD, evalDistr_point, sampleFrom_pure, SPComp.pure_bind,
    lowerStmts_nil]
  rfl

/-- The lowered excepted game is the constant `true`. -/
theorem lowerClosedGame_exceptedGame (k : EcVarId) :
    lowerClosedGame (exceptedGame k) = SPComp.pure true := by
  show SPComp.bind
      (lowerStmts ProcEnv.empty [] 0
        [EcStmt.sampleD .bool "x" (dboolExceptFalse k)] emptyEnv)
      (fun env => SPComp.pure (evalExpr (EcExpr.var .bool "x") env)) = SPComp.pure true
  rw [lowerStmts_exceptedBody, SPComp.pure_bind]
  simp only [evalExpr, Env.read_update_same]

/-- The lowered point-mass game is the constant `true`. -/
theorem lowerClosedGame_pointGame :
    lowerClosedGame pointGame = SPComp.pure true := by
  show SPComp.bind
      (lowerStmts ProcEnv.empty [] 0
        [EcStmt.sampleD .bool "x" (EcDistr.point (EcExpr.lit (t := .bool) true))] emptyEnv)
      (fun env => SPComp.pure (evalExpr (EcExpr.var .bool "x") env)) = SPComp.pure true
  rw [lowerStmts_pointBody, SPComp.pure_bind]
  simp only [evalExpr, Env.read_update_same]

/-- The two imported games lower to one `SPComp Bool`: importing the `dexcepted`
distribution and importing the point mass it equals give the same program. -/
theorem lowerClosedGame_exceptedGame_eq_pointGame (k : EcVarId) :
    lowerClosedGame (exceptedGame k) = lowerClosedGame pointGame := by
  rw [lowerClosedGame_exceptedGame, lowerClosedGame_pointGame]

/-- **The imported non-uniform game returns `true` with probability one.** -/
theorem prTrue_exceptedGame (k : EcVarId) (h : Heap) :
    prTrue (lowerClosedGame (exceptedGame k)) h = 1 := by
  rw [lowerClosedGame_exceptedGame, prTrue_pure_bool]
  simp

/-- The two imported games are pRHL-equal, from the program equality. -/
theorem exceptedGame_coupling (k : EcVarId) :
    pRHL eqPre (lowerClosedGame (exceptedGame k)) (lowerClosedGame pointGame) eqPost := by
  rw [lowerClosedGame_exceptedGame, lowerClosedGame_pointGame]
  exact rHoare_ret fun _ _ hpre => ⟨rfl, hpre⟩

/-- Zero distinguishing advantage between the two imported games. -/
theorem exceptedGame_advantage_zero (k : EcVarId) (A : Bool → SPComp Bool) :
    AdvantageA (lowerClosedGame (exceptedGame k)) (lowerClosedGame pointGame) A = 0 :=
  advantage_zero_of_rHoare _ _ (exceptedGame_coupling k) A

/-! ## The uniform arm is the general arm at the uniform distribution -/

/-- The imported one-time-pad key sample, written with the general sampling arm at
the uniform distribution expression. -/
def uniformSampleGameD : EcGame where
  name := "UniformD"
  locals := ["k"]
  body := [EcStmt.sampleD .bool "k" (EcDistr.uniform .bool)]
  ret := EcExpr.var .bool "k"

/-- The same game, written with the uniform sampling arm. -/
def uniformSampleGame : EcGame where
  name := "Uniform"
  locals := ["k"]
  body := [EcStmt.sample .bool "k"]
  ret := EcExpr.var .bool "k"

/-- The general sampling arm at the uniform distribution expression and the
uniform sampling arm lower to one program, so expressing an existing uniform
sample through `EcStmt.sampleD` leaves its lowering unchanged. -/
theorem lowerClosedGame_uniformSampleGameD :
    lowerClosedGame uniformSampleGameD = lowerClosedGame uniformSampleGame := by
  unfold lowerClosedGame lowerGame
  show SPComp.bind (lowerStmts ProcEnv.empty [] 0
        [EcStmt.sampleD .bool "k" (EcDistr.uniform .bool)] emptyEnv) _
      = SPComp.bind (lowerStmts ProcEnv.empty [] 0
        [EcStmt.sample .bool "k"] emptyEnv) _
  rw [lowerStmts_sampleD_uniform]
  rfl

end CatCrypt.Crypto.EasyCryptImport.NonUniformImport

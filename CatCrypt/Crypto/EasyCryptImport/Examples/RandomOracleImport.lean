/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.EasyCryptImport.FormToProp

/-!
# Worked example: a random oracle with a heap-resident query log

An EasyCrypt module

```
module RO = {
  var log : (int, bool) fmap

  proc query (x : int) : bool = {
    var r;
    if (x \in log) { r <- oget log.[x]; }
    else { r <$ {0,1}; log.[x] <- r; }
    return r;
  }
}
```

as an `EcModule` whose `var log` is an `EcGlobal` at the type code
`EcTy.map .int .bool`. That code interprets to `List (Int × Bool)`, which is not
finite (`logTy_no_fintype`), so the global lives at a `CatCrypt.Core.GLocation`
and its reads and writes lower to `SPComp.gget` / `SPComp.gset`.

An imported statement reads the same global: `EcTerm.glob` takes the global a
program mentions, so `log{&hr}` is a term of the map type and `queryCachedGoal`
is a Hoare judgement about the oracle stated over it.

## Main results

* `query_apply` — the lowered procedure at a heap: read the log, answer from it
  when the point is bound, otherwise sample and bind the point
* `query_apply_cached` — a bound point is answered deterministically, leaving the
  heap untouched
* `query_apply_fresh` — an unbound point is answered uniformly and its answer is
  recorded
* `query_answer_uniform` — the answer to an unbound point is uniform on `Bool`,
  whatever the log holds
* `query_consistent` — two successive queries at the same point agree
* `queryCachedGoal_holds` — an imported `hoare` judgement whose precondition
  reads the log, closed
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.EasyCryptImport.RandomOracleImport

open CatCrypt.Core CatCrypt.Prob CatCrypt.Unary

/-! ## The log global -/

/-- The type code of the query log: a finite map from `int` to `bool`. -/
abbrev logTy : EcTy := .map .int .bool

/-- The log type code is outside the finite subset of `EcTy`. -/
theorem logTy_not_isFin : logTy.isFin = false := rfl

/-- The log type has no `Fintype` instance, so it is not the value type of a
`CatCrypt.Core.Location`. -/
theorem logTy_no_fintype : ¬ Nonempty (Fintype logTy.interp) := by
  rintro ⟨inst⟩
  haveI : Fintype (List (Int × Bool)) := inst
  exact not_finite (List (Int × Bool))

/-- `RO`'s single global `var log`, at a stable heap location id. -/
def logGlobal : EcGlobal := { name := "RO.log", id := 92001, ty := logTy }

@[simp] theorem logGlobal_ty : logGlobal.ty = logTy := rfl

/-- `RO`'s memory footprint. -/
def roLocs : LocSet := {logGlobal.id}

/-! ## The module -/

/-- The module type of `RO`: one procedure `query : int -> bool`. -/
def roInterface : EcInterface where
  names := ["query"]
  sig := fun _ => ⟨.int, .bool⟩

/-- The body of `query`: read the log into a local, answer from it when the point
is bound, otherwise sample an answer and write the extended log back. -/
def roQueryProc : EcProcAt ⟨.int, .bool⟩ where
  params := ["x"]
  body :=
    [ .load logGlobal "m",
      .ite (.mapMem (a := .int) (b := .bool) (.var logTy "m") (.var .int "x"))
        [ .assign .bool "r"
            (.mapGetD (a := .int) (b := .bool) (.var logTy "m") (.var .int "x")
              (.lit false)) ]
        [ .sample .bool "r",
          .store logGlobal
            (.mapSet (.var logTy "m") (.var .int "x") (.var .bool "r")) ] ]
  ret := .var .bool "r"

/-- The imported concrete module `RO`. -/
def roModule : EcModule where
  name := "RO"
  interface := roInterface
  globals := []
  procs := fun _ => roQueryProc

/-- The lowered module. -/
noncomputable def roImpl : ModuleImpl roInterface :=
  lowerModule ProcEnv.empty 0 roModule

/-- The lowered oracle. -/
noncomputable def query (x : Int) : SPComp Bool := roImpl.proc "query" x

/-! ## Closed form of the lowered procedure -/

/-- Lookup in the log held at the oracle's cell. -/
noncomputable def logAt (h : Heap) (x : Int) : Option Bool :=
  EcTy.mapFind (a := .int) (b := .bool) (h.gget logGlobal.loc) x

/-- `logAt` is lookup in the association list the oracle's cell holds. -/
theorem logAt_def (h : Heap) (x : Int) :
    logAt h x = EcTy.mapFind (a := .int) (b := .bool) (h.gget logGlobal.loc) x := rfl

/-- The lowered procedure at a heap: read the cell, and either answer from the log
or sample and extend it. -/
theorem query_apply (x : Int) (h : Heap) :
    query x h =
      if EcTy.mapMem (a := .int) (b := .bool) (h.gget logGlobal.loc) x then
        SDistr.pure
          (EcTy.mapGetD (a := .int) (b := .bool) (h.gget logGlobal.loc) x false, h)
      else
        (SDistr.uniform Bool).bind (fun r =>
          SDistr.pure (r, h.gset logGlobal.loc
            (EcTy.mapSet (a := .int) (b := .bool) (h.gget logGlobal.loc) x r))) := by
  show SPComp.bind
      (lowerStmts ProcEnv.empty [] 0 roQueryProc.body
        (emptyEnv.update "x" ⟨EcTy.int, x⟩))
      (fun env => SPComp.pure (evalExpr roQueryProc.ret env)) h = _
  by_cases hm : EcTy.mapMem (a := .int) (b := .bool) (h.gget logGlobal.loc) x = true
  · rw [if_pos hm]
    -- `evalExpr`'s comparing arms branch on the key code's `hasEq`, so the set
    -- needs both the lemma that reduces that condition and the one that
    -- reduces the branch it leaves.
    simp only [roQueryProc, lowerStmts_load, lowerStmts_ite, lowerStmts_assign,
      lowerStmts_nil, evalCond_eq, evalExpr, EcTy.hasEq_int, dite_true,
      logGlobal_ty, Env.read_update_same,
      Env.read_update_ne _ EcTy.int "m" "x" _ (by decide), SPComp.bind, SPComp.gget,
      SPComp.pure, SDistr.pure_bind, hm, if_true]
  · have hm' : EcTy.mapMem (a := .int) (b := .bool) (h.gget logGlobal.loc) x = false := by
      simpa using hm
    rw [if_neg (by simp [hm'])]
    simp only [roQueryProc, lowerStmts_load, lowerStmts_ite, lowerStmts_sample,
      lowerStmts_store, lowerStmts_nil, sampleFin_bool, evalCond_eq, evalExpr,
      EcTy.hasEq_int, dite_true,
      logGlobal_ty, Env.read_update_same, Env.read_update_ne _ EcTy.int "m" "x" _ (by decide),
      Env.read_update_ne _ logTy "r" "m" _ (by decide),
      Env.read_update_ne _ EcTy.int "r" "x" _ (by decide),
      SPComp.bind, SPComp.gget, SPComp.pure, SDistr.pure_bind]
    rw [if_neg hm]
    simp only [SPComp.bind, SPComp.gset, SPComp.sample, SPComp.pure,
      SDistr.pure_bind, SDistr.bind_assoc]
    simp only [Env.read_update_same]

/-! ## A bound point is deterministic -/

/-- A point already in the log is answered from the log, leaving the heap
untouched. -/
theorem query_apply_cached (x : Int) (h : Heap) (r : Bool) (hc : logAt h x = some r) :
    query x h = SDistr.pure (r, h) := by
  rw [logAt_def] at hc
  have hm : EcTy.mapMem (a := .int) (b := .bool) (h.gget logGlobal.loc) x = true := by
    rw [EcTy.mapMem, hc]; rfl
  have hg : EcTy.mapGetD (a := .int) (b := .bool) (h.gget logGlobal.loc) x false = r := by
    rw [EcTy.mapGetD, hc]; rfl
  rw [query_apply, if_pos hm, hg]

/-! ## A fresh point is uniform -/

/-- A point absent from the log is answered uniformly and its answer is recorded. -/
theorem query_apply_fresh (x : Int) (h : Heap) (hc : logAt h x = none) :
    query x h =
      (SDistr.uniform Bool).bind (fun r =>
        SDistr.pure (r, h.gset logGlobal.loc
          (EcTy.mapSet (a := .int) (b := .bool) (h.gget logGlobal.loc) x r))) := by
  rw [logAt_def] at hc
  have hm : EcTy.mapMem (a := .int) (b := .bool) (h.gget logGlobal.loc) x = false := by
    rw [EcTy.mapMem, hc]; rfl
  rw [query_apply, if_neg (by simp [hm])]

/-- The answer to a fresh point is uniform on `Bool`, independently of the log
contents. -/
theorem query_answer_uniform (x : Int) (h : Heap) (hc : logAt h x = none) :
    (query x h).bind (fun p => SDistr.pure p.1) = SDistr.uniform Bool := by
  simp only [query_apply_fresh x h hc, SDistr.bind_assoc, SDistr.pure_bind, SDistr.bind_pure]

/-- Every point is fresh on the empty heap, so the freshness hypothesis is
satisfiable. -/
theorem query_empty_uniform (x : Int) :
    (query x Heap.empty).bind (fun p => SDistr.pure p.1) = SDistr.uniform Bool :=
  query_answer_uniform x Heap.empty (by rw [logAt_def, Heap.gget_empty]; rfl)

/-! ## The log makes the oracle consistent -/

/-- After a fresh answer is recorded, the point is bound to it. -/
theorem logAt_after_fresh (x : Int) (r : Bool) (h : Heap) :
    logAt (h.gset logGlobal.loc
      (EcTy.mapSet (a := .int) (b := .bool) (h.gget logGlobal.loc) x r)) x = some r := by
  rw [logAt_def, Heap.gget_gset_same, EcTy.mapFind_mapSet_same]

/-- Querying the same point twice returns the same value: the second query reads
the entry the first one wrote. -/
theorem query_consistent (x : Int) :
    SPComp.bind (query x) (fun r₁ =>
      SPComp.bind (query x) (fun r₂ => SPComp.pure (r₁, r₂))) =
    SPComp.bind (query x) (fun r => SPComp.pure (r, r)) := by
  funext h
  simp only [SPComp.bind]
  cases hc : logAt h x with
  | some r =>
      rw [query_apply_cached x h r hc, SDistr.pure_bind, SDistr.pure_bind,
        query_apply_cached x h r hc, SDistr.pure_bind]
  | none =>
      rw [query_apply_fresh x h hc, SDistr.bind_assoc, SDistr.bind_assoc]
      exact congrArg _ (funext fun r => by
        rw [SDistr.pure_bind, SDistr.pure_bind,
          query_apply_cached x _ r (logAt_after_fresh x r h), SDistr.pure_bind])

/-! ## An imported statement over the log

EasyCrypt's

```
lemma query_cached :
  hoare[RO.query : arg = 0 /\ RO.log = [(0, true)]
        ==> res /\ RO.log = [(0, true)]].
```

as an `EcForm`. Both its precondition and its postcondition read the module
global `RO.log`, at the judgement's initial and final memory, which is
`EcTerm.glob` at the code `map int bool` — a term of a type with no `Fintype`
instance. -/

/-- The signature of `RO.query`. -/
def roSig : EcSig := ⟨.int, .bool⟩

/-- The environment the imported statement resolves `RO.query` against. -/
noncomputable def roEnv : ProcEnv :=
  ProcEnv.empty.bindProc "RO./query" (s := roSig) query

theorem roEnv_query : roEnv "RO./query" roSig = query := rfl

/-- The log holding the single binding `0 ↦ true`. -/
def logAtZero : logTy.interp := [((0 : Int), true)]

/-- The imported form of `query_cached`: from a memory whose `RO.log` is the
single binding `0 ↦ true`, the query at `0` returns `true` and leaves the log as
it was. -/
def queryCachedForm : EcForm :=
  .hoare "RO./query" roSig (.lit (t := .int) (0 : Int))
    (.eqT (t := logTy) (.glob logGlobal (.side .cur)) (.lit (t := logTy) logAtZero))
    (.and (.holds (.res .bool .cur))
      (.eqT (t := logTy) (.glob logGlobal (.side .cur)) (.lit (t := logTy) logAtZero)))

/-- The imported statement, as a goal. -/
noncomputable def queryCachedGoal : Prop := importedProp roEnv queryCachedForm

/-- The translated goal is the pHL judgement about the lowered oracle: from a
memory whose log cell holds the single binding, the query at `0` returns `true`
and the log cell still holds that binding. -/
theorem queryCachedGoal_eq :
    queryCachedGoal
      = pHoare (fun h => h.gget logGlobal.loc = logAtZero) (query 0)
          (fun r h' => r = true ∧ h'.gget logGlobal.loc = logAtZero) := rfl

/-- **The imported goal, closed.** Both sides of the judgement are terms over a
countable-typed global, and the judgement they guard is a theorem of CatCrypt. -/
theorem queryCachedGoal_holds : queryCachedGoal := by
  rw [queryCachedGoal_eq]
  intro h hpre r h' hsupp
  have hc : logAt h 0 = some true := by
    rw [logAt_def, hpre]; rfl
  rw [query_apply_cached 0 h true hc] at hsupp
  have hmem : ((true, h) : Bool × Heap) = (r, h') := by
    rwa [← SDistr.mem_support_pure_iff]
  cases hmem
  exact ⟨rfl, hpre⟩

end CatCrypt.Crypto.EasyCryptImport.RandomOracleImport

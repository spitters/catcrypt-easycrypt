/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.EasyCryptImport.Json
import CatCrypt.Crypto.EasyCryptImport.Examples.NonUniformImport
import CatCrypt.NonUniform.UnaryRules

/-!
# Worked example: binder identity, and the bind, product, rescaling and
restriction operators

One exporter fixture, `distrbind.expected.json`, carries five games. Two of them
put a lambda binder and a program variable at one source name; the other three
sample from `dlet`, ``(`*`)`` and `dscale (drestrict …)`.

## The two games at one source name

```
module Bound = {                          module Free = {
  proc main() : bool = {                    proc main() : bool = {
    var b : bool; var y : bool;               var b : bool; var y : bool;
    b <- true;                                b <- true;
    y <$ dmap dbool (fun (b : bool) => b);    y <$ dmap dbool (fun (c : bool) => b);
    return y;                                 return y;
  }                                         }
}                                         }
```

In `Bound` the lambda binder is written `b`, the source name the program variable
already has, and the body reads the binder: EasyCrypt resolves the occurrence to
the binder and exports it as a stamped identifier. In `Free` the binder is `c` and
the body reads the program variable, exported as a `PVloc`. The two denote
different distributions — `Bound` returns a uniform bit, `Free` returns `true` —
and the difference is carried entirely by which identifier the body's occurrence
names.

A valuation keyed by source names alone cannot hold that difference: it stores the
binder of `Free` under the key the program variable `b` occupies as soon as that
binder is named `b`, and the body then reads the sampled value instead of `true`.
`lowerClosedGame_freeGame` is stated for a binder of *any* source name, `"b"`
included, and `freeGame_shadowed_ne_boundGame` is the pair of games that a
name-keyed valuation would identify.

## The three operator games

```
module Bind = {                   module Product = {              module Scaled = {
  proc main() : bool = {            proc main() : bool = {          proc main() : bool = {
    var x : bool;                     var p : bool * bool;            var x : bool;
    x <$ dlet dbool                   p <$ dunit true `*` dbool;      x <$ dscale (drestrict
      (fun (b : bool) =>              return p.`1;                       dbool (fun (b : bool) => b));
        dunit (!b));                }                                 return x;
    return x;                     }                                 }
  }                                                               }
}
```

`Bind` is the bind at a point mass, which is the pushforward EasyCrypt's
`dmap d f = dlet d (dunit \o f)` defines; `Product` reads the first component of
an independent pair whose first factor is a point mass; `Scaled` is the rescaled
restriction that EasyCrypt's `dcond d p = dscale (drestrict d p)` defines, at a
predicate one value of positive weight satisfies.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.EasyCryptImport.DistrBindImport

open Lean (Json)
open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.EasyCryptBridge CatCrypt.Crypto.ForkingLemma
open CatCrypt.NonUniform
open scoped ENNReal

attribute [local implicit_reducible] EcTy.isFin

/-! ## The fixture -/

/-- The exporter's output for the binder and distribution-operator theory, as
text. -/
private def distrBindExportText : String := include_str "../distrbind.expected.json"

/-- The exporter's output for the binder and distribution-operator theory. -/
private def distrBindExport : Json :=
  match Json.parse distrBindExportText with
  | .ok j => j
  | .error _ => Json.null

-- The fixture parses.
#guard (match distrBindExport with | Json.obj _ => true | _ => false)

/-- The lowering of a closed game, with its three fields exposed. -/
private theorem lowerClosedGame_eq (g : EcGame) :
    lowerClosedGame OpEnv.empty g
      = SPComp.bind (lowerStmts ProcEnv.empty g.procs 0 g.body (emptyEnv OpEnv.empty))
          (fun env => SPComp.pure (evalExpr g.ret env)) := rfl

/-! ## The two games at one source name -/

/-- The imported `Bound`: the lambda binder shadows the program variable `b`, and
the body reads the binder. -/
def boundGame (k : EcVarId) : EcGame where
  name := "Bound"
  locals := ["b", "y"]
  body :=
    [EcStmt.assign .bool "b" (EcExpr.lit (t := .bool) true),
     EcStmt.sampleD .bool "y"
       (EcDistr.map (EcDistr.uniform .bool) k (EcExpr.var .bool k))]
  ret := EcExpr.var .bool "y"

/-- The imported `Free`: the lambda binder is a further identifier, and the body
reads the program variable `b`. -/
def freeGame (k : EcVarId) : EcGame where
  name := "Free"
  locals := ["b", "y"]
  body :=
    [EcStmt.assign .bool "b" (EcExpr.lit (t := .bool) true),
     EcStmt.sampleD .bool "y"
       (EcDistr.map (EcDistr.uniform .bool) k (EcExpr.var .bool "b"))]
  ret := EcExpr.var .bool "y"

-- `Bound` imports with a stamped binder that the body's occurrence is.
#guard (match importGame ecPrelude "Bound" distrBindExport with
        | .ok { name := "Bound", locals := ["b", "y"], procs := [],
                body := [.assign .bool "b" (.lit true),
                         .sampleD .bool "y"
                           (.map (.uniform _ _) k (.var .bool z))],
                ret := .var .bool "y" } =>
          k.stamp.isSome && k.name == "b" && z == k
        | _ => false)

-- `Free` imports with the body's occurrence at the program variable `b`, which
-- carries no stamp, under a stamped binder of another source name.
#guard (match importGame ecPrelude "Free" distrBindExport with
        | .ok { name := "Free", locals := ["b", "y"], procs := [],
                body := [.assign .bool "b" (.lit true),
                         .sampleD .bool "y"
                           (.map (.uniform _ _) k (.var .bool z))],
                ret := .var .bool "y" } =>
          k.stamp.isSome && z == EcVarId.ofName "b" && k != z
        | _ => false)

/-! ### What each denotes -/

/-- The pushforward along a body that reads the program variable `b` is the point
mass at that variable's value, whatever the binder is: extending the valuation at
a stamped identifier leaves the program variable of any source name readable. -/
theorem evalDistr_freeDistr (k : EcVarId) (hk : k.stamp.isSome) (env : Env) :
    evalDistr (EcDistr.map (EcDistr.uniform .bool) k (EcExpr.var .bool "b")) env
      = SDistr.pure (env.read .bool (EcVarId.ofName "b")) := by
  have hne : EcVarId.ofName "b" ≠ k := by
    intro h
    rw [← h] at hk
    simp at hk
  have hbody : ∀ v : Bool,
      evalExpr (EcExpr.var .bool (EcVarId.ofName "b"))
          (env.update k ⟨EcTy.bool, v⟩)
        = env.read .bool (EcVarId.ofName "b") := fun v =>
    Env.read_update_ne env .bool k (EcVarId.ofName "b") ⟨EcTy.bool, v⟩ hne
  rw [evalDistr_map, evalDistr_uniform]
  simp only [hbody]
  letI := EcTy.bool.fintypeOfIsFin rfl
  exact bind_const_of_mass_one SDistr.mass_uniform _

/-- The pushforward along a body that reads the binder is the distribution the
binder ranges over. -/
theorem evalDistr_boundDistr (k : EcVarId) (env : Env) :
    evalDistr (EcDistr.map (EcDistr.uniform .bool) k (EcExpr.var .bool k)) env
      = evalDistr (EcDistr.uniform .bool) env := by
  have hbody : ∀ v : Bool,
      evalExpr (EcExpr.var .bool k) (env.update k ⟨EcTy.bool, v⟩) = v := fun v =>
    Env.read_update_same env .bool k v
  rw [evalDistr_map]
  simp only [hbody]
  exact SDistr.bind_pure _

/-- **The imported `Free` is the constant `true`, whatever its binder is named.**
The statement quantifies over the binder's source name, so it covers the name the
program variable `b` already carries: the binder's rebinding does not reach the
body's occurrence of the program variable. -/
theorem lowerClosedGame_freeGame (k : EcVarId) (hk : k.stamp.isSome) :
    lowerClosedGame OpEnv.empty (freeGame k) = SPComp.pure true := by
  rw [lowerClosedGame_eq]
  show SPComp.bind
      (lowerStmts ProcEnv.empty [] 0
        [EcStmt.assign .bool "b" (EcExpr.lit (t := .bool) true),
         EcStmt.sampleD .bool "y"
           (EcDistr.map (EcDistr.uniform .bool) k (EcExpr.var .bool "b"))] (emptyEnv OpEnv.empty))
      (fun env => SPComp.pure (evalExpr (EcExpr.var .bool "y") env)) = SPComp.pure true
  rw [lowerStmts_assign, lowerStmts_sampleD, evalDistr_freeDistr k hk]
  simp only [lowerStmts_nil, sampleFrom_pure, SPComp.pure_bind, evalExpr,
    Env.read_update_same]

/-- **The imported `Bound` is a uniform bit.** -/
theorem lowerClosedGame_boundGame (k : EcVarId) :
    lowerClosedGame OpEnv.empty (boundGame k) = SPComp.sample Bool := by
  rw [lowerClosedGame_eq]
  show SPComp.bind
      (lowerStmts ProcEnv.empty [] 0
        [EcStmt.assign .bool "b" (EcExpr.lit (t := .bool) true),
         EcStmt.sampleD .bool "y"
           (EcDistr.map (EcDistr.uniform .bool) k (EcExpr.var .bool k))] (emptyEnv OpEnv.empty))
      (fun env => SPComp.pure (evalExpr (EcExpr.var .bool "y") env)) = SPComp.sample Bool
  rw [lowerStmts_assign, lowerStmts_sampleD, evalDistr_boundDistr k,
    sampleFrom_evalDistr_uniform]
  simp only [lowerStmts_nil, SPComp.bind_assoc, SPComp.pure_bind, evalExpr,
    Env.read_update_same, SPComp.bind_pure, sampleFin_bool]

/-- The imported `Free` returns `true` with probability one. -/
theorem prTrue_freeGame (k : EcVarId) (hk : k.stamp.isSome) (h : Heap) :
    prTrue (lowerClosedGame OpEnv.empty (freeGame k)) h = 1 := by
  rw [lowerClosedGame_freeGame k hk, prTrue_pure_bool]
  simp

/-- The imported `Bound` returns `true` with probability one half. -/
theorem prTrue_boundGame (k : EcVarId) (h : Heap) :
    prTrue (lowerClosedGame OpEnv.empty (boundGame k)) h = 2⁻¹ := by
  rw [lowerClosedGame_boundGame k, ← sampleFrom_uniform Bool,
    NonUniform.prTrue_sampleFrom, SDistr.uniform_apply_some]
  norm_num [Fintype.card_bool]

/-- **The two games at one source name are different programs.** With the binder
of `Free` carrying the program variable's source name, the two games agree in
every source name they mention and differ only in which identifier the body's
occurrence is. A valuation keyed by source names alone identifies them; this
disequality is what that identification would contradict. -/
theorem freeGame_shadowed_ne_boundGame (s : Nat) :
    lowerClosedGame OpEnv.empty (freeGame ⟨"b", some s⟩)
      ≠ lowerClosedGame OpEnv.empty (boundGame ⟨"b", some s⟩) := by
  intro heq
  have h1 : prTrue (lowerClosedGame OpEnv.empty (freeGame ⟨"b", some s⟩)) Heap.empty = 1 :=
    prTrue_freeGame _ rfl Heap.empty
  have h2 : prTrue (lowerClosedGame OpEnv.empty (boundGame ⟨"b", some s⟩)) Heap.empty = 2⁻¹ :=
    prTrue_boundGame _ Heap.empty
  rw [heq, h2] at h1
  exact absurd h1 (by norm_num)

/-- The imported `Free` does not depend on the source name its binder carries. -/
theorem lowerClosedGame_freeGame_rename (k k' : EcVarId)
    (hk : k.stamp.isSome) (hk' : k'.stamp.isSome) :
    lowerClosedGame OpEnv.empty (freeGame k) = lowerClosedGame OpEnv.empty (freeGame k') := by
  rw [lowerClosedGame_freeGame k hk, lowerClosedGame_freeGame k' hk']

/-! ## The bind -/

/-- The imported `Bind`: a sample from `dlet dbool (fun b => dunit (!b))`. -/
def bindGame (k : EcVarId) : EcGame where
  name := "Bind"
  locals := ["x"]
  body :=
    [EcStmt.sampleD .bool "x"
       (EcDistr.letD (EcDistr.uniform .bool) k
         (EcDistr.point (EcExpr.bnot (EcExpr.var .bool k))))]
  ret := EcExpr.var .bool "x"

/-- The same sample written as a pushforward, which is what EasyCrypt's
`dmap d f = dlet d (dunit \o f)` makes it. -/
def bindAsMapGame (k : EcVarId) : EcGame where
  name := "Bind"
  locals := ["x"]
  body :=
    [EcStmt.sampleD .bool "x"
       (EcDistr.map (EcDistr.uniform .bool) k (EcExpr.bnot (EcExpr.var .bool k)))]
  ret := EcExpr.var .bool "x"

-- `Bind` imports as the bind whose second argument is a point mass under the
-- binder, and whose body reads the binder.
#guard (match importGame ecPrelude "Bind" distrBindExport with
        | .ok { name := "Bind", locals := ["x"], procs := [],
                body := [.sampleD .bool "x"
                           (.letD (.uniform _ _) k (.point (.bnot (.var .bool z))))],
                ret := .var .bool "x" } => k.stamp.isSome && z == k
        | _ => false)

/-- **A bind at a point mass is the pushforward.** The two imported games lower to
one `SPComp Bool`, which is the EasyCrypt definition `dmap d f = dlet d (dunit \o f)`
at the level of imported programs. -/
theorem lowerClosedGame_bindGame (k : EcVarId) :
    lowerClosedGame OpEnv.empty (bindGame k) = lowerClosedGame OpEnv.empty (bindAsMapGame k) := by
  rw [lowerClosedGame_eq, lowerClosedGame_eq]
  show SPComp.bind
      (lowerStmts ProcEnv.empty [] 0
        [EcStmt.sampleD .bool "x"
          (EcDistr.letD (EcDistr.uniform .bool) k
            (EcDistr.point (EcExpr.bnot (EcExpr.var .bool k))))] (emptyEnv OpEnv.empty))
      (fun env => SPComp.pure (evalExpr (EcExpr.var .bool "x") env))
    = SPComp.bind
      (lowerStmts ProcEnv.empty [] 0
        [EcStmt.sampleD .bool "x"
          (EcDistr.map (EcDistr.uniform .bool) k
            (EcExpr.bnot (EcExpr.var .bool k)))] (emptyEnv OpEnv.empty))
      (fun env => SPComp.pure (evalExpr (EcExpr.var .bool "x") env))
  rw [lowerStmts_sampleD, lowerStmts_sampleD, evalDistr_letD_point]

/-- Boolean negation as a bijection. -/
private def notEquiv : Bool ≃ Bool := ⟨not, not, Bool.not_not, Bool.not_not⟩

/-- The imported `Bind` denotes the pushforward of the uniform distribution along
negation, which is the uniform distribution. -/
theorem evalDistr_bindDistr (k : EcVarId) (env : Env) :
    evalDistr (EcDistr.letD (EcDistr.uniform .bool) k
        (EcDistr.point (EcExpr.bnot (EcExpr.var .bool k)))) env
      = evalDistr (EcDistr.uniform .bool) env := by
  have hbody : ∀ v : Bool,
      evalExpr (EcExpr.bnot (EcExpr.var .bool k)) (env.update k ⟨EcTy.bool, v⟩)
        = !v := by
    intro v
    simp only [evalExpr, Env.read_update_same]
  rw [evalDistr_letD, evalDistr_uniform]
  simp only [evalDistr_point, hbody]
  exact SDistr.uniform_bind_bij notEquiv

/-- The imported `Bind` is a uniform bit: negating a uniform bit is a uniform
bit. -/
theorem lowerClosedGame_bindGame_eq_sample (k : EcVarId) :
    lowerClosedGame OpEnv.empty (bindGame k) = SPComp.sample Bool := by
  rw [lowerClosedGame_eq]
  show SPComp.bind
      (lowerStmts ProcEnv.empty [] 0
        [EcStmt.sampleD .bool "x"
          (EcDistr.letD (EcDistr.uniform .bool) k
            (EcDistr.point (EcExpr.bnot (EcExpr.var .bool k))))] (emptyEnv OpEnv.empty))
      (fun env => SPComp.pure (evalExpr (EcExpr.var .bool "x") env)) = SPComp.sample Bool
  rw [lowerStmts_sampleD, evalDistr_bindDistr k, sampleFrom_evalDistr_uniform]
  simp only [lowerStmts_nil, SPComp.bind_assoc, SPComp.pure_bind, evalExpr,
    Env.read_update_same, SPComp.bind_pure, sampleFin_bool]

/-! ## The independent product -/

/-- The imported `Product`: a sample from `dunit true `*` dbool`, returning the
first component. -/
def productGame : EcGame where
  name := "Product"
  locals := ["p"]
  body :=
    [EcStmt.sampleD (.prod .bool .bool) "p"
       (EcDistr.prod (EcDistr.point (EcExpr.lit (t := .bool) true))
         (EcDistr.uniform .bool))]
  ret := EcExpr.fst (a := .bool) (b := .bool) (EcExpr.var (.prod .bool .bool) "p")

-- `Product` imports as the independent product of the point mass and the uniform
-- distribution, at the two component codes the pair carrier names.
#guard (match importGame ecPrelude "Product" distrBindExport with
        | .ok { name := "Product", locals := ["p"], procs := [],
                body := [.sampleD (.prod .bool .bool) "p"
                           (.prod (.point (.lit true)) (.uniform _ _))],
                ret := .fst (.var (.prod .bool .bool) "p") } => true
        | _ => false)

/-- **The imported `Product` is the constant `true`.** The first component is drawn
from a point mass and the second, which the game discards, from a total
distribution. -/
theorem lowerClosedGame_productGame : lowerClosedGame OpEnv.empty productGame = SPComp.pure true := by
  rw [lowerClosedGame_eq]
  show SPComp.bind
      (lowerStmts ProcEnv.empty [] 0
        [EcStmt.sampleD (.prod .bool .bool) "p"
          (EcDistr.prod (EcDistr.point (EcExpr.lit (t := .bool) true))
            (EcDistr.uniform .bool))] (emptyEnv OpEnv.empty))
      (fun env => SPComp.pure
        (evalExpr (EcExpr.fst (a := .bool) (b := .bool)
          (EcExpr.var (.prod .bool .bool) "p")) env)) = SPComp.pure true
  rw [lowerStmts_sampleD]
  simp only [lowerStmts_nil, SPComp.bind_assoc, SPComp.pure_bind, evalExpr,
    Env.read_update_same, evalDistr_prod, evalDistr_point, evalDistr_uniform]
  have hfst : ∀ D : SDistr (EcTy.bool.interp × EcTy.bool.interp),
      SPComp.bind (NonUniform.sampleFrom D) (fun v => SPComp.pure v.1)
        = NonUniform.sampleFrom (D.bind fun v => SDistr.pure v.1) := by
    intro D
    rw [← sampleFrom_bind_sampleFrom]
    simp only [sampleFrom_pure]
  letI := EcTy.bool.fintypeOfIsFin rfl
  exact (hfst _).trans (by rw [prod_bind_fst SDistr.mass_uniform]; exact sampleFrom_pure _)

/-! ## The rescaled restriction -/

/-- The imported `Scaled`: a sample from `dscale (drestrict dbool (fun b => b))`. -/
def scaledGame (k : EcVarId) : EcGame where
  name := "Scaled"
  locals := ["x"]
  body :=
    [EcStmt.sampleD .bool "x"
       (EcDistr.scale (EcDistr.restrict (EcDistr.uniform .bool) k (EcExpr.var .bool k)))]
  ret := EcExpr.var .bool "x"

-- `Scaled` imports as the rescaling of a restriction, each at its own
-- constructor.
#guard (match importGame ecPrelude "Scaled" distrBindExport with
        | .ok { name := "Scaled", locals := ["x"], procs := [],
                body := [.sampleD .bool "x"
                           (.scale (.restrict (.uniform _ _) k (.var .bool z)))],
                ret := .var .bool "x" } => k.stamp.isSome && z == k
        | _ => false)

/-- **A rescaled restriction is a conditioning.** This is the EasyCrypt definition
`dcond d p = dscale (drestrict d p)` at the level of imported distributions. -/
theorem evalDistr_scaledDistr (k : EcVarId) (env : Env) :
    evalDistr (EcDistr.scale (EcDistr.restrict (EcDistr.uniform .bool) k
        (EcExpr.var .bool k))) env
      = evalDistr (EcDistr.cond (EcDistr.uniform .bool) k (EcExpr.var .bool k)) env := rfl

/-- **The imported `Scaled` is the constant `true`.** The restriction keeps the
single outcome the predicate admits, and the rescaling gives it the whole mass. -/
theorem lowerClosedGame_scaledGame (k : EcVarId) :
    lowerClosedGame OpEnv.empty (scaledGame k) = SPComp.pure true := by
  rw [lowerClosedGame_eq]
  show SPComp.bind
      (lowerStmts ProcEnv.empty [] 0
        [EcStmt.sampleD .bool "x"
          (EcDistr.scale (EcDistr.restrict (EcDistr.uniform .bool) k
            (EcExpr.var .bool k)))] (emptyEnv OpEnv.empty))
      (fun env => SPComp.pure (evalExpr (EcExpr.var .bool "x") env)) = SPComp.pure true
  have hcond :
      evalDistr (EcDistr.cond (EcDistr.uniform .bool) k (EcExpr.var .bool k)) (emptyEnv OpEnv.empty)
        = SDistr.pure true :=
    NonUniformImport.evalDistr_cond_uniform_eq_pure .bool rfl k
      (EcExpr.var .bool k) (emptyEnv OpEnv.empty) true
      (fun b hb => by simpa [evalExpr, Env.read_update_same] using hb)
      (by simp [evalExpr, Env.read_update_same])
  rw [lowerStmts_sampleD, evalDistr_scaledDistr, hcond]
  simp [lowerStmts_nil, SPComp.pure_bind, evalExpr, Env.read_update_same]

end CatCrypt.Crypto.EasyCryptImport.DistrBindImport

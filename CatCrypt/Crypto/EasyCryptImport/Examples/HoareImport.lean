/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.EasyCryptImport.FormJson
import CatCrypt.Crypto.EasyCryptImport.FormToProp
import CatCryptCore.Unary.Rules

/-!
# Worked example: an imported Hoare judgement from source text to a closed goal

This module takes one export — `hoare.expected.json`, the output of `ec2json` on
an EasyCrypt file declaring a module with one `bool` global and two argument-free
procedures, together with four judgements about them — and carries the module and
one of the judgements through the whole importer: JSON, AST, translation, proof.

The source the export comes from is

```
module Coin = {
  var b : bool

  proc set() : bool  = { var r : bool; b <- true; r <- b; return r; }
  proc toss() : bool = { var c : bool; c <$ {0,1}; b <- c; return c; }
}.

lemma set_sets : hoare [Coin.set : Coin.b = false ==> res /\ Coin.b = true].
```

The three `phoare` lemmas of the same source are decoded and pinned in
`FormJson.lean`, one per `hoarecmp` comparison. `set_sets` is the one carried to a
proof here; `tossLosslessGoal_eq` records the CatCrypt shape a bounded Hoare
judgement at `EcCmp.eq` translates to.

## Why the judgement's argument is the unit value

`EcForm.hoare` carries the argument the procedure is applied to, and EasyCrypt
leaves it implicit: a judgement's assertions speak about the procedure's formal
parameter. The argument is therefore reconstructible only for a procedure that
takes none, which is why both procedures of `Coin` are argument-free
(`FormJson.judgementArg`).

## What is machine-checked, and where the `#guard`s come in

`decodeModule` and `decodeForm` recurse on the `jsonSize` measure, and well-founded
recursion is not definitionally reducible, so the AST values below are written out
and each is pinned to the decoder's output by a `#guard`. The `#guard`s run when
this module is built, so a change in the exporter, the fixture or the decoder that
moved one of these values would fail the build. A field whose type is a projection
out of another field is read back with a recognizer (`isGlobReadAt`, `isBoolLit`,
`isBoolLitExpr`, `EcExpr.varName`) rather than matched by a pattern, because a
pattern there would need an index equation the dependent pattern matcher cannot
solve; the comment at each guard says which field and why. One field, the return
expression of a decoded procedure, is left open — `coinImpl_set` and
`coinImpl_toss` record instead the computation each whole procedure lowers to.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.EasyCryptImport.HoareImport

open CatCrypt.Core CatCrypt.Prob CatCrypt.Unary CatCrypt.Crypto
open CatCrypt.Crypto.EasyCryptBridge
open scoped ENNReal

/-! ## The module

`Coin.b` is the module's one `var` declaration, so it is a heap `Location`, at the
id `decodeModule` assigns it from the base id 0. -/

/-- `Coin`'s single global `var b : bool`. -/
def bGlobal : EcGlobal := { name := "Top.Coin./b", id := 0, ty := .bool }

/-- The `Location` `Coin.b` occupies: its code is finite, so the cell its
`EcGlobal` denotes is also a finite-typed location. -/
def bLoc : Location := bGlobal.finLoc rfl

/-- The module type of `Coin`, in the order the export declares its names. -/
def coinInterface : EcInterface where
  names := ["toss", "set"]
  sig := fun _ => ⟨.unit, .bool⟩

/-- The imported module `Coin`. `set` writes `true` to the global and returns what
it reads back; `toss` samples a bit, stores it, and returns it. -/
def coinModule : EcModule where
  name := "Coin"
  interface := coinInterface
  globals := [bGlobal]
  procs := fun p =>
    match p with
    | "set" =>
        { param := anonymousLocal
          body := [.store bGlobal (.lit true), .load bGlobal "r"]
          ret := .var .bool "r" }
    | "toss" =>
        { param := anonymousLocal
          body := [.sample .bool "c", .store bGlobal (.var .bool "c")]
          ret := .var .bool "c" }
    | _ => { param := anonymousLocal, body := [], ret := .lit default }

/-- Whether an expression is the `bool` literal `v`. The type index is quantified,
so this applies to the expression of an `EcStmt.store`, whose index is the stored
global's own `ty` field. -/
private def isBoolLitExpr {t : EcTy} (e : EcExpr t) (v : Bool) : Bool :=
  match t, e.litValue with
  | .bool, some w => w == v
  | _, _ => false

-- The export's module decodes to that interface and that global.
#guard (match importModule ecPrelude "Coin" hoareExport with
        | .ok M =>
          M.name == "Coin" && M.interface.names == ["toss", "set"]
            && M.interface.sig "set" == { arg := .unit, res := .bool }
            && M.interface.sig "toss" == { arg := .unit, res := .bool }
            && (match M.globals with
                | [{ name := "Top.Coin./b", id := 0, ty := .bool }] => true
                | _ => false)
        | _ => false)

-- `set` decodes to the store of `true` followed by the load into `r`. Its formal
-- parameter is the anonymous name a procedure without arguments gets.
--
-- Two fields have a type that is a projection out of a field rather than a field:
-- `EcStmt.store g e` types `e` at `g.ty`, and `EcProcAt s` types `ret` at `s.res`
-- with `s` fixed by the enclosing `M`. `isBoolLitExpr` reads the stored literal
-- back; the return expression is left open, and `coinImpl_set` below records the
-- computation the whole procedure lowers to.
#guard (match importModule ecPrelude "Coin" hoareExport with
        | .ok M =>
          (match M.procs "set" with
           | { param := "_", body := [.store g₁ e₁, .load g₂ "r"], ret := _ } =>
             g₁.name == "Top.Coin./b" && g₁.id == 0 && g₁.ty == .bool
               && isBoolLitExpr e₁ true
               && g₂.name == "Top.Coin./b" && g₂.id == 0 && g₂.ty == .bool
           | _ => false)
        | _ => false)

-- `toss` decodes to the uniform sample followed by the store of the sampled
-- local, read back with `EcExpr.varName` for the same reason.
#guard (match importModule ecPrelude "Coin" hoareExport with
        | .ok M =>
          (match M.procs "toss" with
           | { param := "_", body := [.sample .bool "c", .store g e], ret := _ } =>
             g.name == "Top.Coin./b" && g.id == 0 && g.ty == .bool
               && e.varName == some "c"
           | _ => false)
        | _ => false)

/-- The lowered module: two `SPComp` procedures sharing the location `Coin.b`. -/
noncomputable def coinImpl : ModuleImpl coinInterface :=
  lowerModule ProcEnv.empty 0 coinModule

/-! ## Closed forms of the two lowered procedures -/

theorem coinImpl_set :
    coinImpl.proc "set" ()
      = SPComp.bind (SPComp.set bLoc true)
          (fun _ => SPComp.bind (SPComp.get bLoc) SPComp.pure) := by
  show SPComp.bind
      (lowerStmts ProcEnv.empty [] 0
        [EcStmt.store bGlobal (EcExpr.lit (t := .bool) true), EcStmt.load bGlobal "r"]
        (emptyEnv.update anonymousLocal ⟨EcTy.unit, ()⟩))
      (fun env => SPComp.pure (evalExpr (EcExpr.var .bool "r") env)) = _
  simp only [lowerStmts_store_finLoc (g := bGlobal) (hfin := rfl),
    lowerStmts_load_finLoc (g := bGlobal) (hfin := rfl), lowerStmts_nil, SPComp.bind_assoc,
    SPComp.pure_bind, evalExpr]
  rfl

theorem coinImpl_toss :
    coinImpl.proc "toss" ()
      = SPComp.bind (SPComp.sample Bool)
          (fun c => SPComp.bind (SPComp.set bLoc c) (fun _ => SPComp.pure c)) := by
  show SPComp.bind
      (lowerStmts ProcEnv.empty [] 0
        [EcStmt.sample .bool "c", EcStmt.store bGlobal (EcExpr.var .bool "c")]
        (emptyEnv.update anonymousLocal ⟨EcTy.unit, ()⟩))
      (fun env => SPComp.pure (evalExpr (EcExpr.var .bool "c") env)) = _
  simp only [lowerStmts_sample, lowerStmts_store_finLoc (g := bGlobal) (hfin := rfl),
    lowerStmts_nil, sampleFin_bool, SPComp.bind_assoc, SPComp.pure_bind, evalExpr,
    Env.read_update_same]
  rfl

/-! ## The resolution environment

A judgement names its procedure by the path the exporter writes, `Top.Coin./set`,
so the two procedures are bound under those paths. -/

/-- The signature of both procedures of `Coin`: `proc p() : bool`. -/
def coinSig : EcSig := ⟨.unit, .bool⟩

/-- The environment the imported statements resolve against. -/
noncomputable def coinEnv : ProcEnv :=
  (ProcEnv.empty.bindProc "Top.Coin./set" (s := coinSig)
      (coinImpl.proc "set")).bindProc "Top.Coin./toss" (s := coinSig)
      (coinImpl.proc "toss")

theorem coinEnv_set : coinEnv "Top.Coin./set" coinSig = coinImpl.proc "set" := rfl

theorem coinEnv_toss : coinEnv "Top.Coin./toss" coinSig = coinImpl.proc "toss" := rfl

/-! ## The imported Hoare judgement -/

/-- The statement of `set_sets`, as the decoder produces it. -/
def setSetsForm : EcForm :=
  .hoare "Top.Coin./set" coinSig (.lit (t := .unit) ())
    (.eqT (t := .bool) (.glob bGlobal (.side .cur)) (.lit false))
    (.and (.holds (.res .bool .cur))
      (.eqT (t := .bool) (.glob bGlobal (.side .cur)) (.lit true)))

-- The decoder produces exactly that form. The two global reads are read back with
-- `isGlobReadAt` rather than matched by a pattern, for the reason `FormJson.lean`
-- gives: `EcTerm.glob` is indexed by a projection out of its own field.
#guard (match hoareStatement "set_sets" with
        | .ok (.hoare "Top.Coin./set" ⟨.unit, .bool⟩ (.lit ()) (.eqT a₁ b₁)
                 (.and (.holds (.res .bool .cur)) (.eqT a₂ b₂))) =>
          isGlobReadAt a₁ bGlobal.name bGlobal.id (.side .cur) && isBoolLit b₁ false
            && isGlobReadAt a₂ bGlobal.name bGlobal.id (.side .cur)
            && isBoolLit b₂ true
        | _ => false)

/-- The imported statement of `set_sets`, as a goal. -/
noncomputable def setSetsGoal : Prop := importedProp coinEnv setSetsForm

/-- Reading `Coin.b` at a memory, in the finite-typed vocabulary. -/
private theorem gget_bGlobal (h : Heap) : h.gget bGlobal.loc = h.get bLoc :=
  Heap.gget_ofLocation h bLoc

/-- The translated goal is the pHL judgement about the lowered procedure
`Coin.set`: from an initial memory where the global holds `false`, the procedure
returns `true` and leaves the global holding `true`. -/
theorem setSetsGoal_eq :
    setSetsGoal
      = pHoare (fun h => h.get bLoc = false) (coinImpl.proc "set" ())
          (fun r h' => r = true ∧ h'.get bLoc = true) := by
  show pHoare (fun h => h.gget bGlobal.loc = false) (coinImpl.proc "set" ())
      (fun r h' => r = true ∧ h'.gget bGlobal.loc = true) = _
  simp only [gget_bGlobal]
  rfl

/-- **The imported goal, closed.** The `hoare` lemma of the EasyCrypt source is a
theorem of CatCrypt. -/
theorem setSetsGoal_holds : setSetsGoal := by
  rw [setSetsGoal_eq, coinImpl_set]
  refine pHoare_bind (Mid := fun (_ : Unit) h => h.get bLoc = true)
    (pHoare_set (fun _ _ => Heap.get_set_same _ _ _)) (fun _ => ?_)
  exact pHoare_bind (Mid := fun v h => v = true ∧ h.get bLoc = true)
    (pHoare_get (fun _ hb => ⟨hb, hb⟩)) (fun _ => pHoare_ret (fun _ h => h))

/-! ## The imported bounded Hoare judgement

The `#guard` on `toss_lossless` in `FormJson.lean` pins every field of the decoded
statement except its bound, which `ℝ≥0∞` has no computable equality to compare.
The form below therefore carries the bound the source writes, `1%r`, as a value
this file states rather than one the decoder is checked against, and
`tossLosslessGoal_eq` reads off the CatCrypt proposition it translates to.

`tossLosslessGoal` stays a `def … : Prop`, which is what an imported statement is
(`FormToProp.lean`): the goal is stated and the proof is left to a reader. Only
`set_sets` is carried to a theorem here. -/

/-- The statement of `toss_lossless` at the bound its source writes. -/
def tossLosslessForm : EcForm :=
  .bdHoare "Top.Coin./toss" coinSig (.lit (t := .unit) ()) .tru .tru .eq 1

/-- The imported statement of `toss_lossless`, as a goal. -/
noncomputable def tossLosslessGoal : Prop := importedProp coinEnv tossLosslessForm

/-- The translated goal is losslessness of the lowered procedure `Coin.toss`
measured against the trivial event: the probability that it terminates at all is
`1`, from every initial memory. -/
theorem tossLosslessGoal_eq :
    tossLosslessGoal
      = ∀ h : Heap, True →
          prEventComp (coinImpl.proc "toss" ()) h (fun _ _ => True) = 1 :=
  rfl

end CatCrypt.Crypto.EasyCryptImport.HoareImport

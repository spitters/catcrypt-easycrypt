/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.EasyCryptImport.FormJson
import CatCrypt.Crypto.EasyCryptImport.FormToProp
import CatCrypt.Crypto.EasyCryptImport.FunctorN

/-!
# Worked example: a functor of two parameters, applied

This module takes one export — `functor2.expected.json`, the output of `ec2json`
on an EasyCrypt file declaring a functor of two parameters over two module types
— and carries the module types, the concrete module, the functor and two
statements through the whole importer: JSON, AST, translation, proof.

The source the export comes from is

```
module type Adv = { proc guess(c : bool) : bool }.
module type Src = { proc get() : bool }.

module Key = {
  var k : bool
  proc get() : bool = { var kk : bool; kk <$ {0,1}; k <- kk; return kk; }
}.

module Pair (P : Adv) (S : Src) = {
  proc main() : bool = { var x, b : bool;
    x <@ S.get(); b <@ P.guess(x); return b; }
}.

module Dup (P : Adv) (P : Adv) = {
  proc main() : bool = { var b : bool; b <@ P.guess(true); return b; }
}.

section Sec.
declare module A <: Adv.
declare module B <: Src.
lemma pair_ll :
  islossless A.guess => islossless B.get => islossless Pair(A, B).main.
lemma pair_key_ll : islossless A.guess => islossless Pair(A, Key).main.
end section Sec.
```

`Pair` binds two parameters, so the export's `params` list has two entries and
the body calls each parameter by its own cross-path — `S./get` and `P./guess`.
The functor decodes to an `EcFunctorN`, whose lowering is curried, so the
application is Lean application at two arguments.

`Dup` binds two parameters of the same source name, which EasyCrypt permits and
whose call `P./guess` names neither of them uniquely; it is here so that the
decoder's rejection of that shape is checked against an export.

## Where the module binders go

Closing the section generalises `pair_ll` over both declared modules, so the
statement arrives with `A` and `B` as nested binders. Translating a binder puts
its module into the resolution environment under that binder's cross-paths, and
the functor image the statement names — `Top.Pair(A, B)./main` — is supplied
through `FormEnv.functorImages` at the inner binder, where both modules are in
scope: it is `Pair` applied to the two modules the environment now offers under
`A` and under `B` (`ProcEnv.moduleX`). `pair_key_ll` binds only `A`, and its
image `Top.Pair(A, Top.Key)./main` is `Pair` applied to that module and to the
lowered `Key`.

Two prefixes are in play per argument, and they are different names: an argument
is read out of the environment under the *binder's* prefix — `A./guess`,
`B./get` — and bound back into it under the *parameter's* prefix, `P./guess` and
`S./get`, which is what the functor body calls. `pairBody_P` and `pairBody_S` pin
that pairing at each parameter.

## Which hypotheses carry the proofs

`main` calls each parameter once and returns; nothing else in it can lose mass.
`pairLlGoal` is closed from both `ProcLossless` hypotheses, and neither is
redundant: `pairMain_lossless` consumes `hB` for the `B.get` call and `hA` for
the `A.guess` call. `pairKeyLlGoal` carries one hypothesis, on `A`, because the
second argument is concrete and `Key.get`'s losslessness is proved here rather
than assumed.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.EasyCryptImport.Functor2Import

open Lean (Json)
open CatCrypt.Core CatCrypt.Prob CatCrypt.Relational CatCrypt.Unary CatCrypt.Crypto
open CatCrypt.Crypto.EasyCryptBridge
open scoped ENNReal

/-! ## The export -/

/-- The exporter's output for the two-parameter functor theory, as text. -/
private def functor2ExportText : String := include_str "../functor2.expected.json"

/-- The exporter's output for the two-parameter functor theory. -/
private def functor2Export : Json :=
  match Json.parse functor2ExportText with
  | .ok j => j
  | .error _ => Json.null

-- The fixture parses, it is an export of the source file it claims, and both
-- declared modules the section binds are reported as section-local rather than
-- exported.
#guard (match decodeEnvelope functor2Export with
        | .ok e => e.source == "tests/functor2.ec" && e.root == "Top"
                     && e.sectionLocal == ["A", "B"]
        | _ => false)

/-! ## The module types -/

/-- The module type `Adv`: one procedure `guess : bool -> bool`. -/
def advInterface : EcInterface where
  names := ["guess"]
  sig := fun _ => ⟨.bool, .bool⟩

/-- The module type `Src`: one procedure `get : unit -> bool`. -/
def srcInterface : EcInterface where
  names := ["get"]
  sig := fun _ => ⟨.unit, .bool⟩

-- The export's two module types declare those names at those signatures.
#guard (match importModType ecPrelude "Adv" functor2Export,
              importModType ecPrelude "Src" functor2Export with
        | .ok I, .ok J =>
          I.names == ["guess"] && I.sig "guess" == { arg := .bool, res := .bool }
            && J.names == ["get"] && J.sig "get" == { arg := .unit, res := .bool }
        | _, _ => false)

/-! ## The concrete module `Key` -/

/-- `Key`'s single global `var k : bool`, at the id `decodeModule` assigns it from
the base id 0. -/
def kGlobal : EcGlobal := { name := "Top.Key./k", id := 0, ty := .bool }

/-- The `Location` `Key.k` occupies: its code is finite, so the cell its
`EcGlobal` denotes is also a finite-typed location. -/
def kLoc : Location := kGlobal.finLoc rfl

/-- The imported concrete module `Key`: `get` samples a bit, stores it and
returns it. -/
def keyModule : EcModule where
  name := "Key"
  interface := srcInterface
  globals := [kGlobal]
  procs := fun _ =>
    { params := [anonymousLocal]
      body := [.sample .bool "kk", .store kGlobal (.var .bool "kk")]
      ret := .var .bool "kk" }

-- The export's module decodes to that interface, that global and that body.
#guard (match importModule ecPrelude "Key" functor2Export with
        | .ok M =>
          M.name == "Key" && M.interface.names == ["get"]
            && M.interface.sig "get" == { arg := .unit, res := .bool }
            && (match M.globals with
                | [{ name := "Top.Key./k", id := 0, ty := .bool }] => true
                | _ => false)
            && (match M.procs "get" with
                | { params := ["_"], body := [.sample .bool "kk", .store g e], ret := r } =>
                  g.name == "Top.Key./k" && g.id == 0 && g.ty == .bool
                    && e.varName == some "kk" && r.varName == some "kk"
                | _ => false)
        | _ => false)

/-- The lowered module: one `SPComp` procedure writing the location `Key.k`. -/
noncomputable def keyImpl : ModuleImpl srcInterface :=
  lowerModule ProcEnv.empty OpEnv.empty 0 keyModule

theorem keyImpl_get :
    keyImpl.proc "get" ()
      = SPComp.bind (SPComp.sample Bool)
          (fun k => SPComp.bind (SPComp.set kLoc k) (fun _ => SPComp.pure k)) := by
  show SPComp.bind
      (lowerStmts ProcEnv.empty [] 0
        [EcStmt.sample .bool "kk", EcStmt.store kGlobal (EcExpr.var .bool "kk")]
        ((emptyEnv OpEnv.empty).update anonymousLocal ⟨EcTy.unit, ()⟩))
      (fun env => SPComp.pure (evalExpr (EcExpr.var .bool "kk") env)) = _
  simp only [lowerStmts_sample, lowerStmts_store_finLoc (g := kGlobal) (hfin := rfl),
    lowerStmts_nil, sampleFin_bool, SPComp.bind_assoc, SPComp.pure_bind, evalExpr,
    Env.read_update_same]
  rfl

/-- `Key.get` loses no mass: it samples, writes one cell and returns. -/
theorem keyImpl_get_lossless : ProcLossless (keyImpl.proc "get") := by
  intro a
  cases a
  rw [keyImpl_get]
  refine lossless_bind (lossless_sample (α := Bool)) (fun k => ?_)
  exact lossless_bind (lossless_set kLoc k) (fun _ => lossless_pure k)

/-! ## The functor of two parameters -/

/-- The module type of `Pair`'s body: one argument-free experiment. -/
def pairInterface : EcInterface where
  names := ["main"]
  sig := fun _ => ⟨.unit, .bool⟩

/-- The body of `Pair(P, S)`: ask the source for a bit, hand it to the adversary,
and return the adversary's answer. -/
def pairModule : EcModule where
  name := "Pair"
  interface := pairInterface
  globals := []
  procs := fun _ =>
    { params := [anonymousLocal]
      body :=
        [ .callProc (xqualify "S" "get") ⟨.unit, .bool⟩ (.lit ()) "x",
          .callProc (xqualify "P" "guess") ⟨.bool, .bool⟩ (.var .bool "x") "b" ]
      ret := .var .bool "b" }

/-- The imported functor `Pair(P : Adv)(S : Src)`. -/
def pairFunctor : EcFunctorN where
  name := "Pair"
  params := [("P", advInterface), ("S", srcInterface)]
  body := pairModule

-- `Pair` decodes to that functor: two parameters in declaration order, each at
-- the interface its module type declares, and a body calling each of them by
-- that parameter's own cross-path.
#guard (match importFunctorN ecPrelude "Pair" functor2Export with
        | .ok F =>
          F.name == "Pair"
            && (match F.params with
                | [(x, I), (y, J)] =>
                  x == "P" && I.names == ["guess"]
                    && I.sig "guess" == { arg := .bool, res := .bool }
                    && y == "S" && J.names == ["get"]
                    && J.sig "get" == { arg := .unit, res := .bool }
                | _ => false)
            && F.body.interface.names == ["main"]
            && F.body.interface.sig "main" == { arg := .unit, res := .bool }
            && F.body.globals.isEmpty
            && (match F.body.procs "main" with
                | { params := ["_"],
                    body := [.callProc q₁ s₁ _ "x", .callProc q₂ s₂ a₂ "b"],
                    ret := r } =>
                  q₁ == "S./get" && s₁ == { arg := .unit, res := .bool }
                    && q₂ == "P./guess" && s₂ == { arg := .bool, res := .bool }
                    && a₂.varName == some "x" && r.varName == some "b"
                | _ => false)
        | _ => false)

-- A module of two parameters is not a module: `decodeModule` says so by name.
#guard (match importModule ecPrelude "Pair" functor2Export with
        | .error _ => true
        | .ok _ => false)

-- `Dup`, whose two parameters share the source name `P`, is rejected: the export
-- carries two `params` entries named alike, and the body's call is the bare
-- cross-path `P./guess`.
#guard (match importFunctorN ecPrelude "Dup" functor2Export with
        | .error _ => true
        | .ok _ => false)

/-! ## Functor application

Each parameter binds under its own cross-path prefix, so the two arguments are
supplied in the order the export lists the parameters and reach the body through
distinct names. -/

/-- The environment resolving `Key`'s procedures. -/
noncomputable def baseEnv : ProcEnv := ProcEnv.empty.bindModuleX "Top.Key" keyImpl

/-- The environment the two module binders of `pair_ll` produce. -/
noncomputable def pairEnv (A : ModuleImpl advInterface) (B : ModuleImpl srcInterface) :
    ProcEnv :=
  (baseEnv.bindModuleX "A" A).bindModuleX "B" B

/-- `Pair(A, B).main`, the procedure `pair_ll` names. -/
noncomputable def pairMain (A : ModuleImpl advInterface) (B : ModuleImpl srcInterface) :
    SPComp Bool :=
  (lowerFunctorNX (pairEnv A B) OpEnv.empty 0 pairFunctor ((pairEnv A B).moduleX "A" advInterface)
      ((pairEnv A B).moduleX "B" srcInterface)).proc "main" ()

/-- The environment the single module binder of `pair_key_ll` produces. -/
noncomputable def keyEnv (A : ModuleImpl advInterface) : ProcEnv :=
  baseEnv.bindModuleX "A" A

/-- `Pair(A, Key).main`, the procedure `pair_key_ll` names. -/
noncomputable def pairKeyMain (A : ModuleImpl advInterface) : SPComp Bool :=
  (lowerFunctorNX (keyEnv A) OpEnv.empty 0 pairFunctor ((keyEnv A).moduleX "A" advInterface)
      keyImpl).proc "main" ()

/-! ## Call resolution

Both parameters are bound in one environment, each under its own prefix, so a
call to one resolves past the other. -/

theorem pairEnv_A (A : ModuleImpl advInterface) (B : ModuleImpl srcInterface) :
    ((pairEnv A B).moduleX "A" advInterface).proc "guess" = A.proc "guess" := rfl

theorem pairEnv_B (A : ModuleImpl advInterface) (B : ModuleImpl srcInterface) :
    ((pairEnv A B).moduleX "B" srcInterface).proc "get" = B.proc "get" := rfl

/-- The environment the body of `Pair(A, B)` is lowered against resolves `P./guess`
to the first argument. -/
theorem pairBody_P (A : ModuleImpl advInterface) (B : ModuleImpl srcInterface) :
    (((pairEnv A B).bindModuleX "P" ((pairEnv A B).moduleX "A" advInterface)).bindModuleX
        "S" ((pairEnv A B).moduleX "B" srcInterface))
      (xqualify "P" "guess") ⟨.bool, .bool⟩ = A.proc "guess" := rfl

/-- The same environment resolves `S./get` to the second argument. -/
theorem pairBody_S (A : ModuleImpl advInterface) (B : ModuleImpl srcInterface) :
    (((pairEnv A B).bindModuleX "P" ((pairEnv A B).moduleX "A" advInterface)).bindModuleX
        "S" ((pairEnv A B).moduleX "B" srcInterface))
      (xqualify "S" "get") ⟨.unit, .bool⟩ = B.proc "get" := rfl

/-- With the second argument concrete, `S./get` resolves to `Key`'s procedure. -/
theorem pairKeyBody_S (A : ModuleImpl advInterface) :
    (((keyEnv A).bindModuleX "P" ((keyEnv A).moduleX "A" advInterface)).bindModuleX
        "S" keyImpl)
      (xqualify "S" "get") ⟨.unit, .bool⟩ = keyImpl.proc "get" := rfl

/-! ## The application in closed form -/

/-- `Pair(A, B).main` asks `B` for a bit and hands it to `A`. -/
theorem pairMain_eq (A : ModuleImpl advInterface) (B : ModuleImpl srcInterface) :
    pairMain A B
      = SPComp.bind (B.proc "get" ())
          (fun x => SPComp.bind (A.proc "guess" x) (fun b => SPComp.pure b)) := by
  show SPComp.bind
      (lowerStmts
        (((pairEnv A B).bindModuleX "P" ((pairEnv A B).moduleX "A" advInterface)).bindModuleX
          "S" ((pairEnv A B).moduleX "B" srcInterface)) [] 0
        [ EcStmt.callProc (xqualify "S" "get") ⟨.unit, .bool⟩
            (EcExpr.lit (t := .unit) ()) "x",
          EcStmt.callProc (xqualify "P" "guess") ⟨.bool, .bool⟩
            (EcExpr.var .bool "x") "b" ]
        ((emptyEnv OpEnv.empty).update anonymousLocal ⟨EcTy.unit, ()⟩))
      (fun env => SPComp.pure (evalExpr (EcExpr.var .bool "b") env)) = _
  simp only [lowerStmts_callProc, lowerStmts_nil, pairBody_P, pairBody_S, evalExpr,
    EcTy.interp, SPComp.bind_assoc, SPComp.pure_bind, Env.read_update_same]
  rfl

/-- `Pair(A, Key).main` samples the key, stores it, and hands it to `A`. -/
theorem pairKeyMain_eq (A : ModuleImpl advInterface) :
    pairKeyMain A
      = SPComp.bind (SPComp.sample Bool) (fun k =>
          SPComp.bind (SPComp.set kLoc k) (fun _ =>
            SPComp.bind (A.proc "guess" k) (fun b => SPComp.pure b))) := by
  show SPComp.bind
      (lowerStmts
        (((keyEnv A).bindModuleX "P" ((keyEnv A).moduleX "A" advInterface)).bindModuleX
          "S" keyImpl) [] 0
        [ EcStmt.callProc (xqualify "S" "get") ⟨.unit, .bool⟩
            (EcExpr.lit (t := .unit) ()) "x",
          EcStmt.callProc (xqualify "P" "guess") ⟨.bool, .bool⟩
            (EcExpr.var .bool "x") "b" ]
        ((emptyEnv OpEnv.empty).update anonymousLocal ⟨EcTy.unit, ()⟩))
      (fun env => SPComp.pure (evalExpr (EcExpr.var .bool "b") env)) = _
  simp only [lowerStmts_callProc, lowerStmts_nil, pairKeyBody_S, keyImpl_get, evalExpr,
    EcTy.interp, SPComp.bind_assoc, SPComp.pure_bind, Env.read_update_same]
  rfl

/-! ## What each hypothesis gives -/

/-- The application terminates whenever both arguments do. Each hypothesis
discharges the call to its own argument. -/
theorem pairMain_lossless (A : ModuleImpl advInterface) (B : ModuleImpl srcInterface)
    (hA : ProcLossless (A.proc "guess")) (hB : ProcLossless (B.proc "get")) :
    isLossless (pairMain A B) := by
  rw [pairMain_eq]
  refine lossless_bind (hB ()) (fun x => ?_)
  exact lossless_bind (hA x) (fun b => lossless_pure b)

/-- With the second argument concrete, the hypothesis on the first argument is
what remains: `Key.get` is proved lossless above. -/
theorem pairKeyMain_lossless (A : ModuleImpl advInterface)
    (hA : ProcLossless (A.proc "guess")) : isLossless (pairKeyMain A) := by
  rw [pairKeyMain_eq]
  refine lossless_bind (lossless_sample (α := Bool)) (fun k => ?_)
  refine lossless_bind (lossless_set kLoc k) (fun _ => ?_)
  exact lossless_bind (hA k) (fun b => lossless_pure b)

/-! ## The statement tables

The signature of `Key`'s procedure comes from the export; the two functor images
the statements name are supplied here, at the signature `Pair`'s body declares. -/

/-- The path `pair_ll` names the two-argument image by. -/
def pairPath : String := "Top.Pair(A, B)./main"

/-- The path `pair_key_ll` names the mixed image by. -/
def pairKeyPath : String := "Top.Pair(A, Top.Key)./main"

/-- The tables the statements of the export decode against. -/
def functor2Tables : Except String FormTables := do
  let e ← decodeEnvelope functor2Export
  let it ← findItem e "Key"
  let S ← decodeStructure ecPrelude 0 it
  .ok (formTables (S.globals.foldl DecodeTables.withGlobal ecPrelude)
        (procSigsOfStructure S ++ [(pairPath, mainSig), (pairKeyPath, mainSig)])
        [("Top.Adv", advInterface), ("Top.Src", srcInterface)]
        [("Top.Key", S.globals)])

/-- Decode the statement of the lemma `name` from the export. -/
def importedStatement (name : String) : Except String EcForm := do
  let F ← functor2Tables
  importAxiom F name functor2Export

/-! ## The imported statements -/

/-- The statement of `pair_ll`, as the decoder produces it. -/
def pairLlForm : EcForm :=
  .allMod "A" advInterface
    (.allMod "B" srcInterface
      (.imp (.lossless (xqualify "A" "guess") ⟨.bool, .bool⟩)
        (.imp (.lossless (xqualify "B" "get") ⟨.unit, .bool⟩)
          (.bdHoare pairPath mainSig (.lit (t := .unit) ()) .tru .tru EcCmp.eq (EcRealLit.mk 1 1)))))

/-- The statement of `pair_key_ll`, as the decoder produces it. -/
def pairKeyLlForm : EcForm :=
  .allMod "A" advInterface
    (.imp (.lossless (xqualify "A" "guess") ⟨.bool, .bool⟩)
      (.bdHoare pairKeyPath mainSig (.lit (t := .unit) ()) .tru .tru EcCmp.eq (EcRealLit.mk 1 1)))

-- The decoder produces those forms: two nested unrestricted module binders,
-- `islossless` over each abstract module's procedure as the dedicated node, and
-- `islossless` over the functor image as the bounded Hoare judgement at the
-- trivial event and the bound `1`.
#guard (match importedStatement "pair_ll" with
        | .ok (.allMod "A" I
                (.allMod "B" J
                  (.imp (.lossless "A./guess" ⟨.bool, .bool⟩)
                    (.imp (.lossless "B./get" ⟨.unit, .bool⟩)
                      (.bdHoare "Top.Pair(A, B)./main" ⟨.unit, .bool⟩ (.lit ())
                        .tru .tru EcCmp.eq (EcRealLit.mk 1 1)))))) =>
          I.names == ["guess"] && I.sig "guess" == { arg := .bool, res := .bool }
            && J.names == ["get"] && J.sig "get" == { arg := .unit, res := .bool }
        | _ => false)

#guard (match importedStatement "pair_key_ll" with
        | .ok (.allMod "A" I
                (.imp (.lossless "A./guess" ⟨.bool, .bool⟩)
                  (.bdHoare "Top.Pair(A, Top.Key)./main" ⟨.unit, .bool⟩ (.lit ())
                    .tru .tru EcCmp.eq (EcRealLit.mk 1 1)))) =>
          I.names == ["guess"] && I.sig "guess" == { arg := .bool, res := .bool }
        | _ => false)

/-- The image `pair_ll` names, as an extension of the resolution environment. It
is bound at the inner binder `B`, where both modules are in scope: instantiating
both binders binds `Pair(A, B).main` to the functor applied to the two modules the
environment now offers under `A` and under `B`. -/
noncomputable def pairImages : String → ProcEnv → ProcEnv := fun name ρ =>
  if name = "B" then
    ρ.bindProc pairPath (s := mainSig)
      (fun _ =>
        (lowerFunctorNX ρ OpEnv.empty 0 pairFunctor (ρ.moduleX "A" advInterface)
            (ρ.moduleX "B" srcInterface)).proc "main" ())
  else ρ

/-- The image `pair_key_ll` names: the functor applied to the module the binder
`A` brings into the environment and to the lowered `Key`. -/
noncomputable def pairKeyImages : String → ProcEnv → ProcEnv := fun name ρ =>
  if name = "A" then
    ρ.bindProc pairKeyPath (s := mainSig)
      (fun _ =>
        (lowerFunctorNX ρ OpEnv.empty 0 pairFunctor (ρ.moduleX "A" advInterface) keyImpl).proc "main" ())
  else ρ

/-- The imported statement of `pair_ll`, as a goal. -/
noncomputable def pairLlGoal : Prop :=
  importedPropWith baseEnv pairImages pairLlForm

/-- The imported statement of `pair_key_ll`, as a goal. -/
noncomputable def pairKeyLlGoal : Prop :=
  importedPropWith baseEnv pairKeyImages pairKeyLlForm

/-- The translated goal: for every two abstract modules whose procedures are
lossless, `Pair(A, B).main` terminates with probability one from every initial
memory. -/
theorem pairLlGoal_eq :
    pairLlGoal
      = ∀ (A : ModuleImpl advInterface) (B : ModuleImpl srcInterface),
          ProcLossless (A.proc "guess") → ProcLossless (B.proc "get") →
          ∀ h : Heap, True → prEventComp (pairMain A B) h (fun _ _ => True) = (1 : ℕ) :=
  rfl

/-- The translated goal for the mixed application, whose second argument is the
lowered `Key`. -/
theorem pairKeyLlGoal_eq :
    pairKeyLlGoal
      = ∀ A : ModuleImpl advInterface, ProcLossless (A.proc "guess") →
          ∀ h : Heap, True → prEventComp (pairKeyMain A) h (fun _ _ => True) = (1 : ℕ) :=
  rfl

/-- **The imported statement of `pair_ll`, closed.** -/
theorem pairLlGoal_holds : pairLlGoal := by
  rw [pairLlGoal_eq]
  intro A B hA hB h _
  rw [Nat.cast_one, prEventComp_true]
  exact pairMain_lossless A B hA hB h

/-- **The imported statement of `pair_key_ll`, closed.** -/
theorem pairKeyLlGoal_holds : pairKeyLlGoal := by
  rw [pairKeyLlGoal_eq]
  intro A hA h _
  rw [Nat.cast_one, prEventComp_true]
  exact pairKeyMain_lossless A hA h

end CatCrypt.Crypto.EasyCryptImport.Functor2Import

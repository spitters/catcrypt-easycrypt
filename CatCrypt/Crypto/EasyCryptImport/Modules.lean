/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.EasyCryptImport.Ast
import CatCryptCore.Core.Code

/-!
# EasyCrypt import: the semantic module layer

This module defines what an imported EasyCrypt module *is* on the CatCrypt side,
and how a procedure call is resolved.

## Modules

`ModuleImpl I` is a record of `SPComp` procedures, one per procedure name of the
interface `I`, each at the signature `I` declares. This is the image of an
EasyCrypt concrete module: the procedures share the heap, so the module's `var`
declarations are heap cells (`EcGlobal.loc`) that the procedure bodies read and
write. Encapsulation is a convention on location ids, not a typing guarantee:
nothing in `ModuleImpl` prevents one module's procedure from touching another
module's locations. EasyCrypt enforces that with `{-M}` restrictions; here it is
an emitted side hypothesis (`Restrictions.lean`).

## Abstract modules

An abstract EasyCrypt module — an adversary or an oracle given only by its
interface — is a `ModuleImpl I` **parameter**. An imported game that quantifies
over all adversaries of interface `I` is therefore a Lean statement of the shape
`∀ (A : ModuleImpl I), …`.

## Functors

A functor `F(X : I)` is a Lean function `ModuleImpl I → ModuleImpl J`
(`Lower.lowerFunctor`). Functor application is function application, and
composing functors is function composition. A functor of several parameters is a
curried function of one `ModuleImpl` per parameter, each bound under its own
prefix (`FunctorN.lean`).

## Call resolution

`ProcEnv` maps a qualified procedure name and a signature to a procedure. The
lowering of `x <@ q(a)` looks `q` up in the ambient `ProcEnv` at the signature
recorded in the call statement, so the same statement resolves against a
concrete module or against an adversary parameter depending on what is bound.
`ProcEnv.bindModule` binds every declared procedure `p` of a module under the
qualified name `qualify pfx p`, which is exactly EasyCrypt's oracle
substitution: resolving `X.o` by `X`'s implementation. `ProcEnv.bindModuleX`
binds the same procedures under `xqualify pfx p`, the cross-path the exporter
writes, which is the name an imported statement calls them by.

A name that is not bound, or a binding whose signature differs from the one at
the call site, falls through to the rest of the environment; `ProcEnv.empty`
answers every query with the procedure that returns the default value. A
well-formed import binds every qualified name its game mentions.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.EasyCryptImport

open CatCrypt.Core

/-- An imported module: an `SPComp` procedure for each name of the interface, at
the signature the interface declares. -/
structure ModuleImpl (I : EcInterface) where
  /-- The procedure registered under each name. -/
  proc : (p : String) → (I.sig p).arg.interp → SPComp (I.sig p).res.interp

/-- Transport a procedure along an equality of signatures. -/
def castProc {s s' : EcSig} (h : s = s')
    (f : s.arg.interp → SPComp s.res.interp) : s'.arg.interp → SPComp s'.res.interp :=
  h ▸ f

@[simp] theorem castProc_rfl {s : EcSig} (f : s.arg.interp → SPComp s.res.interp) :
    castProc rfl f = f := rfl

/-- The resolution environment for qualified procedure calls: a procedure for
each qualified name and signature. -/
def ProcEnv : Type := (q : String) → (s : EcSig) → s.arg.interp → SPComp s.res.interp

namespace ProcEnv

/-- The environment binding no name: every query returns the default value
without touching the heap. -/
noncomputable def empty : ProcEnv := fun _ _ _ => SPComp.pure default

/-- Bind the qualified name `q` at signature `s` to the procedure `f`; queries
at any other name or signature fall through to `ρ`. -/
noncomputable def bindProc (ρ : ProcEnv) (q : String) {s : EcSig}
    (f : s.arg.interp → SPComp s.res.interp) : ProcEnv :=
  fun q' s' => if _ : q' = q then (if h : s = s' then castProc h f else ρ q' s') else ρ q' s'

theorem bindProc_same (ρ : ProcEnv) (q : String) {s : EcSig}
    (f : s.arg.interp → SPComp s.res.interp) : ρ.bindProc q f q s = f := by
  simp [bindProc]

theorem bindProc_ne (ρ : ProcEnv) (q q' : String) {s : EcSig}
    (f : s.arg.interp → SPComp s.res.interp) (s' : EcSig) (h : q' ≠ q) :
    ρ.bindProc q f q' s' = ρ q' s' := dif_neg h

/-- Bind the procedures named in `ps` of the module `M` under their qualified
names. -/
noncomputable def bindProcs (ρ : ProcEnv) (pfx : String) {I : EcInterface}
    (M : ModuleImpl I) : List String → ProcEnv
  | [] => ρ
  | p :: ps => (bindProcs ρ pfx M ps).bindProc (qualify pfx p) (M.proc p)

@[simp] theorem bindProcs_nil (ρ : ProcEnv) (pfx : String) {I : EcInterface}
    (M : ModuleImpl I) : ρ.bindProcs pfx M [] = ρ := rfl

@[simp] theorem bindProcs_cons (ρ : ProcEnv) (pfx : String) {I : EcInterface}
    (M : ModuleImpl I) (p : String) (ps : List String) :
    ρ.bindProcs pfx M (p :: ps)
      = (ρ.bindProcs pfx M ps).bindProc (qualify pfx p) (M.proc p) := rfl

/-- Bind every declared procedure `p` of the module `M` under the qualified name
`qualify pfx p`. This is oracle substitution: a call site `pfx.p` resolves to
`M`'s implementation of `p`. -/
noncomputable def bindModule (ρ : ProcEnv) (pfx : String) {I : EcInterface}
    (M : ModuleImpl I) : ProcEnv :=
  ρ.bindProcs pfx M I.names

theorem bindModule_eq (ρ : ProcEnv) (pfx : String) {I : EcInterface}
    (M : ModuleImpl I) : ρ.bindModule pfx M = ρ.bindProcs pfx M I.names := rfl

/-- Bind the procedures named in `ps` of the module `M` under the cross-paths the
exporter writes. -/
noncomputable def bindProcsX (ρ : ProcEnv) (pfx : String) {I : EcInterface}
    (M : ModuleImpl I) : List String → ProcEnv
  | [] => ρ
  | p :: ps => (bindProcsX ρ pfx M ps).bindProc (xqualify pfx p) (M.proc p)

@[simp] theorem bindProcsX_nil (ρ : ProcEnv) (pfx : String) {I : EcInterface}
    (M : ModuleImpl I) : ρ.bindProcsX pfx M [] = ρ := rfl

@[simp] theorem bindProcsX_cons (ρ : ProcEnv) (pfx : String) {I : EcInterface}
    (M : ModuleImpl I) (p : String) (ps : List String) :
    ρ.bindProcsX pfx M (p :: ps)
      = (ρ.bindProcsX pfx M ps).bindProc (xqualify pfx p) (M.proc p) := rfl

/-- Bind every declared procedure `p` of the module `M` under the cross-path
`xqualify pfx p`, the name the exporter writes at a call site and at a
judgement. This is the binding an imported statement resolves against, where
`qualify` is the binding a hand-written game resolves against. -/
noncomputable def bindModuleX (ρ : ProcEnv) (pfx : String) {I : EcInterface}
    (M : ModuleImpl I) : ProcEnv :=
  ρ.bindProcsX pfx M I.names

theorem bindModuleX_eq (ρ : ProcEnv) (pfx : String) {I : EcInterface}
    (M : ModuleImpl I) : ρ.bindModuleX pfx M = ρ.bindProcsX pfx M I.names := rfl

/-- The module an environment offers under the cross-paths of `pfx` at the
interface `I`: the procedure registered under `xqualify pfx p` for each name `p`
of `I`. This is what a functor is applied to when its argument is available only
through the environment — an imported statement binds its module quantifier into
the environment, and a functor image the statement names is the functor applied
to the module read back out. -/
def moduleX (ρ : ProcEnv) (pfx : String) (I : EcInterface) : ModuleImpl I where
  proc := fun p => ρ (xqualify pfx p) (I.sig p)

@[simp] theorem moduleX_proc (ρ : ProcEnv) (pfx : String) (I : EcInterface)
    (p : String) : (ρ.moduleX pfx I).proc p = ρ (xqualify pfx p) (I.sig p) := rfl

end ProcEnv

end CatCrypt.Crypto.EasyCryptImport

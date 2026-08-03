/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.EasyCryptImport.Ast

/-!
# EasyCrypt import: the abstract-operator parameter layer

An EasyCrypt theory declares operators without definitions (`op dK : K distr.`).
This module defines what such a declaration *is* on the CatCrypt side: a value
parameter of the imported statement, resolved through an environment keyed by the
operator's path and its signature.

## `OpEnv` is `ProcEnv` without the monad

`ProcEnv` (`Modules.lean`) resolves a procedure call to an `SPComp`. An operator
is pure, so `OpEnv` resolves an operator path to a function on the
interpretations of its signature:

```lean
def OpEnv : Type := (path : String) → (s : EcSig) → s.arg.interp → s.res.interp
```

Everything an operator declaration needs rides on `EcSig`:

* a nullary operator has `s.arg = EcTy.unit` and is applied at `.lit ()`;
* an operator of `n` arguments has `s.arg` the arguments' codes as a
  right-nested product, the convention `EcProcAt.params` and `bindParams` fix
  for a procedure's formals;
* a predicate has `s.res = EcTy.bool`;
* a distribution-valued operator has `s.res = EcTy.distr t`, whose
  interpretation is an `SDistr`, so an abstract distribution is an operator and
  reaches sampling through `EcDistr.ofExpr`.

An operator's own arrow type is absorbed into `EcSig` rather than read as an
`EcTy.arrow`: the declaration's outermost arrows are its arguments, and the
argument codes nest into `s.arg`. An argument that is itself a function type is
at `EcTy.arrow` (`Ty.lean`), so `OpEnv` resolves a higher-order operator to a
function taking a function.

## Totality, and what the statement's own binders are for

`OpEnv` is total: a path it does not bind answers with the canonical inhabitant
of the result code, the same shape `ProcEnv.empty` has for a procedure. That
answer is not the operator's meaning, so a statement translated against
`OpEnv.empty` at a path it mentions says nothing about the source operator. What
keeps a statement away from that answer is `EcForm.allOp`: the statement
quantifies over the realization of every operator it mentions, and
`EcForm.opsOf` of an assembled statement is empty (`Form.lean`), so no path of
the statement reaches the environment it is translated in.

## Main definitions

* `OpEnv`: a realization of the abstract operators, mapping a path and an
  `EcSig` to a function on that signature's interpretation.
* `OpEnv.empty`: the total environment answering every path with the result
  code's canonical inhabitant, which is not the operator's meaning.
* `OpEnv.bindOp`, `OpEnv.bindConst`: extend a realization at one path, the
  latter at a nullary signature.

## Main results

* `OpEnv.bindOp_same`, `OpEnv.bindOp_ne`, `OpEnv.bindConst_same`: reading a
  bound path returns what was bound, and binding one path leaves the others.
* `OpEnv.castOp_rfl`: the signature cast at a reflexivity proof is the
  identity, which is what makes the lookup lemmas fire.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.EasyCryptImport

/-- The realization of the abstract operators: a pure function per operator
path, at the signature the operator's declaration gives it. -/
def OpEnv : Type := (path : String) → (s : EcSig) → s.arg.interp → s.res.interp

namespace OpEnv

/-- Transport an operator realization along an equality of signatures. -/
def castOp {s s' : EcSig} (h : s = s')
    (f : s.arg.interp → s.res.interp) : s'.arg.interp → s'.res.interp :=
  h ▸ f

@[simp] theorem castOp_rfl {s : EcSig} (f : s.arg.interp → s.res.interp) :
    castOp rfl f = f := rfl

/-- The realization binding no path: every query answers with the canonical
inhabitant of the result code. -/
def empty : OpEnv := fun _ s _ => s.res.defaultOf

/-- Bind the operator path `path` at signature `s` to `f`; a query at any other
path or signature falls through to `ρ`. -/
def bindOp (ρ : OpEnv) (path : String) {s : EcSig}
    (f : s.arg.interp → s.res.interp) : OpEnv :=
  fun p' s' =>
    if _ : p' = path then (if h : s = s' then castOp h f else ρ p' s') else ρ p' s'

theorem bindOp_same (ρ : OpEnv) (path : String) {s : EcSig}
    (f : s.arg.interp → s.res.interp) : ρ.bindOp path f path s = f := by
  simp [bindOp]

theorem bindOp_ne (ρ : OpEnv) (path p' : String) {s : EcSig}
    (f : s.arg.interp → s.res.interp) (s' : EcSig) (h : p' ≠ path) :
    ρ.bindOp path f p' s' = ρ p' s' := dif_neg h

/-- Bind a nullary operator path to the value `v` of code `t`: the realization
at the signature `⟨unit, t⟩` that ignores its argument. This is the shape of an
EasyCrypt constant declaration `op c : t.`, the abstract distribution `op d : t
distr.` among them. -/
def bindConst (ρ : OpEnv) (path : String) (t : EcTy) (v : t.interp) : OpEnv :=
  ρ.bindOp path (s := ⟨.unit, t⟩) (fun _ => v)

theorem bindConst_same (ρ : OpEnv) (path : String) (t : EcTy) (v : t.interp)
    (a : Unit) : ρ.bindConst path t v path ⟨.unit, t⟩ a = v := by
  rw [bindConst, bindOp_same]

end OpEnv

end CatCrypt.Crypto.EasyCryptImport

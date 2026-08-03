/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.EasyCryptImport.FormToProp
import CatCrypt.Crypto.EasyCryptImport.FormJson

/-!
# An imported statement polymorphic in two type parameters

EasyCrypt's `theories/core/Core.ec` states

```
lemma pairS ['a 'b] : forall (x : 'a * 'b), x = (x.`1, x.`2).
```

`'a` and `'b` are type parameters of the statement, and the exporter writes them
as `tparams` on the item and as `Tvar` nodes in the type of the bound variable, of
both projections and of the applied equality. This module exhibits what the item
becomes here: a family of `EcForm` values indexed by the two type codes, and a
proposition quantifying over the codes.

## The two readings

* `pairSurjAtOpaque` is the statement at the opaque code of each parameter's
  reserved path, which is what `decodeAxiom` produces when no assignment is
  given. `Ty.lean` fixes the carrier of an opaque code at `Carrier` on its path,
  so this reading is
  `∀ v : Carrier "#tyvar.'a" × Carrier "#tyvar.'b", v = (v.1, v.2)`
  (`pairSurjAtOpaque_iff`): the source
  statement at one abstract type per parameter, a consequence of the source's and
  not the whole of it.
* `pairSurjProp` is the statement closed over its parameters, which is
  `∀ (a b : EcTy) (v : (EcTy.prod a b).interp), v = (v.1, v.2)`
  (`pairSurjProp_iff`). The binders range over the type codes the ingestion
  knows, and so over the Lean types in the image of `EcTy.interp` rather than over
  every Lean type; `Form.lean` records that weakening and its alternative.

`pairS` carries no premise, so there is no imported hypothesis set to exhibit a
realization of. `pairSurjProp_holds` closes the imported goal, which is the
strongest available statement that it is not vacuous: the proposition the importer
produces is surjective pairing, and it is provable exactly where the source lemma
is.

## Main definitions

* `pairSurj`: the decoded `pairS` statement as a family in its two type codes.
* `pairSurjProp`: its reading closed over the codes.
* `pairSurjAtOpaque`: its reading at the opaque code of each parameter.

## Main results

* `pairSurjProp_iff`, `pairSurjAtOpaque_iff`: each reading is the expected
  statement about pairs.
* `pairSurjProp_holds`: the imported goal holds.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.EasyCryptImport.Examples.CorePairSurjImport

open CatCrypt.Core
open CatCrypt.Crypto.EasyCryptImport

/-! ## The imported statement -/

/-- The tables `pairS` decodes against: the prelude alone, since the statement
names no module and no declared operator. -/
def coreTables : FormTables := formTables ecPrelude []

/-- The statement as a family in the codes its two type parameters are read at:
the bound variable equated with the pair of its two projections. -/
def pairSurj : EcPolyForm 2 := fun a b =>
  .allTy (.prod a b) "x"
    (.eqT (.var (.prod a b) "x")
      (.pair (.fst (.var (.prod a b) "x")) (.snd (.var (.prod a b) "x"))))

-- The decoder produces that family: at the opaque code of each parameter's
-- reserved path when no assignment is given, and at the assigned codes
-- otherwise.
#guard (match decodeAxiom coreTables jPairSItem with
        | .ok (.allTy (.prod (.opaque "#tyvar.'a") (.opaque "#tyvar.'b")) "x"
                 (.eqT (.var _ "x")
                   (.pair (.fst (.var _ "x")) (.snd (.var _ "x"))))) => true
        | _ => false)

#guard (match decodeAxiomAt coreTables [.bool, .int] jPairSItem with
        | .ok (.allTy (.prod .bool .int) "x"
                 (.eqT (.var _ "x")
                   (.pair (.fst (.var _ "x")) (.snd (.var _ "x"))))) => true
        | _ => false)

-- The statement reads no abstract operator, so assembling it binds nothing and
-- leaves nothing free.
#guard EcForm.opsOf (EcPolyForm.assembleParams pairSurj .bool .int) == []

/-! ## The two propositions -/

/-- The imported statement closed over the codes its type parameters are read
at. -/
noncomputable def pairSurjProp : Prop :=
  importedPropPoly ProcEnv.empty pairSurj

/-- The imported statement at the opaque code of each parameter's reserved
path. -/
noncomputable def pairSurjAtOpaque : Prop :=
  importedProp ProcEnv.empty (pairSurj (.opaque "#tyvar.'a") (.opaque "#tyvar.'b"))

/-! ## What the two propositions are -/

/-- The closed reading quantifies over the two type codes and over the pairs at
them. -/
theorem pairSurjProp_iff :
    pairSurjProp ↔ ∀ (a b : EcTy) (v : (EcTy.prod a b).interp), v = (v.1, v.2) := by
  simp only [pairSurjProp, importedPropPoly_succ, importedPropPoly_zero, importedProp,
    pairSurj, transForm_allTy, transForm_eqT, evalTerm_var, evalTerm_pair,
    evalTerm_fst, evalTerm_snd, FormEnv.bindVar, Env.read_update_same]

/-- The reading at the opaque codes is the statement at the carrier `Ty.lean`
fixes for an abstract type. -/
theorem pairSurjAtOpaque_iff :
    pairSurjAtOpaque
      ↔ ∀ v : Carrier "#tyvar.'a" × Carrier "#tyvar.'b", v = (v.1, v.2) := by
  simp only [pairSurjAtOpaque, importedProp, pairSurj, transForm_allTy,
    transForm_eqT, evalTerm_var, evalTerm_pair, evalTerm_fst, evalTerm_snd,
    FormEnv.bindVar, Env.read_update_same]

/-- The imported goal holds: a pair is the pair of its components. -/
theorem pairSurjProp_holds : pairSurjProp := by
  rw [pairSurjProp_iff]
  intro _ _ _
  rfl

end CatCrypt.Crypto.EasyCryptImport.Examples.CorePairSurjImport

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.EasyCryptImport.Modules
import CatCryptCore.Relational.Frame
import CatCryptCore.Relational.Rules
import CatCryptCore.Unary.Event
import CatCryptCore.Unary.Lossless

/-!
# EasyCrypt import: module restrictions as side hypotheses

EasyCrypt's module system carries three annotations that CatCrypt has no
type-level home for: the memory restriction `A{-M}`, the losslessness assertion
`islossless A.f`, and complexity budgets. The importer does not drop them and
does not encode them in `ModuleImpl`; it emits them as **explicit hypotheses on
the generated statement**. This module defines the predicates those hypotheses
are stated with, and proves the lemmas that make them usable and satisfiable.

## `A{-M}` — memory restriction

`agreeOff locs`, from the core relational vocabulary, relates two heaps that
coincide outside the location ids `locs`. `RespectsLocs locs f` says the procedure `f` cannot observe or create a
difference inside `locs`: run from two heaps agreeing outside `locs`, it returns
equal values and leaves heaps that still agree outside `locs`. This is the
`rHoare`-shaped image of EasyCrypt's `A{-M}` with `locs` the footprint
`globLocs M.globals` of `M`'s globals. `ModuleRespectsLocs` is the whole-module
form.

The predicate is satisfiable, not a disguised falsehood: `respectsLocs_of_isPure`
shows every heap-independent procedure respects every `locs`, and
`RespectsLocs.bind` shows the predicate is closed under sequencing, so a functor
built over a restricted adversary is again restricted.

## `glob A` — the footprint a module lives on

`agreeOn locs` relates two heaps that coincide *on* the location ids `locs`, the
complementary relation to `agreeOff`. `RespectsOn locs f` says the procedure `f`
sees and changes nothing outside `locs`: run from two heaps agreeing on `locs`,
it returns equal values and leaves heaps that still agree on `locs`. This is the
`rHoare`-shaped image of "the module's global state is `locs`", which is what
EasyCrypt's `glob A` names for an abstract module, and `agreeOn locs` is the
image of the precondition `={glob A}`.

## `islossless` — termination

`ProcLossless f` is `isLossless (f x)` for every argument, the CatCrypt reading
of EasyCrypt's `islossless`: the procedure's output sub-distribution has total
mass one, i.e. it never fails. `ModuleLossless` is the whole-module form.

## Complexity

EasyCrypt's cost and query-count restrictions have no representation here and
are not emitted: there is no `SPComp`-level notion of a query counter or a
running time to state them against. An imported concrete-security statement that
depends on `q_H` or on a running time loses that dependence; this is a gap, not
a hypothesis that could be supplied.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.EasyCryptImport

open CatCrypt.Core CatCrypt.Prob CatCrypt.Relational CatCrypt.Unary

/-! ## Heaps agreeing on a footprint -/

/-- Two heaps agree on the location ids `locs`. This is the relational
precondition an imported `={glob M}` is stated against, with `locs` the footprint
of `M`'s globals. -/
def agreeOn (locs : LocSet) : RPre :=
  fun h₁ h₂ => ∀ id ∈ locs, h₁.data.lookup id = h₂.data.lookup id

theorem agreeOn_refl (locs : LocSet) (h : Heap) : agreeOn locs h h := fun _ _ => rfl

/-- Heap equality implies agreement on every footprint: whole-memory equality is
at least as strong as a footprint comparison. -/
theorem agreeOn_of_eq {locs : LocSet} {h₁ h₂ : Heap} (h : h₁ = h₂) : agreeOn locs h₁ h₂ :=
  h ▸ agreeOn_refl locs h₁

/-- Agreement outside `locs` implies agreement on any footprint disjoint from
`locs`. -/
theorem agreeOn_of_agreeOff {locs fp : LocSet} (hd : Disjoint fp locs) {h₁ h₂ : Heap}
    (h : agreeOff locs h₁ h₂) : agreeOn fp h₁ h₂ :=
  fun id hid => h id (Finset.disjoint_left.mp hd hid)

/-- Writing to a location outside a footprint preserves agreement on it, with
possibly different values on the two sides. -/
theorem agreeOn_set_of_not_mem (locs : LocSet) (l : Location) (hl : l.id ∉ locs)
    {h₁ h₂ : Heap} (h : agreeOn locs h₁ h₂) (v₁ v₂ : l.ty) :
    agreeOn locs (h₁.set l v₁) (h₂.set l v₂) := by
  intro id hid
  have hne : id ≠ l.id := fun he => hl (he ▸ hid)
  simpa only [Heap.set, Finmap.lookup_insert_of_ne _ hne] using h id hid

/-! ## Synchronised heap writes -/

/-- Two synchronised writes to the same location, with possibly different
values: it suffices that the precondition survives both writes. This is the
relational rule an imported `M.g <- e` pair reduces to. -/
theorem rHoare_set_step {α β : Type*} {Φ Φ' : RPre} {Ψ : RPost α β}
    (l : Location) (v₁ v₂ : l.ty) {c₁ : SPComp α} {c₂ : SPComp β}
    (hΦ : ∀ h₁ h₂, Φ h₁ h₂ → Φ' (h₁.set l v₁) (h₂.set l v₂))
    (h : rHoare Φ' c₁ c₂ Ψ) :
    rHoare Φ (SPComp.bind (SPComp.set l v₁) (fun _ => c₁))
             (SPComp.bind (SPComp.set l v₂) (fun _ => c₂)) Ψ := by
  intro h₁ h₂ hpre
  simpa only [SPComp.bind, SPComp.set, SDistr.pure_bind] using h _ _ (hΦ h₁ h₂ hpre)

/-- A read of a location immediately after a write to it returns the written
value. This contracts the `store` / `load` pair an imported module produces when
one procedure writes a global that the next procedure reads. -/
theorem bind_set_get {α : Type} (l : Location) (v : l.ty) (f : l.ty → SPComp α) :
    SPComp.bind (SPComp.set l v) (fun _ => SPComp.bind (SPComp.get l) f)
      = SPComp.bind (SPComp.set l v) (fun _ => f v) := by
  funext h
  simp only [SPComp.bind, SPComp.set, SPComp.get, SDistr.pure_bind, Heap.get_set_same]

/-! ## `A{-M}`: the memory restriction -/

/-- The image of EasyCrypt's module restriction `A{-M}` on a single procedure:
started from heaps that agree outside `locs`, the procedure returns equal values
and leaves heaps that still agree outside `locs`. -/
def RespectsLocs {α β : Type} (locs : LocSet) (f : α → SPComp β) : Prop :=
  ∀ x, rHoare (agreeOff locs) (f x) (f x)
    (fun r₁ h₁ r₂ h₂ => r₁ = r₂ ∧ agreeOff locs h₁ h₂)

/-- The whole-module form of `A{-M}`: every procedure of the module respects the
footprint. -/
def ModuleRespectsLocs {I : EcInterface} (locs : LocSet) (M : ModuleImpl I) : Prop :=
  ∀ p, RespectsLocs locs (M.proc p)

/-- A heap-independent procedure respects every footprint: it cannot read the
heap, so it cannot see the difference, and it cannot write it, so it cannot
create one. This witnesses that `RespectsLocs` is satisfiable. -/
theorem respectsLocs_of_isPure {α β : Type} (locs : LocSet) (f : α → SPComp β)
    (hf : ∀ x, SPComp.IsPure (f x)) : RespectsLocs locs f := by
  intro x h₁ h₂ hpre
  obtain ⟨d, hd⟩ := hf x
  rw [hd h₁, hd h₂]
  exact liftR_bind (R := Eq) (liftR_refl d) (fun a a' haa' => liftR_pure ⟨haa', hpre⟩)

/-- A procedure whose write-set is inside `locs`, and which returns equal values
when started from heaps agreeing outside `locs`, is restricted. The heap half of
the conclusion is the core frame rule `r_frame_agreeOff` applied to the value
half: each run leaves the locations outside `locs` as it found them, and the two
initial heaps agree there. -/
theorem RespectsLocs.of_preservesOutside {α β : Type} {locs : LocSet} {f : α → SPComp β}
    (hpres : ∀ x, PreservesOutside (f x) locs)
    (hval : ∀ x, rHoare (agreeOff locs) (f x) (f x) (fun r₁ _ r₂ _ => r₁ = r₂)) :
    RespectsLocs locs f := by
  intro x
  exact rHoare_mono_pre (r_frame_agreeOff (hpres x) (hpres x) (hval x))
    (fun _ _ hpre => ⟨hpre, hpre⟩)

/-- Restriction is closed under sequencing: running a restricted procedure and
feeding its result to a restricted continuation is again restricted. A functor
whose body only sequences calls to a restricted parameter therefore inherits the
restriction. -/
theorem RespectsLocs.bind {α β γ : Type} {locs : LocSet} {f : α → SPComp β}
    {k : β → SPComp γ} (hf : RespectsLocs locs f) (hk : RespectsLocs locs k) :
    RespectsLocs locs (fun x => SPComp.bind (f x) k) := by
  intro x
  refine rHoare_bind (hf x) (fun a b => ?_)
  rintro h₁ h₂ ⟨rfl, hoff⟩
  exact hk a h₁ h₂ hoff

/-- Restriction is preserved by post-processing the result with a pure
function. -/
theorem RespectsLocs.map {α β γ : Type} {locs : LocSet} {f : α → SPComp β}
    (hf : RespectsLocs locs f) (g : β → γ) :
    RespectsLocs locs (fun x => SPComp.bind (f x) (fun b => SPComp.pure (g b))) :=
  hf.bind (respectsLocs_of_isPure locs _ (fun b => SPComp.pure_isPure (g b)))

/-! ## `glob A`: the footprint a module lives on -/

/-- The image of "the module's global state is the footprint `locs`" on a single
procedure: started from heaps that agree on `locs`, the procedure returns equal
values and leaves heaps that still agree on `locs`. -/
def RespectsOn {α β : Type} (locs : LocSet) (f : α → SPComp β) : Prop :=
  ∀ x, rHoare (agreeOn locs) (f x) (f x)
    (fun r₁ h₁ r₂ h₂ => r₁ = r₂ ∧ agreeOn locs h₁ h₂)

/-- The whole-module form: every procedure of the module lives on the
footprint. -/
def ModuleRespectsOn {I : EcInterface} (locs : LocSet) (M : ModuleImpl I) : Prop :=
  ∀ p, RespectsOn locs (M.proc p)

/-- A heap-independent procedure lives on every footprint, including the empty
one. This witnesses that `RespectsOn` is satisfiable. -/
theorem respectsOn_of_isPure {α β : Type} (locs : LocSet) (f : α → SPComp β)
    (hf : ∀ x, SPComp.IsPure (f x)) : RespectsOn locs f := by
  intro x h₁ h₂ hpre
  obtain ⟨d, hd⟩ := hf x
  rw [hd h₁, hd h₂]
  exact liftR_bind (R := Eq) (liftR_refl d) (fun a a' haa' => liftR_pure ⟨haa', hpre⟩)

/-- Living on a footprint is closed under sequencing. -/
theorem RespectsOn.bind {α β γ : Type} {locs : LocSet} {f : α → SPComp β}
    {k : β → SPComp γ} (hf : RespectsOn locs f) (hk : RespectsOn locs k) :
    RespectsOn locs (fun x => SPComp.bind (f x) k) := by
  intro x
  refine rHoare_bind (hf x) (fun a b => ?_)
  rintro h₁ h₂ ⟨rfl, hon⟩
  exact hk a h₁ h₂ hon

/-! ## `islossless`: termination -/

/-- The image of EasyCrypt's `islossless M.f`: the procedure never fails, i.e.
its output sub-distribution has total mass one from every heap. -/
def ProcLossless {α β : Type} (f : α → SPComp β) : Prop := ∀ x, isLossless (f x)

/-- The whole-module form of `islossless`. -/
def ModuleLossless {I : EcInterface} (M : ModuleImpl I) : Prop :=
  ∀ p, ProcLossless (M.proc p)

theorem ProcLossless.bind {α β γ : Type} {f : α → SPComp β} {k : β → SPComp γ}
    (hf : ProcLossless f) (hk : ProcLossless k) :
    ProcLossless (fun x => SPComp.bind (f x) k) :=
  fun x => lossless_bind (hf x) (fun b => hk b)

/-- The probability of the trivial event is the total mass. This is what relates
the two forms an imported `islossless` can arrive in: the dedicated `ProcLossless`
node and the bounded Hoare judgement `bd_hoare[q : true ==> true] = 1`, whose
translation measures the trivial event. -/
theorem prEventComp_true {α : Type} (c : SPComp α) (h₀ : Heap) :
    prEventComp c h₀ (fun _ _ => True) = SDistr.mass (c h₀) := by
  simp only [prEventComp, prEvent, if_pos trivial, tsum_some_eq_mass]

/-- A lossless procedure terminates with probability one at every argument and
from every initial memory, which is the bounded Hoare judgement an imported
`islossless` translates to when it arrives as `bd_hoare[q : true ==> true] = 1`. -/
theorem prEventComp_true_eq_one_of_procLossless {α β : Type} {f : α → SPComp β}
    (hf : ProcLossless f) (x : α) (h₀ : Heap) :
    prEventComp (f x) h₀ (fun _ _ => True) = 1 := by
  rw [prEventComp_true]; exact hf x h₀

end CatCrypt.Crypto.EasyCryptImport

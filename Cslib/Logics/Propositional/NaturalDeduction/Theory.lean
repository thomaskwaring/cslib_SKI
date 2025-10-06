/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
import Cslib.Logics.Propositional.NaturalDeduction.Basic
import Mathlib.Tactic.NthRewrite

/-! # Operations on theories for natural deduction

## Main definitions

- `Theory.WeakerThan` : a theory `T` is weaker than `T'` if everything derivable from `T` is also
derivable from `T'`.
- `Theory.Saturation` : the theory of everything provable from `T`.
- `Theory.Saturated` : `T` is saturated if everything provable from `T` is in `T`.

## Main results

- `instPreorderTheory` : the relation `Theory.WeakerThan` is a preorder.
- `Theory.saturation_saturation` : the saturation of a theory is saturated.
- `Theory.Derivable.iff_derivable_saturation` : a proposition is derivable from `T` iff it is
derivable from `T.saturation` — equivalently, saturation is idempotent (viz `Theory.saturate_idem`).

-/

namespace PL

namespace NJ

variable {Atom : Type u} [DecidableEq Atom]

def Theory.WeakerThan (T T' : Theory Atom) : Prop :=
  ∀ (A : Proposition Atom), T.Derivable A → T'.Derivable A

instance instLETheory : LE (Theory Atom) where
  le := Theory.WeakerThan

instance instPreorderTheory : Preorder (Theory Atom) where
  lt T T' := T.WeakerThan T' ∧ ¬ T'.WeakerThan T
  le_refl _ _ := id
  le_trans _ _ _ h h' := fun B hB => h' B <| h B hB

theorem Theory.weakerThan_of_subset {T T' : Theory Atom} (h : T ⊆ T') : T ≤ T' :=
  fun _ ⟨Γ, _, D⟩ => ⟨Γ, by grind, D⟩

def Theory.saturated (T : Theory Atom) : Prop :=
  ∀ (A : Proposition Atom), ⊢[T] A → A ∈ T

def Theory.saturate (T : Theory Atom) : Theory Atom := {A : Proposition Atom | ⊢[T] A}

theorem Theory.saturate_def (T : Theory Atom) (A : Proposition Atom) :
  A ∈ T.saturate ↔ ⊢[T] A := Eq.to_iff rfl

theorem Theory.weakerThan_iff {T T' : Theory Atom} : T ≤ T' ↔ T.saturate ⊆ T'.saturate := by
  constructor <;> intro h
  · intro A
    rw [T.saturate_def, T'.saturate_def]
    exact h A
  · intro A hA
    have : _ := h <| (T.saturate_def A).mpr hA
    rwa [←T'.saturate_def]

theorem Theory.saturation_saturated (T : Theory Atom) : T.saturate.saturated := by
  intro B ⟨Γ, h, D⟩
  rw [Theory.saturate_def]
  have : Γ ⊢[T] B := ⟨Γ, by grind, D⟩
  refine Theory.Derivable.multi_subs ?_ this
  intro A hA
  exact (T.saturate_def A).mpr (h hA)

theorem Theory.saturated_iff (T : Theory Atom) : T.saturated ↔ T = T.saturate := by
  constructor <;> intro h
  · ext A
    rw [T.saturate_def]
    constructor
    · exact Theory.Derivable.ax'
    · exact h A
  · rw [h]
    exact T.saturation_saturated

theorem Theory.saturate_idem (T : Theory Atom) : T.saturate.saturate = T.saturate := by
  nth_rw 2 [T.saturate.saturated_iff.mp T.saturation_saturated]

theorem Theory.weaker_than_saturation (T : Theory Atom) : T ≤ T.saturate := by
  intro A hA
  exact Theory.Derivable.ax' hA

theorem Theory.Derivable.iff_derivable_saturation {T : Theory Atom} {A : Proposition Atom} :
    ⊢[T.saturate] A ↔ ⊢[T] A := by
  constructor <;> intro h
  · rwa [←T.saturate.saturate_def, T.saturate_idem, T.saturate_def] at h
  · exact (T.weaker_than_saturation A) h

theorem Theory.saturation_weaker_than (T : Theory Atom) : T.saturate ≤ T := by
  intro _ _
  rwa [← Theory.Derivable.iff_derivable_saturation]


end NJ

end PL

/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
module

public import Cslib.Logics.Propositional.NaturalDeduction.Basic
public import Mathlib.Order.Heyting.Basic

@[expose] public section

namespace Cslib.Logic.PL

open Proposition Theory InferenceSystem DerivableIn

variable {Atom : Type u} {T : Theory Atom}

structure KripkeModel (Atom Worlds : Type*) [PartialOrder Worlds] where
  Forces' : Worlds → Atom → Prop
  forces'_monotone : Monotone Forces'

variable {Worlds : Type*} [PartialOrder Worlds] {C : KripkeModel Atom Worlds}

def KripkeModel.Forces (C : KripkeModel Atom Worlds) (c : Worlds) : Proposition Atom → Prop
  | atom x => C.Forces' c x
  | Proposition.and A B => C.Forces c A ∧ C.Forces c B
  | Proposition.or A B => C.Forces c A ∨ C.Forces c B
  | impl A B => ∀ c' : Worlds, c ≤ c' → C.Forces c' A → C.Forces c' B

scoped notation c " ⊨[" C "] " A => KripkeModel.Forces C c A

lemma KripkeModel.forces_monotone {c c' : Worlds} (h : c ≤ c') (A : Proposition Atom) (hc : c ⊨[C] A) :
    c' ⊨[C] A := by
  induction A with
  | atom x => exact C.forces'_monotone h x hc
  | and A B aih bih => exact ⟨aih hc.1, bih hc.2⟩
  | or A B aih bih =>
    cases hc with
    | inl hA => exact Or.inl <| aih hA
    | inr hB => exact Or.inr <| bih hB
  | impl A B aih bih =>
    intro c'' h' hA
    exact hc c'' (h.trans h') hA

-- def Theory.Derivation.size {T : Theory Atom} [DecidableEq Atom] {Γ : Ctx Atom}
--     {B : Proposition Atom} (D : T.Derivation (Γ ⊢ B)) : ℕ :=
--   match D with
--   | ax _ | ass _ => 1
--   | conjI D D' | implE D D' => D.size + D'.size + 1
--   | conjE₁ D | conjE₂ D | disjI₁ D | disjI₂ D | implI _ D => D.size + 1
--   | disjE D D' D'' => D.size + D'.size + D''.size + 1
--   termination_by sizeOf D

theorem Theory.Derivation.forces [DecidableEq Atom] {Γ : Ctx Atom} {B : Proposition Atom}
    {c : Worlds} (hT : ∀ A ∈ T, c ⊨[C] A) (D : T.Derivation Γ B) (hΓ : ∀ A ∈ Γ, c ⊨[C] A) :
    c ⊨[C] B := by
  induction D generalizing c with
  | ax hB => exact hT _ hB
  | ass hB => exact hΓ _ hB
  | conjI DA DB aih bih => exact ⟨aih hT hΓ, bih hT hΓ⟩
  | conjE₁ D ih => exact (ih hT hΓ).1
  | conjE₂ D ih => exact (ih hT hΓ).2
  | disjI₁ D ih => exact Or.inl <| ih hT hΓ
  | disjI₂ D ih => exact Or.inr <| ih hT hΓ
  | disjE D DA DB ih aih bih =>
    cases ih hT hΓ with
    | inl hA =>
      apply aih hT
      simp_rw [Finset.mem_insert]
      rintro A' (rfl | hA')
      · exact hA
      · exact hΓ A' hA'
    | inr hB =>
      apply bih hT
      simp_rw [Finset.mem_insert]
      rintro A' (rfl | hA')
      · exact hB
      · exact hΓ A' hA'
  | implI Γ D ih =>
    intro c' hc hA
    apply ih
    · intro _ h
      exact (C.forces_monotone hc) _ (hT _ h)
    · simp_rw [Finset.mem_insert]
      rintro A' (rfl | hA')
      · exact hA
      · exact (C.forces_monotone hc) A' (hΓ A' hA')
  | implE D D' ih ih' => exact ih hT hΓ _ (le_refl c) <| ih' hT hΓ

end Cslib.Logic.PL

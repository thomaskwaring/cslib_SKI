/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
import Cslib.Logics.NaturalDeduction.NJ
import Mathlib.Order.Heyting.Basic
import Mathlib.Data.Finset.Fold
import Mathlib.Order.Fin.Basic

/-! # Heyting-algebra semantics for intuitionistic propositional logic -/

universe u

variable {Atom : Type u} [DecidableEq Atom]

namespace IPL

namespace Semantics

variable {H : Type _} [HeytingAlgebra H]

abbrev Valuation (Atom : Type u) (H : Type _) [HeytingAlgebra H] := Atom → H

variable (v : Valuation Atom H)

open Proposition NJ

/-- The interpretation of a compound formula in a Heyting algebra -/
def Proposition.interpret : Proposition Atom → H
  | atom x => v x
  | bot => ⊥
  | conj A B => (Proposition.interpret A) ⊓ (Proposition.interpret B)
  | disj A B => (Proposition.interpret A) ⊔ (Proposition.interpret B)
  | impl A B => (Proposition.interpret A) ⇨ (Proposition.interpret B)

scoped notation v "[" A "]" => Proposition.interpret v A

-- instance interpPropCoe : CoeFun (Valuation Atom H) (fun _ => Proposition Atom → H) where
--   coe := Proposition.interpret

def Ctx.interpret (Γ : Ctx Atom) : H := Γ.fold (· ⊓ ·) ⊤ (Proposition.interpret v)

scoped notation v "[" Γ "]" => Ctx.interpret v Γ

-- instance interpCtxCoe : CoeFun (Valuation Atom H) (fun _ => Ctx Atom → H) where
--   coe := Ctx.interpret

theorem Ctx.interpret_antitone {Γ Δ : Ctx Atom} (h : Γ ⊆ Δ) :
    v[Δ] ≤ v[Γ] := by
  have h_disj : Disjoint Γ (Δ \ Γ) := Finset.disjoint_sdiff
  have hΔ : Γ.disjUnion (Δ \ Γ) h_disj = Δ := by grind
  have h_top : ⊤ ⊓ ⊤ = (⊤ : H) := top_inf_eq ⊤
  unfold interpret
  nth_rw 1 [←h_top]
  rw [←hΔ, Finset.fold_disjUnion h_disj]
  exact inf_le_left


def Sequent.valid : Sequent Atom → Prop
  | ⟨Γ,A⟩ => (v[Γ]) ≤ (v[A])

open Derivation

protected theorem sound {S : Sequent Atom} (D : Derivation S) : Sequent.valid v S := by
  induction D with
  | ax Γ A =>
    simp [Sequent.valid, Ctx.interpret]
  | botE _ _ ih =>
    dsimp! only at ih ⊢
    trans ⊥
    · assumption
    · exact OrderBot.bot_le _
  | conjI _ _ ih ih' =>
    dsimp! only at ih ih' ⊢
    exact le_inf ih ih'
  | @conjE₁ _ A B _ ih =>
    dsimp! only at ih ⊢
    trans v[A] ⊓ v[B]
    · assumption
    · exact inf_le_left
  | @conjE₂ _ A B _ ih =>
    dsimp! only at ih ⊢
    trans v[A] ⊓ v[B]
    · assumption
    · exact inf_le_right
  | @disjI₁ _ A _ _ ih =>
    dsimp! only at ih ⊢
    trans v[A]
    · assumption
    · exact le_sup_left
  | @disjI₂ _ _ B _ ih =>
    dsimp! only at ih ⊢
    trans v[B]
    · assumption
    · exact le_sup_right
  | @disjE Γ A B C _ _ _ ih₁ ih₂ ih₃ =>
    dsimp! only at ih₁ ih₂ ih₃ ⊢
    trans v[insert A Γ] ⊔ v[insert B Γ]
    · simp only [Ctx.interpret, Finset.fold_insert_idem]
      rw [←inf_sup_right]
      apply le_inf
      · assumption
      · rfl
    · apply sup_le <;> assumption
  | implI Γ _ ih =>
    dsimp! only at ih ⊢
    refine le_himp_iff.mpr ?_
    simpa [Ctx.interpret, inf_comm] using ih
  | @implE _ A B _ _ ih ih' =>
    dsimp! only at ih ih' ⊢
    trans (v[A] ⇨ v[B]) ⊓ v[A]
    · apply le_inf <;> assumption
    · exact himp_inf_le

protected theorem sound' {S : Sequent Atom} (h : Derivable S) : Sequent.valid v S :=
  let ⟨D⟩ := h; IPL.Semantics.sound v D

theorem not_lem_derivable (x : Atom) : ¬ Derivable ⟨∅, (atom x).disj <| impl (atom x) bot⟩ := by
  intro h
  let v : Atom → Fin 3 := fun _ => 1
  have h_sound : _ := IPL.Semantics.sound' v h
  simp [Sequent.valid, Ctx.interpret, Finset.fold_empty, Top.top, Proposition.interpret,
    v, Bot.bot, himp] at h_sound

theorem not_dne_derivable (x : Atom) : ¬ Derivable ⟨{impl (atom x) bot |>.impl bot}, atom x⟩ := by
  intro h
  let v : Atom → Fin 3 := fun _ => 1
  have h_sound : _ := IPL.Semantics.sound' v h
  simp [Sequent.valid, Ctx.interpret, Proposition.interpret, Finset.fold_singleton, v, Top.top,
    Bot.bot, himp] at h_sound

end Semantics

end IPL

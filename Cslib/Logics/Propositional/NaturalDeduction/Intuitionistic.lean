/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
module

public import Cslib.Logics.Propositional.NaturalDeduction.Basic
public import Mathlib.Order.WithBot

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Proposition Theory Derivation InferenceSystem DerivableIn

variable {Atom : Type u} [DecidableEq Atom] [Bot Atom]

/-- An intuitionistic `T`-derivation of {A₁, ..., Aₙ} ⊢ B demonstrates B using (undischarged)
assumptions among Aᵢ, possibly appealing to axioms from `T`. This adds ex falso quodlibet to
`T`.Derivation. -/
inductive Theory.IntDerivation {T : Theory Atom} : Ctx Atom → Proposition Atom → Type u where
  /-- Axiom -/
  | ax {Γ : Ctx Atom} {A : Proposition Atom} (_ : A ∈ T) : IntDerivation Γ A
  /-- Assumption -/
  | ass {Γ : Ctx Atom} {A : Proposition Atom} (_ : A ∈ Γ) : IntDerivation Γ A
  /-- Conjunction introduction -/
  | conjI {Γ : Ctx Atom} {A B : Proposition Atom} :
      IntDerivation Γ A → IntDerivation Γ B → IntDerivation Γ (A ∧ B)
  /-- Conjunction elimination left -/
  | conjE₁ {Γ : Ctx Atom} {A B : Proposition Atom} : IntDerivation Γ (A ∧ B) → IntDerivation Γ A
  /-- Conjunction elimination right -/
  | conjE₂ {Γ : Ctx Atom} {A B : Proposition Atom} : IntDerivation Γ (A ∧ B) → IntDerivation Γ B
  /-- Disjunction introduction left -/
  | disjI₁ {Γ : Ctx Atom} {A B : Proposition Atom} : IntDerivation Γ A → IntDerivation Γ (A ∨ B)
  /-- Disjunction introduction right -/
  | disjI₂ {Γ : Ctx Atom} {A B : Proposition Atom} : IntDerivation Γ B → IntDerivation Γ (A ∨ B)
  /-- Disjunction elimination -/
  | disjE {Γ : Ctx Atom} {A B C : Proposition Atom} : IntDerivation Γ (A ∨ B) →
      IntDerivation (insert A Γ) C → IntDerivation (insert B Γ) C → IntDerivation Γ C
  /-- Implication introduction -/
  | implI {A B : Proposition Atom} (Γ : Ctx Atom) :
      IntDerivation (insert A Γ) B → IntDerivation Γ (A → B)
  /-- Implication elimination -/
  | implE {Γ : Ctx Atom} {A B : Proposition Atom} :
      IntDerivation Γ (A → B) → IntDerivation Γ A → IntDerivation Γ B
  /-- Ex falso quodlibet. -/
  | efq {Γ : Ctx Atom} (A : Proposition Atom) : IntDerivation Γ ⊥ → IntDerivation Γ A

variable {T : Theory Atom}

def Theory.IntDerivation.toDerivation {T : Theory Atom} {Γ : Ctx Atom} {A : Proposition Atom} :
    T.IntDerivation Γ A → (T ∪ IPL).Derivation Γ A
  | ax hA => .ax (Set.mem_union_left IPL hA)
  | ass hA => .ass hA
  | conjI DA DB => .conjI DA.toDerivation DB.toDerivation
  | conjE₁ D => .conjE₁ D.toDerivation
  | conjE₂ D => .conjE₂ D.toDerivation
  | disjI₁ D => .disjI₁ D.toDerivation
  | disjI₂ D => .disjI₂ D.toDerivation
  | disjE D DA DB => .disjE D.toDerivation DA.toDerivation DB.toDerivation
  | implI Γ D => .implI Γ D.toDerivation
  | implE D D' => .implE D.toDerivation D'.toDerivation
  | efq A D => .implE (A := ⊥) (.ax (Set.mem_union_right T ⟨A, rfl⟩)) D.toDerivation

theorem derivableIn_intuitionisticCompletion_iff_nonempty_intDerivation {T : Theory Atom}
    {Γ : Ctx Atom} {A : Proposition Atom} :
    DerivableIn (T ∪ IPL : Theory Atom) (⟨Γ, A⟩ : Sequent) ↔
    Nonempty (T.IntDerivation Γ A) := by
  refine ⟨fun ⟨(D : (T ∪ IPL).Derivation Γ A)⟩ => ?_,
    fun h => ⟨h.some.toDerivation⟩⟩
  induction D with
  | ax hA =>
    cases hA
    case inl hA => exact ⟨.ax hA⟩
    case inr hA =>
      obtain ⟨A, rfl⟩ := hA
      exact ⟨.implI _ <| .efq A <| .ass (Finset.mem_insert_self ⊥ _)⟩
  | ass hA => exact ⟨.ass hA⟩
  | conjI DA DB aih bih => exact ⟨.conjI (aih ⟨DA⟩).some (bih ⟨DB⟩).some⟩
  | conjE₁ D ih => exact ⟨.conjE₁ (ih ⟨D⟩).some⟩
  | conjE₂ D ih => exact ⟨.conjE₂ (ih ⟨D⟩).some⟩
  | disjI₁ D ih => exact ⟨.disjI₁ (ih ⟨D⟩).some⟩
  | disjI₂ D ih => exact ⟨.disjI₂ (ih ⟨D⟩).some⟩
  | disjE D DA DB ih aih bih => exact ⟨.disjE (ih ⟨D⟩).some (aih ⟨DA⟩).some (bih ⟨DB⟩).some⟩
  | implI Γ D ih => exact ⟨.implI Γ (ih ⟨D⟩).some⟩
  | implE D D' ih ih' => exact ⟨.implE (ih ⟨D⟩).some (ih' ⟨D'⟩).some⟩

end Cslib.Logic.PL

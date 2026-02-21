/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public meta import Cslib.Languages.CombinatoryLogic.Defs
public import Cslib.Foundations.Data.OmegaSequence.Init
public import Cslib.Foundations.Data.Relation

@[expose] public section

namespace Cslib.SKI

open Red Relation ωSequence

variable {Base : Type*}

inductive Ty (Base : Type*) where
  | base : Base → Ty Base
  | arr : Ty Base → Ty Base → Ty Base

scoped infixr:70 " ⤳ " => Ty.arr

open Ty

inductive Typing : SKI → Ty Base → Prop where
  | typeS (A B C : Ty Base) : Typing S ((A ⤳ B ⤳ C) ⤳ (A ⤳ B) ⤳ A ⤳ C)
  | typeK (A B : Ty Base) : Typing K (A ⤳ B ⤳ A)
  | typeI (A : Ty Base) : Typing I (A ⤳ A)
  | typeApp (A B : Ty Base) (x y : SKI) : Typing x (A ⤳ B) → Typing y A → Typing (x ⬝ y) B

attribute [scoped grind .] Typing.typeS Typing.typeK Typing.typeI Typing.typeApp
attribute [scoped grind cases] Typing

scoped notation:50 "⊢ " t " ∶ " A:arg => Typing t A

namespace Typing

variable {A B C X : Ty Base} {x y : SKI}

lemma S_iff : ⊢ S ∶ X ↔ ∃ A B C, X = (A ⤳ B ⤳ C) ⤳ (A ⤳ B) ⤳ A ⤳ C := by grind

lemma K_iff : ⊢ K ∶ X ↔ ∃ A B, X = (A ⤳ B ⤳ A) := by grind

lemma I_iff : ⊢ I ∶ X ↔ ∃ A, X = (A ⤳ A) := by grind

lemma app_iff : ⊢ (x ⬝ y) ∶ B ↔ ∃ A, ⊢ x ∶ (A ⤳ B) ∧ ⊢ y ∶ A := by grind

theorem subject_reduction (h : x ⭢ y) (hx : ⊢ x ∶ X) : ⊢ y ∶ X := by
  induction h generalizing X
  case red_S =>
    simp_rw [app_iff, S_iff] at hx
    grind [app_iff]
  all_goals grind

end Typing

abbrev SN (x : SKI) : Prop := ¬ ∃ xs : ωSequence SKI, xs 0 = x ∧ ∀ n : ℕ, xs n ⭢ xs (n + 1)

lemma SN.of_normal (x : SKI) (hx : Normal Red x) : SN x := by
  intro ⟨xs, h0, htr⟩
  exact hx ⟨xs 1, by simpa [h0] using htr 0⟩

def SemTyping (x : SKI) : Ty Base → Prop
  | base _ => SN x
  | arr A B => ∀ y, SemTyping y A → SemTyping (x ⬝ y) B

scoped notation:50 "⊨ " t " ∶ " A:arg => SemTyping t A

theorem SN_head_of_SN {x y : SKI} (h : SN (x ⬝ y)) : SN x := by
  contrapose! h
  obtain ⟨xs, h0, htr⟩ := h
  use map (· ⬝ y) xs
  constructor
  · simpa
  · intro n
    simpa using red_head _ _ _ (htr n)

@[reducible]
def IsValue : SKI → Prop
  | S | S ⬝ _ | S ⬝ _ ⬝ _ | K | K ⬝ _ | I => True
  | _ => False

@[scoped grind .]
lemma reducible_head {x y : SKI} (hx : Reducible Red x) : Reducible Red (x ⬝ y) := by
  obtain ⟨x', hx⟩ := hx
  exact ⟨x' ⬝ y, red_head _ _ _ hx⟩

@[scoped grind .]
lemma reducible_S {x y z : SKI} : Reducible Red (S ⬝ x ⬝ y ⬝ z) := ⟨_, red_S ..⟩

@[scoped grind .]
lemma reducible_K {x y : SKI} : Reducible Red (K ⬝ x ⬝ y) := ⟨_, red_K ..⟩

@[scoped grind .]
lemma reducible_I {x : SKI} : Reducible Red (I ⬝ x) := ⟨_, red_I ..⟩

lemma progress : (x : SKI) → x.IsValue ∨ Reducible Red x
  | S | S ⬝ _ | S ⬝ _ ⬝ _ | K | K ⬝ _ | I => by simp
  | I ⬝ x => Or.inr reducible_I
  | I ⬝ x ⬝ y => Or.inr <| reducible_head <| reducible_I
  | K ⬝ x ⬝ y => Or.inr reducible_K
  | w ⬝ x ⬝ y ⬝ z => by
    right
    obtain (hw | hw) := progress w
    · unfold IsValue at hw
      split at hw
      · exact reducible_S
      · exact reducible_head reducible_S
      · exact reducible_head <| reducible_head reducible_S
      · exact reducible_head reducible_K
      · exact reducible_head <| reducible_head reducible_K
      · exact reducible_head <| reducible_head reducible_I
      · exact False.elim hw
    · exact reducible_head <| reducible_head <| reducible_head hw


end Cslib.SKI

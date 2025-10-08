/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
import Cslib.Logics.NaturalDeduction.NJ

universe u v

variable {Atom : Type u} [DecidableEq Atom]

namespace IPL

open Proposition

namespace NJ

open Derivation

structure DerivationClosed (S : Set (Proposition Atom)) where
  der {Γ : Ctx Atom} {B : Proposition Atom} (hΓ : ↑Γ ⊆ S) (hB : Derivable ⟨Γ, B⟩) : B ∈ S

def Realiser : Proposition Atom → Type v
  | atom _ => PUnit
  | bot => PUnit
  | conj A B => Realiser A × Realiser B
  | disj A B => Realiser A ⊕ Realiser B
  | impl A B => Realiser A → Realiser B

def Realises (S : Set (Proposition Atom)) : (A : Proposition Atom) → Realiser A → Prop
  | atom x, _ => atom x ∈ S
  | bot, _ => False
  | conj A B, t => Realises S A t.1 ∧ Realises S B t.2
  | disj A _, Sum.inl x => Realises S A x
  | disj _ B, Sum.inr y => Realises S B y
  | impl A B, f => impl A B ∈ S ∧ ∀ x : Realiser A, Realises S A x → Realises S B (f x)

theorem mem_gluing_of_realised (S : Set (Proposition Atom)) (hS : DerivationClosed S) :
    (A : Proposition Atom) → (x : Realiser A) → Realises S A x → A ∈ S
  | atom _, _, h => h
  | bot, _, h => False.elim h
  | conj A B, ⟨x, y⟩, ⟨hx, hy⟩ => by
    refine hS.der (Γ := {A, B}) ?_ ?_
    · have : A ∈ S := mem_gluing_of_realised S hS A x hx
      have : B ∈ S := mem_gluing_of_realised S hS B y hy
      grind
    · exact ⟨conjI (A := A) (B := B) (ax' <| by grind) (ax' <| by grind)⟩
  | disj A _, Sum.inl x, hx => by
    refine hS.der (Γ := {A}) ?_ ?_
    · have : A ∈ S := mem_gluing_of_realised S hS A x hx
      grind
    · exact ⟨disjI₁ (ax' <| by grind)⟩
  | disj _ B, Sum.inr y, hy => by
    refine hS.der (Γ := {B}) ?_ ?_
    · have : B ∈ S := mem_gluing_of_realised S hS B y hy
      grind
    · exact ⟨disjI₂ (ax' <| by grind)⟩
  | impl A B, _, ⟨h, _⟩ => h

instance instInhabitedRealiser : (A : Proposition Atom) → Inhabited (Realiser A)
  | atom _ => ⟨()⟩
  | bot => ⟨()⟩
  | conj A B =>
    @instInhabitedProd _ _ (instInhabitedRealiser A) ((instInhabitedRealiser B))
  | disj A _ => ⟨Sum.inl (instInhabitedRealiser A).default⟩
  | impl _ B => @instInhabitedForall _ _ (instInhabitedRealiser B)

def Derivation.Realiser {Γ : Ctx Atom} {B : Proposition Atom} (ts : ∀ A ∈ Γ, Realiser A) :
    Derivation ⟨Γ, B⟩ → Realiser B
  | ax Γ A => ts A (Finset.mem_insert_self A Γ)
  | botE A _ => default
  | conjI D E => ⟨D.Realiser ts, E.Realiser ts⟩
  | conjE₁ D => (D.Realiser ts).1
  | conjE₂ D => (D.Realiser ts).2
  | disjI₁ D => Sum.inl <| D.Realiser ts
  | disjI₂ D => Sum.inr <| D.Realiser ts
  | @disjE _ _ Γ A B C D E₁ E₂ => by
    cases D.Realiser ts
    case inl t =>
      refine E₁.Realiser ?_
      intro A' hA'
      by_cases A' ∈ Γ
      case pos h => exact ts A' h
      case neg h =>
        have : A' = A := by grind
        exact this ▸ t
    case inr t =>
      refine E₂.Realiser ?_
      intro A' hA'
      by_cases A' ∈ Γ
      case pos h => exact ts A' h
      case neg h =>
        have : A' = B := by grind
        exact this ▸ t
  | @implI _ _ A B Γ D => by
    intro tA
    apply D.Realiser
    intro A' hA'
    by_cases A' ∈ Γ
    case pos h => exact ts A' h
    case neg h =>
      have : A' = A := by grind
      exact this ▸ tA
  | implE D E => D.Realiser ts <| E.Realiser ts

-- theorem adequacy (S : Set (Proposition Atom)) (Γ : Ctx Atom)
--     (ts : ∀ A ∈ Γ, Realiser A) (hts : ∀ (A : Proposition Atom) (h : A ∈ Γ), Realises S A (ts A h))
--     (B : Proposition Atom) (D : Derivation ⟨Γ, B⟩) : Realises S B <| D.Realiser ts := by
--   cases D
--   case ax Γ _ =>
--     unfold Derivation.Realiser
--     exact hts B (Finset.mem_insert_self B _)
--   case botE D =>
--     -- have : D.size < (botE B D).size := by grind [Derivation.size]
--     exact False.elim <| adequacy S Γ ts hts bot D
--   case conjI A B D E =>
--     unfold Realises Derivation.Realiser
--     reduce
--     -- have : D.size < (conjI D E).size := by grind [Derivation.size]
--     -- have : E.size < (conjI D E).size := by grind [Derivation.size]
--     constructor <;> apply adequacy <;> exact hts
--   case conjE₁ B' D =>
--     -- have : D.size < (conjE₁ D).size := by grind [Derivation.size]
--     have : _ := adequacy S Γ ts hts (B.conj B') D
--     unfold Realises at this
--     unfold Derivation.Realiser
--     exact this.1
--   case conjE₂ A D =>
--     have : _ := adequacy S Γ ts hts (A.conj B) D
--     unfold Realises at this
--     unfold Derivation.Realiser
--     exact this.2
--   case disjI₁ A B D =>
--     have :_ := adequacy S Γ ts hts A D
--     unfold Realises Derivation.Realiser
--     assumption
--   case disjI₂ A B D =>
--     have :_ := adequacy S Γ ts hts B D
--     unfold Realises Derivation.Realiser
--     assumption
--   -- case disjE A A' D E E' =>
--   --   unfold Derivation.Realiser
--   --   cases D.Realiser ts

--   termination_by D.size
-- --   decreasing_by all_goals sorry
-- --   -- · grind [Derivation.size]
-- --   -- ·
-- --   --   grind [Derivation.size]
-- --   -- --   ·
-- --     -- · expose_names
-- --     --   -- rw [h_3]




end NJ

end IPL

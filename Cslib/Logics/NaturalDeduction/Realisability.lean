/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
import Cslib.Logics.NaturalDeduction.NJ
import Mathlib.Computability.Primrec

universe u v

variable {Atom : Type u} [DecidableEq Atom]

namespace IPL

open Proposition

namespace NJ

open Derivation

def Realiser (base : Atom → Type v) : Proposition Atom → Type v
  | atom x => base x
  | bot => PUnit
  | conj A B => Realiser base A × Realiser base B
  | disj A B => Realiser base A ⊕ Realiser base B
  | impl A B => Realiser base A → Realiser base B

structure IsGluingSet (base : Atom → Type v) (u : (x : Atom) → base x → Prop)
    (S : Set (Proposition Atom)) where
  atoms : ∀ (x : Atom), (∃ (t : base x), u x t) → atom x ∈ S
  -- theorems : ∀ A : Proposition Atom, Proposition.PDerivable A → A ∈ S
  der {Γ : Ctx Atom} {B : Proposition Atom} (hΓ : ↑Γ ⊆ S) (hB : Derivable ⟨Γ, B⟩) : B ∈ S
  -- mp {A B : Proposition Atom} : (impl A B) ∈ S → A ∈ S → B ∈ S

def Realises {base : Atom → Type v} (ρ : (x : Atom) → base x → Prop) (S : Set (Proposition Atom))
    (hS : IsGluingSet base ρ S) : (A : Proposition Atom) → (Realiser base A) → Prop
  | atom x, t => ρ x t
  | bot, _ => False
  | conj A B, ⟨s, t⟩ => Realises ρ S hS A s ∧ Realises ρ S hS B t
  | disj A _, Sum.inl s => Realises ρ S hS A s
  | disj _ B, Sum.inr t => Realises ρ S hS B t
  | impl A B, f =>
      impl A B ∈ S ∧ ∀ t : Realiser base A, Realises ρ S hS A t → Realises ρ S hS B (f t)

theorem mem_gluing_of_realised {base : Atom → Type v} (ρ : (x : Atom) → base x → Prop)
    (S : Set (Proposition Atom)) (hS : IsGluingSet base ρ S) (A : Proposition Atom)
    (hA : ∃ t : Realiser base A, Realises ρ S hS A t) : A ∈ S := by
  cases A <;> let ⟨t, ht⟩ := hA <;> unfold Realises at ht
  case atom x =>
    exact hS.atoms x ⟨t, ht⟩
  case bot => contradiction
  case conj A B =>
    cases t
    case mk s t =>
      reduce at ht
      have hA : A ∈ S := mem_gluing_of_realised ρ S hS A ⟨s, ht.1⟩
      have hB : B ∈ S := mem_gluing_of_realised ρ S hS B ⟨t, ht.2⟩
      apply hS.der (Γ := {A, B}) (B := A.conj B) (by grind)
      constructor
      apply conjI <;> exact ax' (by grind)
  case disj A B =>
    cases t
    case inl s =>
      reduce at ht
      have hA : A ∈ S := mem_gluing_of_realised ρ S hS A ⟨s, ht⟩
      apply hS.der (Γ := {A}) (B := A.disj B) (by grind)
      constructor
      apply disjI₁
      exact ax' (by grind)
    case inr t =>
      reduce at ht
      have hB : B ∈ S := mem_gluing_of_realised ρ S hS B ⟨t, ht⟩
      apply hS.der (Γ := {B}) (B := A.disj B) (by grind)
      constructor
      apply disjI₂
      exact ax' (by grind)
  case impl A B => exact ht.1

instance instInhabitedRealiser {base : Atom → Type v} (h_base : ∀ x : Atom, Inhabited (base x)) :
    (A : Proposition Atom) → Inhabited (Realiser base A)
  | atom x => h_base x
  | bot => ⟨(default : PUnit)⟩
  | conj A B =>
      @instInhabitedProd _ _ (instInhabitedRealiser h_base A) ((instInhabitedRealiser h_base B))
  | disj A _ => ⟨Sum.inl (instInhabitedRealiser h_base A).default⟩
  | impl _ B => @instInhabitedForall _ _ (instInhabitedRealiser h_base B)

def Derivation.Realiser {base : Atom → Type v} {Γ : Ctx Atom} {B : Proposition Atom}
    (h_base : ∀ x : Atom, Inhabited (base x)) (ts : ∀ A ∈ Γ, Realiser base A) :
    (D : Derivation ⟨Γ, B⟩) → Realiser base B
  | ax Γ A => ts A (Finset.mem_insert_self A Γ)
  | botE A _ => (instInhabitedRealiser h_base A).default
  | conjI D E => ⟨D.Realiser h_base ts, E.Realiser h_base ts⟩
  | conjE₁ D => (D.Realiser h_base ts).1
  | conjE₂ D => (D.Realiser h_base ts).2
  | disjI₁ D => Sum.inl <| D.Realiser h_base ts
  | disjI₂ D => Sum.inr <| D.Realiser h_base ts
  | @disjE _ _ Γ A B C D E₁ E₂ => by
      cases D.Realiser h_base ts
      case inl t =>
        refine E₁.Realiser h_base ?_
        intro A' hA'
        by_cases A' ∈ Γ
        case pos h => exact ts A' h
        case neg h =>
          have : A' = A := by grind
          exact this ▸ t
      case inr t =>
        refine E₂.Realiser h_base ?_
        intro A' hA'
        by_cases A' ∈ Γ
        case pos h => exact ts A' h
        case neg h =>
          have : A' = B := by grind
          exact this ▸ t
    | @implI _ _ A B Γ D => by
        intro tA
        apply D.Realiser h_base
        intro A' hA'
        by_cases A' ∈ Γ
        case pos h => exact ts A' h
        case neg h =>
          have : A' = A := by grind
          exact this ▸ tA
    | implE D E => D.Realiser h_base ts <| E.Realiser h_base ts

-- theorem adequacy {base : Atom → Type v} (ρ : (x : Atom) → base x → Prop)
--     (S : Set (Proposition Atom)) (hS : IsGluingSet base ρ S)
--     (h_base : ∀ x : Atom, Inhabited (base x)) (Γ : Ctx Atom) (ts : ∀ A ∈ Γ, Realiser base A)
--     (hts : ∀ (A : Proposition Atom) (h : A ∈ Γ), Realises ρ S hS A (ts A h))
--     (B : Proposition Atom) (D : Derivation ⟨Γ, B⟩) : Realises ρ S hS B <| D.Realiser h_base ts := by
--   cases D
--   case ax x =>
--     unfold Derivation.Realiser
--     sorry

end NJ

end IPL

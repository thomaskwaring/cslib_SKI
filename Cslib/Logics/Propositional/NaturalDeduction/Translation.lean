/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
import Cslib.Logics.Propositional.NaturalDeduction.Theorems
import Cslib.Logics.Propositional.NaturalDeduction.Theory
import Mathlib.Data.Finset.Image

/-! # Double negation translation -/

namespace PL

open Proposition

variable {Atom : Type u} [DecidableEq Atom] [Bot Atom]

def Proposition.godelGentzenDoubleNeg : Proposition Atom → Proposition Atom
  | atom x => ~~ atom x
  | conj A B => conj (godelGentzenDoubleNeg A) (godelGentzenDoubleNeg B)
  | disj A B => ~(conj (~ godelGentzenDoubleNeg A) (~ godelGentzenDoubleNeg B))
  | impl A B => impl (godelGentzenDoubleNeg A) (godelGentzenDoubleNeg B)

scoped notation A:45 "ᵍ" => godelGentzenDoubleNeg A

namespace NJ

def Ctx.godelGentzenDoubleNeg : Ctx Atom → Ctx Atom :=
  Finset.image Proposition.godelGentzenDoubleNeg

scoped notation Γ:45 "ᵍ" => Ctx.godelGentzenDoubleNeg Γ

def Theory.godelGentzenDoubleNeg : Theory Atom → Theory Atom :=
  Set.image Proposition.godelGentzenDoubleNeg

scoped notation T:45 "ᵍ" => Theory.godelGentzenDoubleNeg T

theorem godelGentzen_insert {A : Proposition Atom} {Γ : Ctx Atom} :
  (insert A Γ : Ctx Atom)ᵍ = insert (Aᵍ) (Γᵍ) := by
    simp [Ctx.godelGentzenDoubleNeg]

open Derivation Theory

/-! ### Double negation shifts -/

def conjShift {A B : Proposition Atom} : Proposition.equiv (~~(A ⋏ B)) (~~A ⋏ ~~B) := by
  constructor
  · apply conjI
    · apply implI
      apply implE (A := ~(A ⋏ B))
      · exact ax' (by grind)
      · apply implI
        apply implE (A := A)
        · exact ax' (by grind)
        · apply conjE₁ (B := B)
          exact ax' (by grind)
    · apply implI
      apply implE (A := ~(A ⋏ B))
      · exact ax' (by grind)
      · apply implI
        apply implE (A := B)
        · exact ax' (by grind)
        · apply conjE₂ (A := A)
          exact ax' (by grind)
  · apply implI
    apply implE (A := ~B)
    · apply conjE₂ (A := ~~A) <| ax' (by grind)
    · apply implI
      apply implE (A := ~A)
      · apply conjE₁ (B := ~~B) <| ax' (by grind)
      · apply implI
        apply implE (A := A ⋏ B)
        · exact ax' (by grind)
        · apply conjI <;> exact ax' (by grind)

theorem conj_dn_shift {A B : Proposition Atom} : ~~(A ⋏ B) ≡ (~~A ⋏ ~~B) := by
  rw [equiv_iff]
  exact ⟨conjShift⟩

def impDnImpImpDn {A B : Proposition Atom} : Derivation ⟨∅,(~~ (A ⟶ B)) ⟶ (A ⟶ ~~B)⟩ := by
  apply implI; apply implI; apply implI
  apply implE (A := ~(A ⟶ B)) (ax' <| by grind)
  apply implI
  apply implE (A := B) (ax' <| by grind)
  apply implE (A := A) <;> exact ax' <| by grind

theorem imp_dn_of_dn_imp {A B : Proposition Atom} : ⊢((~~ (A ⟶ B)) ⟶ (A ⟶ ~~B)) :=
  ⟨∅, by grind, impDnImpImpDn⟩

def godelGentzenDNE {Γ : Ctx Atom} : (A : Proposition Atom) → Derivation ⟨Γ, ~~Aᵍ ⟶ Aᵍ⟩
  | atom x =>
    implI (Γ := Γ) <| Derivation.tne.weak' (by grind [Proposition.godelGentzenDoubleNeg])
  | conj A B => by
    apply implI
    apply conjI
    · apply implE (A := ~~Aᵍ) (godelGentzenDNE A)
      apply conjE₁ (B := ~~Bᵍ)
      exact conjShift.1.weak' (by grind [Proposition.godelGentzenDoubleNeg])
    · apply implE (A := ~~Bᵍ) (godelGentzenDNE B)
      apply conjE₂ (A := ~~Aᵍ)
      exact conjShift.1.weak' (by grind [Proposition.godelGentzenDoubleNeg])
  | disj A B =>
    implI (Γ := Γ) <| Derivation.tne.weak' (by grind [Proposition.godelGentzenDoubleNeg])
  | impl A B => by
    apply implI
    apply implI
    apply implE (A := ~~Bᵍ) (godelGentzenDNE B)
    apply implE (A := Aᵍ)
    · apply implE (A := ~~ (Aᵍ ⟶ Bᵍ)) (impDnImpImpDn.weak' (by grind))
      exact ax' (by grind [Proposition.godelGentzenDoubleNeg])
    · exact ax' (by grind)

theorem godelGentzen_dn_equiv (A : Proposition Atom) : ~~Aᵍ ≡ Aᵍ := by
  induction A with
  | atom x => exact equivalent_comm tne_equivalent
  | conj A B aih bih => exact equivalent_trans conj_dn_shift ((Theory.empty Atom).inf_wd aih bih)
  | disj A B aih bih => exact equivalent_comm tne_equivalent
  | impl A B aih bih =>
    constructor
    · refine Theory.Derivable.trans imp_dn_of_dn_imp ?_
      exact (Theory.empty Atom).himp_wd (by rfl) bih |>.1
    · exact impl_derivable_iff.mpr SDerivable.dni

/-! ### Negative translation -/

theorem Theory.godelGentzen_equiv {T : Theory Atom} [IsClassical T] (A : Proposition Atom) :
    A ≡[T] Aᵍ := by
  induction A with
  | atom x =>
    exact dn_equiv (atom x)
  | conj A B aih bih =>
    exact T.inf_wd aih bih
  | disj A B aih bih =>
    refine equivalent_trans (B := ~~Aᵍ ⋎ ~~Bᵍ) ?_ ?_
    · refine equivalent_trans (B := Aᵍ ⋎ Bᵍ) ?_ ?_
      · exact T.sup_wd aih bih
      · exact T.sup_wd (dn_equiv _) (dn_equiv _)
    · exact equivalent_comm disj_not_not_conj_equivalent
  | impl A B aih bih =>
    exact T.himp_wd aih bih

def isClassicalAx : Proposition Atom → Bool
  | impl A B => (decide <| A = (~~B)) || (decide <| A = ⊥)
  | _ => false

instance instDecidableCPL (A : Proposition Atom) : Decidable (A ∈ CPL) :=
  decidable_of_bool (isClassicalAx A) <| by grind [cases Proposition, isClassicalAx, CPL, IPL]

def Derivation.godelGentzenTranslation {Γ : Ctx Atom} {B : Proposition Atom} :
    (D : Derivation ⟨Γ, B⟩) → Derivation ⟨Γᵍ, Bᵍ⟩
  | ax Γ A => (godelGentzen_insert (A := A)) ▸ ax ..
  | conjI D E => conjI D.godelGentzenTranslation E.godelGentzenTranslation
  | conjE₁ D => conjE₁ D.godelGentzenTranslation
  | conjE₂ D => conjE₂ D.godelGentzenTranslation
  | @disjI₁ _ _ _ A B D =>
    implI _ <|
    implE (A := Aᵍ) (conjE₁ (B := ~Bᵍ) (ax ..)) <|
    D.godelGentzenTranslation.weak' (by grind)
  | @disjI₂ _ _ _ A B D =>
    implI _ <|
    implE (A := Bᵍ) (conjE₂ (A := ~Aᵍ) (ax ..)) <|
    D.godelGentzenTranslation.weak' (by grind)
  | @disjE _ _ _ A B C D E₁ E₂ => by
    let D' := D.godelGentzenTranslation
    refine implE (godelGentzenDNE C) ?_
    apply implI
    apply implE (A := (~Aᵍ ⋏ ~Bᵍ)) (D'.weak' <| by exact Finset.subset_insert ( ~ Cᵍ) (Γᵍ))
    apply conjI
    · apply implI
      apply implE (A := Cᵍ) (ax' <| by simp)
      refine E₁.godelGentzenTranslation.weak' ?_
      simp [Ctx.godelGentzenDoubleNeg]
    · apply implI
      apply implE (A := Cᵍ) (ax' <| by simp)
      refine E₂.godelGentzenTranslation.weak' ?_
      simp [Ctx.godelGentzenDoubleNeg]
  | implI Γ D => implI (Γᵍ) <| (godelGentzen_insert (Atom := Atom)) ▸ D.godelGentzenTranslation
  | implE D E => implE D.godelGentzenTranslation E.godelGentzenTranslation

theorem derivable_godelGentzen_efq {A : Proposition Atom} : ⊢(⊥ ⟶ A)ᵍ := by
  refine ⟨∅, by grind, ?_⟩
  apply implI
  apply implE (A := ~~Aᵍ) (godelGentzenDNE A)
  apply implI
  apply implE (A := (⊥ ⟶ ⊥))
  · have : (⊥ : Proposition Atom)ᵍ = ((⊥ ⟶ ⊥) ⟶ ⊥) := by
      simp [Proposition.godelGentzenDoubleNeg, instBotProposition]
    exact ax' (by grind)
  · exact derivationTop (Atom := Atom) |>.weak' (by grind)

theorem derivable_godelGentzen_dne {A : Proposition Atom} : ⊢(~~A ⟶ A)ᵍ := by
  refine ⟨∅, by grind, ?_⟩
  apply implI
  apply implE (A := ~~Aᵍ) (godelGentzenDNE A)
  apply implI
  refine implE (A := ⊥ ⟶ ⊥) ?_ (derivationTop.weak' (by grind))
  apply implE (A := (~A)ᵍ)
  · exact ax' (by grind [Proposition.godelGentzenDoubleNeg, instBotProposition])
  · apply implI; apply implI
    apply implE (A := Aᵍ) <;> exact ax' (by grind)

theorem derivable_godelGentzen_classicalAx {A : Proposition Atom} (hA : A ∈ CPL) : ⊢ Aᵍ := by
  simp_rw [CPL, IPL, Set.mem_union, Set.mem_range] at hA
  cases hA
  case inl h =>
    let ⟨A'', h⟩ := h
    rw [←h]
    exact Theory.Derivable.theory_weak _ _ (by grind) _ derivable_godelGentzen_efq
  case inr h =>
    let ⟨A'', h⟩ := h
    simp_rw [←h]
    apply Theory.Derivable.theory_weak (Theory.empty Atom) _ (by grind)
    exact derivable_godelGentzen_dne

theorem translation_sDerivable_iff {Γ : Ctx Atom} {A : Proposition Atom} :
    Γ ⊢[CPL] A ↔ Γᵍ ⊢ (Aᵍ) := by
constructor
· intro ⟨Δ, h, D⟩
  suffices ⊢[↑(Γᵍ)] (Aᵍ) by simp_all [SDerivable, Theory.SDerivable]
  refine Theory.Derivable.multi_subs (Γ := Δᵍ) ?_ (hB := ⟨Δᵍ,by simp,D.godelGentzenTranslation⟩)
  intro A hA
  simp_rw [Ctx.godelGentzenDoubleNeg, Finset.mem_image] at hA
  replace ⟨A', hAΔ, hAA'⟩ := hA
  rw [← hAA']
  have : _ := (Set.mem_union _ _ _).mp <| h hAΔ
  cases this
  case inl h =>
    exact (derivable_godelGentzen_classicalAx h).theory_weak _ _ (by grind)
  case inr h =>
    apply Theory.Derivable.ax'
    rw [Finset.mem_coe, Ctx.godelGentzenDoubleNeg, Finset.mem_image]
    grind
· intro h
  suffices ⊢[CPL ∪ Γ] (A) by simp_all [SDerivable, Theory.SDerivable]
  have : IsClassical (CPL ∪ ↑Γ : Theory Atom) := by
    apply instIsClassicalExtention (T := CPL)
    grind
  rw [Theory.equivalent_derivable <| Theory.godelGentzen_equiv A]
  refine Theory.Derivable.multi_subs (hB := h.theory_weak _ _ <| by grind) ?_
  intro A hA
  replace ⟨A',hA⟩ := Finset.mem_image.mp hA
  rw [←hA.2, ←Theory.equivalent_derivable <| Theory.godelGentzen_equiv (A')]
  apply Theory.Derivable.ax'
  grind

theorem Theory.translation_derivable_iff {T : Theory Atom} (B : Proposition Atom) :
    ⊢[T ∪ CPL] B ↔ ⊢[Tᵍ] (Bᵍ) := by
  constructor <;> intro h
  · let ⟨Γ, hΓ, D⟩ := h
    have : Γ ⊢[CPL] B := ⟨Γ, by grind, D⟩
    have : Γᵍ ⊢ Bᵍ := translation_sDerivable_iff.mp this
    refine Theory.Derivable.multi_subs ?_ (hB := this.theory_weak (T' := Tᵍ) _ (by grind))
    intro A hA
    replace ⟨A', hA', hA⟩ := Finset.mem_image.mp hA
    rw [←hA]
    have : A' ∈ T ∪ CPL := by grind
    cases Set.mem_union _ _ _|>.mp this
    case inl h =>
      apply Theory.Derivable.ax'
      apply (Set.mem_image _ _ _).mpr
      exists A'
    case inr h =>
      exact (derivable_godelGentzen_classicalAx h).theory_weak _ _ (by grind)
  · have : IsClassical (T ∪ CPL) := by apply instIsClassicalExtention (T := CPL); simp
    rw [Theory.equivalent_derivable <| Theory.godelGentzen_equiv B]
    suffices Tᵍ ≤ (T ∪ CPL) by exact (this _) h
    intro A ⟨Γ, hΓ, D⟩
    have : Γ ⊢[T ∪ CPL] A := ⟨Γ, by grind, D⟩
    refine Theory.Derivable.multi_subs ?_ (hB := this)
    intro A hA
    have ⟨A', hA'⟩ :_ := (Set.mem_image _ _ _).mp <| hΓ hA
    rw [←hA'.2]
    rw [←Theory.equivalent_derivable <| Theory.godelGentzen_equiv A']
    exact Theory.Derivable.ax' (by grind)

end NJ

end PL

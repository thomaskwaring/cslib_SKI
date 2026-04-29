/-
Copyright (c) 2026 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
module

public import Cslib.Logics.Propositional.Semantics.Heyting
public import Mathlib.Order.UpperLower.CompleteLattice
public import Cslib.ForMathlib.Order.PrimeSeparator
public import Mathlib.Data.Sum.Order

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

lemma KripkeModel.forces_monotone {c c' : Worlds} (h : c ≤ c') (A : Proposition Atom)
    (hc : c ⊨[C] A) : c' ⊨[C] A := by
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

theorem Theory.Derivation.forces [DecidableEq Atom] {Γ : Ctx Atom} {B : Proposition Atom}
    {c : Worlds} (hT : ∀ A ∈ T, c ⊨[C] A) (hΓ : ∀ A ∈ Γ, c ⊨[C] A) (D : T.Derivation Γ B) :
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

open Order Ideal PFilter Valuation OrderDual

variable {H : Type*} [GeneralizedHeytingAlgebra H] (v : Valuation Atom H) {F : PFilter H}
  (hF : F.IsPrime)

def KripkeModel.ofHeyting : KripkeModel Atom {F : PFilter H // F.IsPrime} where
  Forces' F x := v x ∈ F.val
  forces'_monotone _ _ hle _ h := hle h

lemma KripkeModel.ofHyeting_forces_iff (A : Proposition Atom) :
    (⟨F, hF⟩ ⊨[ofHeyting v] A) ↔ v⟦A⟧ ∈ F := by
  induction A generalizing F with
  | atom x => simp [ofHeyting, Forces, pInterpret]
  | and A B aih bih =>
    simp_rw [Forces, pInterpret, aih, bih]
    exact F.inf_mem_iff.symm
  | or A B aih bih =>
    simp_rw [Forces, pInterpret, aih, bih]
    refine ⟨?_, hF.mem_or_mem⟩
    rintro (hA | hB)
    · exact F.mem_of_le le_sup_left hA
    · exact F.mem_of_le le_sup_right hB
  | impl A B aih bih =>
    constructor <;> intro h
    · by_contra hc
      have hdisj : Disjoint ((F ⊔ PFilter.principal (v⟦A⟧) : PFilter H) : Set H)
          (Ideal.principal (v⟦B⟧)) := by
        rw [Set.disjoint_iff]
        intro x ⟨hx, hx'⟩
        obtain ⟨f, hf, hle⟩ : ∃ f ∈ F, f ⊓ v⟦A⟧ ≤ x := by
          rwa [PFilter.mem_coe, Lattice.mem_pFilter_sup_principal] at hx
        rw [Ideal.mem_coe, Ideal.mem_principal] at hx'
        refine hc <| F.mem_of_le ?_ hf
        rw [pInterpret, le_himp_iff]
        exact hle.trans hx'
      obtain ⟨G, hG, hle, hdisj⟩ := DistribLattice.prime_filter_of_disjoint_filter_ideal hdisj
      have hGA : ⟨G, hG⟩ ⊨[ofHeyting v] A := by
        rw [aih hG]
        refine PFilter.mem_of_mem_of_le ?_ hle
        simp only [PFilter.mem_sup, PFilter.mem_principal]
        use F.nonempty.some, F.nonempty.some_mem, v⟦A⟧, le_refl _, inf_le_right
      have hGB : ⟨G, hG⟩ ⊨[ofHeyting v] B := h _ (le_sup_left.trans hle) hGA
      absurd hdisj
      rw [Set.not_disjoint_iff]
      use v⟦B⟧, (bih hG).mp hGB, Ideal.mem_principal_self
    · intro ⟨G, hG⟩ hle hA
      rw [aih hG] at hA
      rw [bih hG]
      exact G.mem_of_le (x := v⟦A⟧ ⊓ v⟦A → B⟧) (by simp [pInterpret]) <| inf_mem_iff.mpr ⟨hA, hle h⟩

theorem KripkeModel.ofHeyting_spec (A : Proposition Atom) :
    (v ⊨ A) ↔ (∀ F hF, ⟨F, hF⟩ ⊨[ofHeyting v] A) := by
  simp_rw [PValid, KripkeModel.ofHyeting_forces_iff]
  constructor
  · intro h F hF
    exact h ▸ F.top_mem
  · intro h
    contrapose! h
    have : Disjoint ((⊥ : PFilter H) : Set H) (Ideal.principal (v⟦A⟧)) := by
      rw [Set.disjoint_iff]
      intro x ⟨hx, hx'⟩
      rw [PFilter.mem_coe, ←PFilter.principal_bot, PFilter.mem_principal, top_le_iff] at hx
      rw [Ideal.mem_coe, Ideal.mem_principal, hx, top_le_iff] at hx'
      exact h hx'
    obtain ⟨G, hG, -, hdisj⟩ := DistribLattice.prime_filter_of_disjoint_filter_ideal this
    use G, hG
    contrapose hdisj with hmem
    simp_rw [Set.not_disjoint_iff, Ideal.mem_coe]
    use v⟦A⟧, hmem, Ideal.mem_principal_self

theorem KripkeModel.complete [Bot Atom] [DecidableEq Atom] {B : Proposition Atom} :
    DerivableIn T B ↔ ∀ {Worlds : Type u} [PartialOrder Worlds] (C : KripkeModel Atom Worlds)
      (c : Worlds), (∀ A ∈ T, c ⊨[C] A) → c ⊨[C] B := by
  constructor
  · intro ⟨D⟩ _ _ C c hC
    exact D.forces hC (fun _ => by simp)
  · intro h
    rw [←T.lindenbaum_complete, KripkeModel.ofHeyting_spec]
    intro F hF
    apply h
    intro A hA
    exact KripkeModel.ofHeyting_spec _ _ |>.mp (T.tValid_canonicalV A hA) F hF

def KripkeModel.restrict (C : KripkeModel Atom Worlds) (s : Set Worlds) : KripkeModel Atom s where
  Forces' x := C.Forces' x
  forces'_monotone _ _ h := C.forces'_monotone h

lemma KripkeModel.restrict_forces_iff_of_isUpperSet {s : Set Worlds} (hs : IsUpperSet s) {c : s}
    {A : Proposition Atom} : (c ⊨[C.restrict s] A) ↔ c ⊨[C] A := by
  induction A generalizing c
  case impl A B aih bih =>
    simp_rw [Forces, aih, bih]
    exact ⟨fun h c' hc hA => h ⟨c', hs hc c.property⟩ hc hA, fun h c' hc => h c' hc⟩
  all_goals simp_all [Forces, restrict]

def KripkeModel.disj {W W' : Type*} [PartialOrder W] [PartialOrder W'] (C : KripkeModel Atom W)
    (C' : KripkeModel Atom W') : KripkeModel Atom (WithBot <| W ⊕ W') where
  Forces' c x := c.recBotCoe False fun c' => c'.rec (C.Forces' · x) (C'.Forces' · x)
  forces'_monotone c c' hc x := by
    cases c with
    | bot => simp
    | coe c =>
      cases c' with
      | bot => exact False.elim (WithBot.not_coe_le_bot c <| hc)
      | coe c' =>
        rw [WithBot.coe_le_coe] at hc
        cases hc with
        | inl h => apply C.forces'_monotone; assumption
        | inr h => apply C'.forces'_monotone; assumption

lemma KripkeModel.disj_inl_forces {W W' : Type*} [PartialOrder W] [PartialOrder W']
    (C : KripkeModel Atom W) (C' : KripkeModel Atom W') {c : W} {A : Proposition Atom} :
    (↑(Sum.inl c : (W ⊕ W')) ⊨[C.disj C'] A) ↔ c ⊨[C] A := by
  induction A generalizing c <;> simp_all [Forces, disj]

lemma KripkeModel.disj_inr_forces {W W' : Type*} [PartialOrder W] [PartialOrder W']
    (C : KripkeModel Atom W) (C' : KripkeModel Atom W') {c' : W'} {A : Proposition Atom} :
    (↑(Sum.inr c' : (W ⊕ W')) ⊨[C.disj C'] A) ↔ c' ⊨[C'] A := by
  induction A generalizing c' <;> simp_all [Forces, disj]

theorem MPL.disjunction_property [Bot Atom] [DecidableEq Atom] {A B : Proposition Atom}
    (h : DerivableIn (MPL (Atom := Atom)) (A ∨ B)) :
    DerivableIn (MPL (Atom := Atom)) A ∨ DerivableIn (MPL (Atom := Atom)) B := by
  simp_rw [KripkeModel.complete] at h ⊢
  contrapose! h
  obtain ⟨⟨WA, _, CA, cA, hCA, hcA⟩, ⟨WB, _, CB, cB, hCB, hcB⟩⟩ := h
  use WithBot ((Set.Ici cA) ⊕ (Set.Ici cB)), inferInstance,
    KripkeModel.disj (CA.restrict _) (CB.restrict _), ⊥
  refine ⟨fun _ => False.elim, ?_⟩
  rintro (h | h)
  · apply hcA
    rw [←KripkeModel.restrict_forces_iff_of_isUpperSet (c := ⟨cA, le_rfl⟩) (isUpperSet_Ici cA),
      ←(CA.restrict (Set.Ici cA)).disj_inl_forces (CB.restrict (Set.Ici cB))]
    exact KripkeModel.forces_monotone bot_le _ h
  · apply hcB
    rw [←KripkeModel.restrict_forces_iff_of_isUpperSet (c := ⟨cB, le_rfl⟩) (isUpperSet_Ici cB),
      ←(CA.restrict (Set.Ici cA)).disj_inr_forces (CB.restrict (Set.Ici cB))]
    exact KripkeModel.forces_monotone bot_le _ h

theorem IPL.disjunction_property [Bot Atom] [DecidableEq Atom] {A B : Proposition Atom}
    (h : DerivableIn (IPL (Atom := Atom)) (A ∨ B)) :
    DerivableIn (IPL (Atom := Atom)) A ∨ DerivableIn (IPL (Atom := Atom)) B := by
  simp_rw [KripkeModel.complete] at h ⊢
  contrapose! h
  obtain ⟨⟨WA, _, CA, cA, hCA, hcA⟩, ⟨WB, _, CB, cB, hCB, hcB⟩⟩ := h
  use WithBot ((Set.Ici cA) ⊕ (Set.Ici cB)), inferInstance,
    KripkeModel.disj (CA.restrict _) (CB.restrict _), ⊥
  constructor
  · rintro _ ⟨A, rfl⟩ c _ hc
    cases c with
    | bot =>
      rw [← Proposition.atom_bot, KripkeModel.Forces] at hc
      simp [KripkeModel.disj] at hc
    | coe c =>
      cases c with
      | inl c =>
        rw [KripkeModel.disj_inl_forces,
          KripkeModel.restrict_forces_iff_of_isUpperSet (isUpperSet_Ici cA)] at hc ⊢
        exact hCA (⊥ → A) ⟨A, rfl⟩ c c.property hc
      | inr c =>
        rw [KripkeModel.disj_inr_forces,
          KripkeModel.restrict_forces_iff_of_isUpperSet (isUpperSet_Ici cB)] at hc ⊢
        exact hCB (⊥ → A) ⟨A, rfl⟩ c c.property hc
  · rintro (h | h)
    · apply hcA
      rw [←KripkeModel.restrict_forces_iff_of_isUpperSet (c := ⟨cA, le_rfl⟩) (isUpperSet_Ici cA),
        ←(CA.restrict (Set.Ici cA)).disj_inl_forces (CB.restrict (Set.Ici cB))]
      exact KripkeModel.forces_monotone bot_le _ h
    · apply hcB
      rw [←KripkeModel.restrict_forces_iff_of_isUpperSet (c := ⟨cB, le_rfl⟩) (isUpperSet_Ici cB),
        ←(CA.restrict (Set.Ici cA)).disj_inr_forces (CB.restrict (Set.Ici cB))]
      exact KripkeModel.forces_monotone bot_le _ h

end Cslib.Logic.PL

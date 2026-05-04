/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
module

public import Cslib.Logics.Propositional.NaturalDeduction.Basic
public import Mathlib.Order.Antisymmetrization
public import Mathlib.Tactic.TFAE

/-! # Results and constructions for propositional theories -/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Proposition Theory InferenceSystem DerivableIn Derivation IsIntuitionistic IsClassical

variable {Atom : Type u} [DecidableEq Atom]

namespace Theory

/-! ### Ordering -/

protected structure Embedding (T T' : Theory Atom) where
  derOfMem {A : Proposition Atom} (hA : A ∈ T) : T'⇓A

open Embedding

variable {T T' T'' : Theory Atom}

def Derivation.mapEmbedding (emb : T.Embedding T') {Γ : Ctx Atom} {A : Proposition Atom} :
    T.Derivation Γ A → T'.Derivation Γ A
  | ax hA => (emb.derOfMem hA).weak_ctx (Finset.empty_subset Γ)
  | ass hA => ass hA
  | andI D E => andI (D.mapEmbedding emb) (E.mapEmbedding emb)
  | andE₁ D => andE₁ (D.mapEmbedding emb)
  | andE₂ D => andE₂ (D.mapEmbedding emb)
  | orI₁ D => orI₁ (D.mapEmbedding emb)
  | orI₂ D => orI₂ (D.mapEmbedding emb)
  | orE D DA DB => orE (D.mapEmbedding emb) (DA.mapEmbedding emb) (DB.mapEmbedding emb)
  | implI _ D => implI _ (D.mapEmbedding emb)
  | implE D E => implE (D.mapEmbedding emb) (E.mapEmbedding emb)

namespace Embedding

def ofSubset (h : T ⊆ T') : T.Embedding T' where
  derOfMem hA := ax (h hA)

protected def refl : T.Embedding T where
  derOfMem hA := ax hA

protected def comp (emb : T.Embedding T') (emb' : T'.Embedding T'') : T.Embedding T'' where
  derOfMem hA := (emb.derOfMem hA).mapEmbedding emb'

end Embedding

def WeakerThan (T T' : Theory Atom) : Prop := Nonempty (T.Embedding T')

instance : LE (Theory Atom) where
  le := Theory.WeakerThan

def WeakerThan.mk' (h : ∀ {A}, A ∈ T → DerivableIn T' A) : T ≤ T' := ⟨⟨fun hA => h hA⟩⟩

noncomputable def WeakerThan.embedding (h : T ≤ T') : T.Embedding T' := h.some

lemma WeakerThan.of_subset (h : T ⊆ T') : T ≤ T' := ⟨Embedding.ofSubset h⟩

noncomputable def Derivation.mapLE (h : T ≤ T') {Γ : Ctx Atom} {A : Proposition Atom}
    (D : T⇓(Γ ⊢ A)) : T'⇓(Γ ⊢ A) := D.mapEmbedding h.embedding

namespace WeakerThan

instance instIsPreorderWeakerThan : IsPreorder (Theory Atom) Theory.WeakerThan where
  refl _ := ⟨Embedding.refl⟩
  trans _ _ _ h h' := ⟨h.embedding.comp h'.embedding⟩

instance instPreorderTheory : Preorder (Theory Atom) where
  lt T T' := T ≤ T' ∧ ¬(T' ≤ T)
  le_refl T := ⟨Embedding.refl⟩
  le_trans _ _ _ h h' := ⟨h.embedding.comp h'.embedding⟩

lemma iff_forall_mem_derivableIn :
    T ≤ T' ↔ ∀ {A : Proposition Atom}, A ∈ T → DerivableIn T' A :=
  ⟨fun h _ hA => ⟨h.embedding.derOfMem hA⟩, .mk'⟩

lemma iff_forall_derivableIn_of_derivableIn :
    T ≤ T' ↔ ∀ A : Proposition Atom, DerivableIn T A → DerivableIn T' A := by
  constructor
  · intro h A hA
    exact ⟨hA.toDerivation.mapLE h⟩
  · intro h
    refine ⟨⟨?_⟩⟩
    intro A hA
    exact (h A ⟨ax hA⟩).toDerivation

instance : Bot (Theory Atom) := ⟨MPL Atom⟩

instance : OrderBot (Theory Atom) where
  bot_le _ := WeakerThan.of_subset <| Set.empty_subset ..

instance : Top (Theory Atom) := ⟨Set.univ⟩

instance : OrderTop (Theory Atom) where
  le_top _ := WeakerThan.of_subset <| Set.subset_univ ..

end WeakerThan

open WeakerThan

instance theorySetoid : Setoid (Theory Atom) := AntisymmRel.setoid (Theory Atom) WeakerThan

lemma setoid_def : T ≈ T' ↔ T ≤ T' ∧ T' ≤ T := Iff.rfl

lemma equiv_iff_forall_mem_derivableIn :
    T ≈ T' ↔ (∀ A ∈ T, DerivableIn T' A) ∧ (∀ A ∈ T', DerivableIn T A) := by
  simp_rw [setoid_def, iff_forall_mem_derivableIn]

lemma equiv_iff_forall_derivableIn_derivableIn :
    T ≈ T' ↔ ∀ A : Proposition Atom, DerivableIn T A ↔ DerivableIn T' A := by
  constructor
  · intro ⟨h, h'⟩ A
    exact ⟨iff_forall_derivableIn_of_derivableIn.mp h A,
      iff_forall_derivableIn_of_derivableIn.mp h' A⟩
  · intro h
    refine ⟨iff_forall_derivableIn_of_derivableIn.mpr fun A => (h A).mp,
      iff_forall_derivableIn_of_derivableIn.mpr fun A => (h A).mpr⟩


/-! ### Saturated theories -/

def Saturated (T : Theory Atom) : Prop := ∀ A : Proposition Atom, DerivableIn T A → A ∈ T

def saturation (T : Theory Atom) : Theory Atom := {A : Proposition Atom | DerivableIn T A }

lemma subset_saturation_self : T ⊆ T.saturation := fun _ hA => ⟨ax hA⟩

@[simp]
lemma saturation_le_iff : T.saturation ≤ T' ↔ T ≤ T' := by
   rw [iff_forall_mem_derivableIn, iff_forall_derivableIn_of_derivableIn]
   simp [saturation]

lemma saturation_le_self : T.saturation ≤ T := saturation_le_iff.mpr le_rfl

lemma Saturated.iff_saturation_subset : T.saturation ⊆ T ↔ T.Saturated := Set.setOf_subset

lemma le_iff_saturation_subset_saturation : T ≤ T' ↔ T.saturation ⊆ T'.saturation := by
  rw [iff_forall_derivableIn_of_derivableIn]
  rfl

lemma equiv_iff_saturation_eq : T ≈ T' ↔ T.saturation = T'.saturation := by
  simp_rw [setoid_def, le_iff_saturation_subset_saturation, Set.Subset.antisymm_iff]

lemma saturation_saturated : T.saturation.Saturated := by
  rw [←Saturated.iff_saturation_subset, ←le_iff_saturation_subset_saturation]
  exact saturation_le_self

lemma Saturated.TFAE : [T.Saturated, T.saturation ⊆ T, T.saturation = T].TFAE := by
  tfae_have 2 ↔ 1 := Saturated.iff_saturation_subset
  tfae_have 2 ↔ 3 := by simp [Set.Subset.antisymm_iff, T.subset_saturation_self]
  tfae_finish

@[simp]
lemma saturation_idem : T.saturation.saturation = T.saturation :=
  Saturated.TFAE.out 0 2 |>.mp saturation_saturated

lemma isInconsistent_iff_saturation_eq_top : IsInconsistent Atom T ↔ T.saturation = ⊤ := by
  simp [isInconsistent_iff, saturation, Top.top, Set.eq_univ_iff_forall]

/-! ### Intuitionistic and classical theories-/

variable [Bot Atom] {T T' T'' : Theory Atom}

instance instIsIntuitionisticIPL : IsIntuitionistic Atom (IPL Atom) where
  efq A := ax (efq_mem_ipl A)

noncomputable def IsIntuitionistic.embeddingIPL [IsIntuitionistic Atom T] :
    (IPL Atom).Embedding T where
  derOfMem hA := by rw [←Classical.choose_spec hA]; exact efq _

@[implicit_reducible]
def instIsIntuitionisticOfEmbedding [IsIntuitionistic Atom T]
    (emb : T.Embedding T') : IsIntuitionistic Atom T' where
  efq A := (efq A : T⇓(⊥ → A)).mapEmbedding emb

instance instIsIntuitionisticOfEmbeddingIPL (emb : (IPL Atom).Embedding T') :
  IsIntuitionistic Atom T' where
    efq A := (efq A : (IPL Atom)⇓(⊥ → A)).mapEmbedding emb

def IsIntuitionistic.efqCtx [IsIntuitionistic Atom T] (Γ : Ctx Atom) (A : Proposition Atom)
    : T⇓(Γ ⊢ ⊥ → A) := (efq A : T⇓(⊥ → A)).weak_ctx (Finset.empty_subset Γ)

/-- Efq as a derived rule. -/
def IsIntuitionistic.efqRule [IsIntuitionistic Atom T] (Γ : Ctx Atom) (A : Proposition Atom)
    (D : T⇓(Γ ⊢ ⊥)) : T⇓(Γ ⊢ A) :=
  implE (A := ⊥) (efqCtx Γ A) D

/-- Prove any proposition from contradictory hypotheses. -/
def IsIntuitionistic.contra [IsIntuitionistic Atom T] {Γ : Ctx Atom} (A B : Proposition Atom)
    (hΓ : A ∈ Γ) (hΓ' : (¬A) ∈ Γ) : T⇓(Γ ⊢ B) :=
  efqRule Γ B <| implE (ass hΓ') (ass hΓ)

lemma IsIntuitionistic.isInconsistent_iff_derivableIn_bot [IsIntuitionistic Atom T] :
    IsInconsistent Atom T ↔ DerivableIn T (⊥ : Proposition Atom) := by
  refine ⟨fun h => h.forall_derivableIn ⊥, ?_⟩
  intro ⟨D⟩
  constructor
  intro A
  exact ⟨efqRule ∅ A D⟩

instance instIsClassicalCPL : IsClassical Atom (CPL Atom) where
  dne A := ax (dne_mem_cpl A)

noncomputable def IsClassical.embeddingCPL [IsClassical Atom T] : (CPL Atom).Embedding T where
  derOfMem hA := by rw [←Classical.choose_spec hA]; exact dne _

@[implicit_reducible]
def instIsClassicalOfEmbedding [IsClassical Atom T] (emb : T.Embedding T') :
    IsClassical Atom T' where
  dne A := (dne A : T⇓(¬¬A → A)).mapEmbedding emb

instance instIsClassicalOfEmbeddingCPL (emb : (CPL Atom).Embedding T') :
    IsClassical Atom T' where
  dne A := (dne A : (CPL Atom)⇓(¬¬A → A)).mapEmbedding emb

def IsClassical.byContra [IsClassical Atom T] {Γ : Ctx Atom} {A : Proposition Atom}
    (D : T⇓(insert (¬ A) Γ ⊢ ⊥)) : T⇓(Γ ⊢ A) :=
  implE (A := ¬¬A) ((dne A : T⇓(¬¬A → A)) |>.weak_ctx <| Finset.empty_subset ..) D.implI

instance instIsIntuitionisticOfIsClassical [IsClassical Atom T] : IsIntuitionistic Atom T where
  efq A := implI _ <| byContra <| ass (by grind)

def IsClassical.lem [IsClassical Atom T] (A : Proposition Atom) : T⇓(A ∨ ¬ A) := by
  apply byContra
  apply implE (ass <| Finset.mem_insert_self ..)
  apply orI₂; apply implI
  apply implE (A := A ∨ ¬ A) (ass <| by grind)
  exact orI₁ <| ass <| Finset.mem_insert_self ..

def IsClassical.byCases [IsClassical Atom T] {Γ : Ctx Atom} {A B : Proposition Atom}
    (D : T⇓(insert A Γ ⊢ B)) (D' : T⇓(insert (¬ A) Γ ⊢ B)) : T⇓(Γ ⊢ B) :=
  (lem A |>.weak_ctx <| Finset.empty_subset Γ).orE D D'

def IsClassical.pierce [IsClassical Atom T] (A B : Proposition Atom) : T⇓(((A → B) → A) → A) := by
  apply implI; apply byContra
  apply implE (ass <| Finset.mem_insert_self ..)
  apply implE (A := A → B) (ass <| by grind); apply implI
  apply contra A B <;> grind

/-- The axiom system consisting of instances of LEM. -/
def LEM (Atom : Type u) [Bot Atom] : Theory Atom := {A ∨ ¬ A | A : Proposition Atom}

omit [DecidableEq Atom] in
lemma lem_mem_lem (A : Proposition Atom) : (A ∨ ¬ A) ∈ LEM Atom := ⟨A, rfl⟩

instance instIsClassicalLEM : IsClassical Atom (LEM Atom ∪ IPL Atom : Theory Atom) where
  dne A := by
    have : IsIntuitionistic Atom (LEM Atom ∪ IPL Atom : Theory Atom) :=
      instIsIntuitionisticOfEmbedding (.ofSubset Set.subset_union_right)
    apply implI
    apply orE (ax <| Set.mem_union_left _ <| lem_mem_lem A)
    · exact ass (Finset.mem_insert_self A _)
    · apply contra (¬A) A <;> grind

theorem CPL_equiv_LEM_union_IPL : CPL Atom ≈ (LEM Atom ∪ IPL Atom : Theory Atom) := by
  rw [equiv_iff_forall_mem_derivableIn]
  constructor
  · intro _ hA
    exact ⟨(ax hA).mapEmbedding embeddingCPL⟩
  · rintro _ (⟨A, rfl⟩ | ⟨A, rfl⟩)
    · exact ⟨lem A⟩
    · exact ⟨efq A⟩

/-- The axiom system consisting of instances of Pierce's law. -/
def Pierce (Atom : Type u) : Theory Atom :=
  {((A → B) → A) → A | (A : Proposition Atom) (B : Proposition Atom)}

omit [DecidableEq Atom] [Bot Atom] in
lemma pierce_mem_pierce (A B : Proposition Atom) : (((A → B) → A) → A) ∈ Pierce Atom := ⟨A, B, rfl⟩

instance instIsClassicalPierce : IsClassical Atom (Pierce Atom ∪ IPL Atom : Theory Atom) where
  dne A := by
    have : IsIntuitionistic Atom (Pierce Atom ∪ IPL Atom : Theory Atom) :=
      instIsIntuitionisticOfEmbedding (.ofSubset Set.subset_union_right)
    apply implI
    apply implE (A := (A → ⊥) → A) (ax <| Set.mem_union_left _ <| pierce_mem_pierce A ⊥)
    apply implI
    apply contra (¬ A) A <;> grind

theorem CPL_equiv_pierce_union_IPL : CPL Atom ≈ (Pierce Atom ∪ IPL Atom : Theory Atom) := by
  rw [equiv_iff_forall_mem_derivableIn]
  constructor
  · intro _ hA
    exact ⟨(ax hA).mapEmbedding embeddingCPL⟩
  · rintro _ (⟨A, B, rfl⟩ | ⟨A, rfl⟩)
    · exact ⟨pierce A B⟩
    · exact ⟨efq A⟩

end Cslib.Logic.PL.Theory

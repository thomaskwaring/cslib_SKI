/-
Copyright (c) 2026 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
module

public import Cslib.Logics.Propositional.NaturalDeduction.Basic
public import Cslib.Foundations.Logic.LogicalEquivalence
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Order.Antisymmetrization

@[expose] public section

namespace Cslib.Logic.PL

variable {Atom : Type u} [DecidableEq Atom] {T : Theory Atom}

open Theory Derivation InferenceSystem Proposition

/-! ### Shift hypotheses between the context and the theory. -/

/-- Move the axioms used in a derivation `D` to the context, obtaining a derivation in minimal
logic. -/
def Theory.Derivation.collectAxs {Γ : Ctx Atom} {B : Proposition Atom} :
    T.Derivation Γ B →
      Σ Δ : {Δ : Ctx Atom // (Δ : Theory Atom) ⊆ T}, MPL.Derivation (Γ ∪ Δ) B
  | @ax _ _ _ _ B _ => ⟨⟨{B}, by grind⟩, ass <| by grind⟩
  | ass _ => ⟨⟨∅, by grind⟩, ass <| by grind⟩
  | conjI D E =>
    let ⟨Δ₁, D'⟩ := collectAxs D
    let ⟨Δ₂, E'⟩ := collectAxs E
    ⟨⟨Δ₁ ∪ Δ₂, by grind⟩, conjI (D'.weak_ctx <| by grind) (E'.weak_ctx <| by grind)⟩
  | conjE₁ D => let ⟨Δ, D'⟩ := collectAxs D; ⟨Δ, conjE₁ D'⟩
  | conjE₂ D => let ⟨Δ, D'⟩ := collectAxs D; ⟨Δ, conjE₂ D'⟩
  | disjI₁ D => let ⟨Δ, D'⟩ := collectAxs D; ⟨Δ, disjI₁ D'⟩
  | disjI₂ D => let ⟨Δ, D'⟩ := collectAxs D; ⟨Δ, disjI₂ D'⟩
  | disjE D E₁ E₂ =>
    let ⟨Δ, D'⟩ := collectAxs D
    let ⟨Δ₁, E₁'⟩ := collectAxs E₁
    let ⟨Δ₂, E₂'⟩ := collectAxs E₂
    ⟨⟨Δ ∪ Δ₁ ∪ Δ₂, by grind⟩,
      disjE (D'.weak_ctx <| by grind) (E₁'.weak_ctx <| by grind) (E₂'.weak_ctx <| by grind)⟩
  | implI Γ D =>
    let ⟨Δ, D'⟩ := collectAxs D; ⟨Δ, implI (Γ ∪ Δ) (D'.weak_ctx <| by grind)⟩
  | implE D E =>
    let ⟨Δ₁, D'⟩ := collectAxs D
    let ⟨Δ₂, E'⟩ := collectAxs E
    ⟨⟨Δ₁ ∪ Δ₂, by grind⟩, implE (D'.weak_ctx <| by grind) (E'.weak_ctx <| by grind)⟩

theorem DerivableIn.collect_axs {Γ : Ctx Atom} {B : Proposition Atom} :
    DerivableIn T (Γ ⊢ B) →
      ∃ Δ : Ctx Atom, (DerivableIn (MPL (Atom := Atom)) ((Γ ∪ Δ) ⊢ B)) ∧ ((Δ : Theory Atom) ⊆ T)
  | ⟨D⟩ => let ⟨Δ, D'⟩ := D.collectAxs; ⟨Δ, ⟨⟨D'⟩, by grind⟩⟩

/-- Move some axioms from the theory to the context. -/
def Theory.Derivation.axsToAss {T : Theory Atom} {Γ Δ : Ctx Atom} {B : Proposition Atom} :
    (T ∪ Δ).Derivation Γ B → T.Derivation (Γ ∪ Δ) B
  | @ax _ _ _ _ B _ => by
    by_cases B ∈ Δ
    case pos => exact ass <| by grind
    case neg => exact ax <| by grind
  | ass _ => ass <| by grind
  | conjI D E => conjI (axsToAss D) (axsToAss E)
  | conjE₁ D => conjE₁ (axsToAss D)
  | conjE₂ D => conjE₂ (axsToAss D)
  | disjI₁ D => disjI₁ (axsToAss D)
  | disjI₂ D => disjI₂ (axsToAss D)
  | @disjE _ _ _ _ A' B C D E₁ E₂ => by
    refine disjE (axsToAss D) ?_ ?_
    · let E₁' : _ := axsToAss (B := C) E₁
      rw [Finset.insert_union] at E₁'
      assumption
    · let E₂' : _ := axsToAss (B := C) E₂
      rw [Finset.insert_union] at E₂'
      assumption
  | @implI _ _ _ A' B _ D => by
    let D' : _ := axsToAss (B := B) D
    rw [Finset.insert_union] at D'
    exact implI _ D'
  | implE D E => implE (axsToAss D) (axsToAss E)

theorem DerivableIn.axs_to_ass {T : Theory Atom} {Γ Δ : Ctx Atom} {B : Proposition Atom} :
    DerivableIn (T ∪ Δ : Theory Atom) (Γ ⊢ B) → DerivableIn T ((Γ ∪ Δ) ⊢ B)
  | ⟨D⟩ => ⟨D.axsToAss⟩

/-- Remove some assumptions by moving them to the theory. -/
def Theory.Derivation.assToAxs' {T : Theory Atom} {Γ Δ : Ctx Atom} {B : Proposition Atom} :
    T.Derivation Γ B → (T ∪ Δ).Derivation (Γ \ Δ) B
  | @ass _ _ _ _ B _ => by
    by_cases B ∈ Δ
    case pos =>
      exact ax <| by grind
    case neg =>
      exact ass <| by grind
  | ax _ => ax <| by grind
  | conjI D E => conjI (assToAxs' D) (assToAxs' E)
  | conjE₁ D => conjE₁ (assToAxs' D)
  | conjE₂ D => conjE₂ (assToAxs' D)
  | disjI₁ D => disjI₁ (assToAxs' D)
  | disjI₂ D => disjI₂ (assToAxs' D)
  | @disjE _ _ _ _ A' B C D E₁ E₂ =>
    disjE (assToAxs' D)
      ((assToAxs' (Δ := Δ) (B := C) E₁).weak_ctx <| by grind)
      ((assToAxs' (Δ := Δ) (B := C) E₂).weak_ctx <| by grind)
  | @implI _ _ _ A' B _ D =>
    implI _ ((assToAxs' (Δ := Δ) (B := B) D).weak_ctx <| by grind)
  | implE D E => implE (assToAxs' D) (assToAxs' E)

/-- Remove dependence on some assumptions by adding them to the theory. -/
def Theory.Derivation.assToAxs {T : Theory Atom} {Γ Δ : Ctx Atom} {B : Proposition Atom}
    (D : T⇓((Γ ∪ Δ) ⊢ B)) : (T ∪ Δ : Theory Atom)⇓(Γ ⊢ B) := (assToAxs' D).weak_ctx <| by grind

theorem DerivableIn.ass_to_axs {T : Theory Atom} {Γ Δ : Ctx Atom} {B : Proposition Atom} :
    DerivableIn T ((Γ ∪ Δ) ⊢ B) → DerivableIn (T ∪ Δ : Theory Atom) (Γ ⊢ B)
  | ⟨D⟩ => ⟨D.assToAxs⟩

theorem Derivable.union_iff_derivable_union {Γ Δ : Ctx Atom} {B : Proposition Atom} :
    DerivableIn T ((Γ ∪ Δ) ⊢ B) ↔ DerivableIn (T ∪ Δ : Theory Atom) (Γ ⊢ B) :=
  ⟨DerivableIn.ass_to_axs, DerivableIn.axs_to_ass⟩

namespace Theory

/-! ### Operations on and properties of theories

TODO: if we generalised the derivability relation to be a typeclass, these definitions and results
ought also to generalise.
-/

/-- A theory is inconsistent if it proves every proposition. -/
abbrev Inconsistent (T : Theory Atom) : Prop := ∀ A : Proposition Atom, DerivableIn T A

/-- A theory is consistent if it is not inconsistent. -/
abbrev Consistent (T : Theory Atom) : Prop := ¬ Inconsistent T

/-- An intuitionistic theory is inconisistent iff it is so in the more familiar way (if it proves
falsum). -/
theorem inconsistent_iff [Bot Atom] [IsIntuitionistic T] :
    Inconsistent T ↔ DerivableIn T (⊥ : Proposition Atom) := by
  constructor
  · exact (· ⊥)
  · intro ⟨D⟩ A
    exact ⟨implE (A := ⊥) (ax <| by grind) D⟩

/-! The **compactness theorem**: a theory is inconsistent iff it has a finite inconsistent
subtheory. -/
theorem compactness [Bot Atom] [IsIntuitionistic T] :
    Inconsistent T ↔ ∃ T' : Theory Atom,
      Inconsistent (IPL ∪ T' : Theory Atom) ∧ T'.Finite ∧ T' ⊆ T := by
  constructor
  · rw [inconsistent_iff]
    intro ⟨D⟩
    let ⟨Γ, D⟩ := D.collectAxs
    refine ⟨Γ, ?_, Set.toFinite .., by grind⟩
    have : IsIntuitionistic (IPL ∪ (Γ : Theory Atom)) := by grind
    rw [inconsistent_iff]
    exact ⟨(assToAxs D).weak_theory <| by grind⟩
  · intro ⟨T', h, _⟩
    have : IsIntuitionistic (IPL ∪ T') := by grind
    rw [inconsistent_iff] at h ⊢
    exact DerivableIn.weak_theory (by grind) h

/-- Proof-relevant ordering on theories. -/
protected def Embedding (T T' : Theory Atom) := ∀ A ∈ T, T'⇓A

/-- A theory `T` is weaker than `T'` if all its axioms are `T'`-derivable. -/
def WeakerThan (T T' : Theory Atom) : Prop :=
  ∀ A ∈ T, DerivableIn T' A

instance instLETheory : LE (Theory Atom) where
  le := WeakerThan

lemma Embedding.le {T T' : Theory Atom} (emb : T.Embedding T') : T ≤ T' :=
  fun A hA => ⟨emb A hA⟩

lemma nonempty_embedding_iff_le {T T' : Theory Atom} :
    Nonempty (T.Embedding T') ↔ T ≤ T' where
  mp h := Embedding.le h.some
  mpr h := ⟨fun A hA => h A hA |>.some⟩

/-- Embedding induced by an inclusion. -/
def Embedding.ofSubset {T T' : Theory Atom} (h : T ⊆ T') : T.Embedding T' :=
  fun _ hA => ax (h hA)

lemma le_of_subset {T T' : Theory Atom} (h : T ⊆ T') : T ≤ T' :=
  nonempty_embedding_iff_le.mp ⟨.ofSubset h⟩

end Theory

/-- Replace appeals to axioms in `T` by `T'`-derivations. -/
def Theory.Derivation.mapEmbedding {T T' : Theory Atom} {Γ : Ctx Atom}
    {A : Proposition Atom} (h : T.Embedding T') : T.Derivation Γ A → T'.Derivation Γ A
  | ax hB => h _ hB |>.weak_ctx Γ.empty_subset
  | ass hB => ass hB
  | conjI D E => conjI (D.mapEmbedding h) (E.mapEmbedding h)
  | conjE₁ D => conjE₁ (D.mapEmbedding h)
  | conjE₂ D => conjE₂ (D.mapEmbedding h)
  | disjI₁ D => disjI₁ (D.mapEmbedding h)
  | disjI₂ D => disjI₂ (D.mapEmbedding h)
  | disjE D E E' => disjE (D.mapEmbedding h) (E.mapEmbedding h) (E'.mapEmbedding h)
  | implI _ D => implI _ (D.mapEmbedding h)
  | implE D E => implE (D.mapEmbedding h) (E.mapEmbedding h)

/-- A theory embeds into itself. -/
def Theory.Embedding.id (T : Theory Atom) : T.Embedding T := fun _ => ax

/-- Compose embeddings. -/
def Theory.Embedding.comp {T T' T'' : Theory Atom} (emb : T.Embedding T')
    (emb' : T'.Embedding T'') : T.Embedding T'' := fun A hA => (emb A hA).mapEmbedding emb'

theorem DerivableIn.of_le {T T' : Theory Atom} (hle : T ≤ T') {Γ : Ctx Atom}
    {A : Proposition Atom} (h : DerivableIn T (Γ ⊢ A)) : DerivableIn T' (Γ ⊢ A) :=
  ⟨h.some.mapEmbedding (nonempty_embedding_iff_le.mpr hle).some⟩

/-- `T ≤ T'` is in fact equivalent to the stronger condition in the conclusion of
`Derivable.of_le`. -/
theorem Theory.LE_iff_derivableIn_of_derivableIn {T T' : Theory Atom} :
    T ≤ T' ↔ ∀ {Γ : Ctx Atom} {A : Proposition Atom},
      DerivableIn T (Γ ⊢ A) → DerivableIn T' (Γ ⊢ A) :=
  ⟨DerivableIn.of_le, fun h _ hA => h ⟨ax hA⟩⟩

instance instPreorderTheory : Preorder (Theory Atom) where
  lt T T' := T.WeakerThan T' ∧ ¬ T'.WeakerThan T
  le_refl _ _ h := ⟨ax h⟩
  le_trans _ _ _ h h' A hA := DerivableIn.of_le h' (h A hA)

/-- Minimal logic embeds into every theory. -/
def Theory.Embedding.mpl (T : Theory Atom) : MPL.Embedding T := .ofSubset T.empty_subset

theorem isBot_mpl : IsBot (MPL (Atom := Atom)) := fun T => (Embedding.mpl T).le

theorem isTop_of_inconsistent (h : T.Inconsistent) : IsTop T :=
  fun _ A _ => h A

theorem ipl_le_cpl [Bot Atom] : IPL (Atom := Atom) ≤ CPL := by
  rintro _ ⟨A, rfl⟩
  constructor
  apply implI
  apply implE (A := ¬¬A) (ax <| by grind)
  exact implI _ <| ass <| by grind

/-- A derivation of ex falso quodlibet in an intuitionistic theory. -/
def Theory.efq [Bot Atom] [IsIntuitionistic T] (A : Proposition Atom) : T⇓(⊥ → A) :=
  ax <| by grind

def Theory.efqHyp [Bot Atom] [IsIntuitionistic T] {Γ : Ctx Atom} (h : ⊥ ∈ Γ)
    (A : Proposition Atom) : T⇓(Γ ⊢ A) :=
  implE ((T.efq A).weak_ctx <| Finset.empty_subset Γ) (ass h)

/-- `T` derives efq if `IPL` embeds into `T`. -/
def Theory.Embedding.efqOfIPL [Bot Atom] (emb : IPL.Embedding T) (A : Proposition Atom) :
    T⇓(⊥ → A) := (IPL.efq A).mapEmbedding emb

def Theory.efqOfIPLHyp [Bot Atom] (emb : IPL.Embedding T) {Γ : Ctx Atom} (h : ⊥ ∈ Γ)
    (A : Proposition Atom) : T⇓(Γ ⊢ A) :=
  (IPL.efqHyp h A).mapEmbedding emb

def Theory.absurd [Bot Atom] [IsIntuitionistic T] {Γ : Ctx Atom} (A B : Proposition Atom)
    (hA : A ∈ Γ) (hA' : (¬ A) ∈ Γ) : T⇓(Γ ⊢ B) :=
  implE (A := ⊥) (ax <| by grind) (implE (A := A) (ass <| by grind) (ass <| by grind))

def Theory.absurdOfIPL [Bot Atom] (emb : IPL.Embedding T) {Γ : Ctx Atom} (A B : Proposition Atom)
    (hA : A ∈ Γ) (hA' : (¬ A) ∈ Γ) : T⇓(Γ ⊢ B) := (IPL.absurd A B hA hA').mapEmbedding emb

/-- A derivation of double-negation elimination in a classical theory. -/
def Theory.dne [Bot Atom] [IsClassical T] (A : Proposition Atom) : T⇓(¬¬A → A) :=
  ax <| by grind

/-- `T` derives dne if `CPL` embeds into `T`. -/
def Theory.Embedding.dneOfCPL [Bot Atom] (emb : CPL.Embedding T) (A : Proposition Atom) :
  T⇓(¬¬A → A) := (CPL.dne A).mapEmbedding emb

/-- A derivation of the law of excluded middle in a classical theory. -/
def Theory.lem [Bot Atom] [IsClassical T] (A : Proposition Atom) : T⇓(A ∨ ¬ A) := by
  apply implE (A := ¬¬(A ∨ ¬A)) (ax <| by grind)
  apply implI
  apply implE (A := A ∨ ¬A) (ass <| by grind)
  apply disjI₂
  apply implI
  refine implE (A := A) ?_ (ass <| by grind)
  apply implI
  apply implE (A := A ∨ ¬A) (ass <| by grind)
  apply disjI₁
  exact ass <| by grind

/-- `T` derives lem if `CPL` embeds into `T`. -/
def Theory.Embedding.lemOfCPL [Bot Atom] (emb : CPL.Embedding T) (A : Proposition Atom) :
    T⇓(A ∨ ¬ A) := (CPL.lem A).mapEmbedding emb

/-- A derivation of Pierce's law in a classical theory. -/
def Theory.pierce [Bot Atom] [IsClassical T] (A B : Proposition Atom) :
    T⇓(((A → B) → A) → A) := by
  apply implI
  apply disjE (lem A |>.weak_ctx (by grind)) (ass <| by grind)
  apply implE (A := A → B) (ass <| by grind)
  apply implI
  apply implE (A := ¬¬B) (ax <| by grind)
  apply implI
  apply implE (A := A) <;> exact ass (by grind)

/-- `T` derives Pierce's law if `CPL` embeds into `T`. -/
def Theory.Embedding.pierceOfCPL [Bot Atom] (emb : CPL.Embedding T)
    (A B : Proposition Atom) : T⇓(((A → B) → A) → A) := (CPL.pierce A B).mapEmbedding emb

/-- A theory is saturated if every provable proposition is in fact an axiom. -/
def Theory.Saturated (T : Theory Atom) : Prop :=
  ∀ (A : Proposition Atom), DerivableIn T A → A ∈ T

/-- The saturation of a theory is the collection of all provable propositions. -/
def Theory.saturate (T : Theory Atom) : Theory Atom := {A : Proposition Atom | DerivableIn T A}

/-- `T` embeds into its saturation. -/
def Theory.embeddingSaturate (T : Theory Atom) : T.Embedding T.saturate :=
  fun _ hA => ax ⟨ax hA⟩

theorem Theory.le_saturation (T : Theory Atom) : T ≤ T.saturate :=
  nonempty_embedding_iff_le.mp ⟨T.embeddingSaturate⟩

theorem Theory.saturation_le (T : Theory Atom) : T.saturate ≤ T :=
  fun _ hA => hA

/-- Saturating a theory does not affect derivability. -/
theorem DerivableIn.iff_derivableIn_saturate {T : Theory Atom} {Γ : Ctx Atom}
    {A : Proposition Atom} : DerivableIn T.saturate (Γ ⊢ A) ↔ DerivableIn T (Γ ⊢ A) :=
  ⟨DerivableIn.of_le T.saturation_le, DerivableIn.of_le T.le_saturation⟩

/-- The `WeakerThan` relation corresponds exactly to inclusion between saturations. -/
theorem Theory.weakerThan_iff {T T' : Theory Atom} : T ≤ T' ↔ T.saturate ⊆ T'.saturate := by
  constructor <;> intro h
  · intro A
    exact DerivableIn.of_le h
  · intro A hA
    exact h ⟨ax hA⟩

/-- The saturation of a theory deserves its name. -/
theorem Theory.saturate_saturated (T : Theory Atom) : T.saturate.Saturated := by
  intro B hB
  exact DerivableIn.iff_derivableIn_saturate.mp hB

theorem Theory.saturated_iff (T : Theory Atom) : T.Saturated ↔ T = T.saturate := by
  constructor <;> intro h
  · ext A
    constructor
    · exact fun hA => ⟨ax hA⟩
    · exact h A
  · rw [h]
    exact T.saturate_saturated

theorem Theory.saturate_idem (T : Theory Atom) : T.saturate.saturate = T.saturate :=
  T.saturate.saturated_iff.mp T.saturate_saturated |>.symm

/-! ### Equivalent axiomatizations of classical logic -/

namespace Theory

instance : Setoid (Theory Atom) := AntisymmRel.setoid (Theory Atom) (· ≤ ·)

def LEM [Bot Atom] : Theory Atom := {A ∨ ¬ A | A : Proposition Atom}

def Pierce : Theory Atom := {((A → B) → A) → A | (A : Proposition Atom) (B : Proposition Atom)}

theorem ipl_lem_equiv_cpl [Bot Atom] : (IPL (Atom := Atom)) ∪ LEM ≈ CPL where
  left := by
    rintro _ (h | ⟨A, rfl⟩)
    · exact ipl_le_cpl _ h
    · exact ⟨CPL.lem A⟩
  right := by
    rintro _ ⟨A, rfl⟩
    constructor
    apply implI
    apply disjE (A := A) (B := ¬ A)
      (ax <| by apply Set.mem_union_right; exact ⟨A, rfl⟩) (ass <| by grind)
    apply Theory.absurdOfIPL (A := ¬ A) (Embedding.ofSubset Set.subset_union_left)
      <;> grind

theorem ipl_pierce_equiv_cpl [Bot Atom] : (IPL (Atom := Atom)) ∪ Pierce ≈ CPL where
  left := by
    rintro _ (h | ⟨A, B, rfl⟩)
    · exact ipl_le_cpl _ h
    · exact ⟨CPL.pierce A B⟩
  right := by
    rintro _ ⟨A, rfl⟩
    constructor
    apply implI
    apply implE (A := ¬ A → A) (ax <| by apply Set.mem_union_right; exact ⟨A, ⊥, rfl⟩)
    apply implI
    apply Theory.absurdOfIPL (A := ¬ A) (Embedding.ofSubset Set.subset_union_left)
      <;> grind

end Theory

/-! ### Mapping along propositional constructors -/

/-- Apply `and` to a pair of derivations. -/
def Theory.Derivation.andAnd {A A' B B' : Proposition Atom} (DA : T⇓({A} ⊢ A'))
    (DB : T⇓({B} ⊢ B')) : T⇓({A ∧ B} ⊢A' ∧ B') := by
  apply conjI
  · refine Derivation.cut (Γ := {A ∧ B}) (Δ := ∅) ?_ DA
    exact conjE₁ (B := B) <| ass <| by grind
  · refine Derivation.cut (Γ := {A ∧ B}) (Δ := ∅) ?_ DB
    exact conjE₂ (A := A) <| ass <| by grind

/-- Apply `and` to a pair of equivalences. -/
def Theory.equiv.andAnd {A A' B B' : Proposition Atom} (eA : T.equiv A A') (eB : T.equiv B B') :
    T.equiv (A ∧ B) (A' ∧ B') := ⟨eA.mp.andAnd eB.mp, eA.mpr.andAnd eB.mpr⟩

lemma DerivableIn.and_and {A A' B B' : Proposition Atom} (hA : DerivableIn T ({A} ⊢ A'))
    (hB : DerivableIn T ({B} ⊢ B')) : DerivableIn T ({A ∧ B} ⊢ A' ∧ B') := ⟨hA.some.andAnd hB.some⟩

lemma Theory.Equiv.and_and {A A' B B' : Proposition Atom} (hA : A ≡[T] A') (hB : B ≡[T] B') :
    (A ∧ B) ≡[T] (A' ∧ B') := ⟨hA.some.andAnd hB.some⟩

/-- Apply `or` to a pair of derivations. -/
def Theory.Derivation.orOr {A A' B B' : Proposition Atom} (DA : T⇓({A} ⊢ A')) (DB : T⇓({B} ⊢ B')) :
    T⇓({A ∨ B} ⊢ A' ∨ B') := by
  apply disjE (ass <| Finset.mem_singleton_self (A ∨ B))
  · exact disjI₁ <| DA.weak_ctx <| by grind
  · exact disjI₂ <| DB.weak_ctx <| by grind

/-- Apply `or` to a pair of equivalences. -/
def Theory.equiv.orOr {A A' B B' : Proposition Atom} (eA : T.equiv A A') (eB : T.equiv B B') :
    T.equiv (A ∨ B) (A' ∨ B') := ⟨eA.mp.orOr eB.mp, eA.mpr.orOr eB.mpr⟩

lemma DerivableIn.or_or {A A' B B' : Proposition Atom} (hA : DerivableIn T ({A} ⊢ A'))
    (hB : DerivableIn T ({B} ⊢ B')) : DerivableIn T ({A ∨ B} ⊢ A' ∨ B') := ⟨hA.some.orOr hB.some⟩

lemma Theory.Equiv.or_or {A A' B B' : Proposition Atom} (hA : A ≡[T] A') (hB : B ≡[T] B') :
    (A ∨ B) ≡[T] (A' ∨ B') := ⟨hA.some.orOr hB.some⟩

/-- Apply `impl` to a pair of derivations. Note that `· → ·` is contravariant in its first
argument. -/
def Theory.Derivation.implImpl {A A' B B' : Proposition Atom} (DA : T⇓({A} ⊢ A'))
    (DB : T⇓({B} ⊢ B')) : T⇓({A' → B} ⊢ A → B') := by
  apply implI
  refine cut (A := B) (Γ := {A, A' → B}) (Δ := ∅) ?_ DB |>.weak_ctx (by grind)
  exact implE (A := A') (ass <| by grind) (DA.weak_ctx <| by grind)

/-- Apply `impl` to a pair of equivalences. -/
def Theory.equiv.implImpl {A A' B B' : Proposition Atom} (eA : T.equiv A A') (eB : T.equiv B B') :
    T.equiv (A → B) (A' → B') := ⟨eA.mpr.implImpl eB.mp, eA.mp.implImpl eB.mpr⟩

lemma DerivableIn.impl_impl {A A' B B' : Proposition Atom} (hA : DerivableIn T ({A} ⊢ A'))
    (hB : DerivableIn T ({B} ⊢ B')) : DerivableIn T ({A' → B} ⊢ A → B') :=
  ⟨hA.some.implImpl hB.some⟩

lemma Theory.Equiv.impl_impl {A A' B B' : Proposition Atom} (hA : A ≡[T] A') (hB : B ≡[T] B') :
    (A → B) ≡[T] (A' → B') := ⟨hA.some.implImpl hB.some⟩

/-- Apply `not` to a pair of derivations. -/
def Theory.Derivation.modusTollens [Bot Atom] {A B : Proposition Atom} (D : T⇓({A} ⊢ B)) :
    T⇓({¬ B} ⊢ ¬ A) := D.implImpl (ass <| Finset.mem_singleton_self ⊥)

/-- Apply `not` to an equivalence. -/
def Theory.equiv.not [Bot Atom] {A B : Proposition Atom} (e : T.equiv A B) :
    T.equiv (¬ A) (¬ B) := ⟨e.mpr.modusTollens, e.mp.modusTollens⟩

lemma DerivableIn.modus_tollens [Bot Atom] {A B : Proposition Atom} (h : DerivableIn T ({A} ⊢ B)) :
    DerivableIn T ({¬ B} ⊢ ¬ A) := ⟨h.some.modusTollens⟩

def Theory.Equiv.not [Bot Atom] {A B : Proposition Atom} (h : A ≡[T] B) :
    (¬ A) ≡[T] (¬ B) := ⟨h.some.not⟩

/-- Transform a derivation of `B` depending on a hypothesis `A` to a derivation of `¬ A` depending
on `¬ B`. -/
def Theory.Derivation.modusTollensSwap [Bot Atom] {Γ : Ctx Atom} {A B : Proposition Atom}
    (D : T⇓(insert A Γ ⊢ B)) : T⇓(insert (¬ B) Γ ⊢ ¬ A) :=
  implI _ <| implE (A := B) (ass <| by grind) (D.weak_ctx <| by grind)

lemma DerivableIn.modus_tollens_swap [Bot Atom] {Γ : Ctx Atom} {A B : Proposition Atom}
    (h : DerivableIn T (insert A Γ ⊢ B)) : DerivableIn T (insert (¬ B) Γ ⊢ ¬ A) :=
  ⟨h.some.modusTollensSwap⟩

/-- Transform a family of equivalences for each `Atom` into a an equivalence of the
substitutions. -/
def Proposition.mapSubstEquiv {Atom Atom' : Type u} [DecidableEq Atom'] {T : Theory Atom'}
    {f f' : Atom → Proposition Atom'} (h : ∀ x : Atom, T.equiv (f x) (f' x)) :
    (A : Proposition Atom) → T.equiv (A >>= f) (A >>= f')
  | atom x => h x
  | Proposition.and A B => (A.mapSubstEquiv h).andAnd (B.mapSubstEquiv h)
  | Proposition.or A B => (A.mapSubstEquiv h).orOr (B.mapSubstEquiv h)
  | impl A B => (A.mapSubstEquiv h).implImpl (B.mapSubstEquiv h)

lemma Proposition.map_subst_equiv {Atom Atom' : Type u} [DecidableEq Atom'] {T : Theory Atom'}
    {f f' : Atom → Proposition Atom'} (h : ∀ x : Atom, (f x) ≡[T] (f' x)) (A : Proposition Atom) :
    (A >>= f) ≡[T] (A >>= f') := ⟨A.mapSubstEquiv <| fun x => (h x).some⟩

/-! ### Contexts and logical equivalence

We implement context filling as a special case of sustitution, distinguishing an atom as the
"hole". Note that this implies contexts are non-linear, so may have zero, one or more holes.

To define a `LogicalEquivalence` instance using `T.Equiv`, we set `Judgment` to be a pair of
a context `Γ` and proposition `A`, which is valid if `Γ ⊢[T] A` is derivable. Judgement context have
two cases, for whether the hole is in the context or the conclusion.
-/

instance : HasContext (Proposition Atom) where
  Context := Proposition (Option Atom)
  fill c A := c >>= (Option.rec A pure)

instance (T : Theory Atom) : Congruence (Proposition Atom) T.Equiv where
  refl := Theory.Equiv.refl
  symm _ _ := Theory.Equiv.symm
  trans _ _ _ := Theory.Equiv.trans
  elim := by
    intro c A B e
    apply Proposition.map_subst_equiv
    rintro (none | x)
    · exact e
    · exact Theory.Equiv.refl (A := atom x)

/-- Judgmental contexts. -/
inductive JudgementContext (Atom : Type u) where
  /-- A hole in the conclusion: `conc Γ` is the context `Γ ⊢ {}` -/
  | conc : Ctx Atom → JudgementContext Atom
  /-- A hole in the (hypothesis) context: `hyp Γ B` is the context `Γ, {} ⊢ B`. -/
  | hyp : Ctx Atom → Proposition Atom → JudgementContext Atom

/-- Fill the hole in a judgement context. -/
def JudgementContext.fill (c : JudgementContext Atom) (A : Proposition Atom) :
    Ctx Atom × Proposition Atom :=
  match c with
  | conc Γ => ⟨Γ, A⟩
  | hyp Γ B => ⟨insert A Γ, B⟩

instance : HasHContext (Ctx Atom × Proposition Atom) (Proposition Atom) where
  Context := JudgementContext Atom
  fill := JudgementContext.fill

/-- A pair `Γ, A` is valid for a theory `T` if `Γ ⊢[T] A` is derivable. -/
def Theory.Valid (T : Theory Atom) : (Ctx Atom × Proposition Atom) → Prop
  | ⟨Γ, A⟩ => DerivableIn T (Γ ⊢ A)

instance : LogicalEquivalence (Proposition Atom) (Ctx Atom × Proposition Atom) T.Valid where
  eqv := T.Equiv
  eqv_fill_valid h c hA := by
    cases c with
    | conc => exact equiv_iff_equiv_derivableIn.mp h _ |>.mp hA
    | hyp => exact equiv_iff_equiv_derivableIn_hypothesis.mp h _ _ |>.mp hA

/-! ### Monad lemmas -/
instance : LawfulMonad Proposition := by
  apply LawfulMonad.mk'
  · intro _ A
    induction A <;> simp_all [Functor.map, subst]
  · simp [bind, subst]
  · intro _ _ _ A
    induction A <;> simp_all [bind, subst]
  all_goals
    intro _ _ _ _
    rfl

/-! ### Extensions of theories -/

namespace Theory

variable {Atom Atom' Atom'' : Type u} [DecidableEq Atom] [DecidableEq Atom'] [DecidableEq Atom'']

/-- An extension `T'` of a theory `T` generalises `Theory.Embedding` to allow a change of the
atomic language. -/
structure Extension (T : Theory Atom) (T' : Theory Atom') where
  f : Atom → Proposition Atom'
  emb : (T.subst f).Embedding T'

def Embedding.toExtension (T T' : Theory Atom) (e : T.Embedding T') : T.Extension T' where
  f := pure
  emb := show T = T.subst pure by simp [Theory.subst] ▸ e

namespace Extension

variable {T : Theory Atom} {T' : Theory Atom'} {T'' : Theory Atom''}

/-- An extension of theories is conservative if it doesn't add any new theorems, when restricted
to the domain language `Atom`. -/
def IsConservative [DecidableEq Atom] [DecidableEq Atom'] : Extension T T' → Prop
  | ⟨f, _⟩ => ∀ (A : Proposition Atom), DerivableIn T' (A >>= f) → DerivableIn T A

omit [DecidableEq Atom] in
lemma subst_le (e : T.Extension T') : T.subst e.f ≤ T' := e.emb.le

/-- Map a derivation into the extended theory. -/
def mapDerivation (e : T.Extension T') {Γ : Ctx Atom} {A : Proposition Atom} (D : T⇓(Γ ⊢ A)) :
    T'⇓(Γ.subst e.f ⊢ A >>= e.f) :=
  (D.substAtom e.f).mapEmbedding e.emb

def mapEquiv (e : T.Extension T') {A B : Proposition Atom} (eqv : T.equiv A B) :
    T'.equiv (A >>= e.f) (B >>= e.f) := ⟨e.mapDerivation eqv.mp, e.mapDerivation eqv.mpr⟩

lemma derivableIn_subst (e : T.Extension T') {Γ : Ctx Atom} {A : Proposition Atom}
    (h : DerivableIn T (Γ ⊢ A)) : DerivableIn T' (Γ.subst e.f ⊢ A >>= e.f) :=
  ⟨e.mapDerivation h.some⟩

lemma equiv_subst (e : T.Extension T') {A B : Proposition Atom} (eqv : A ≡[T] B) :
    (A >>= e.f) ≡[T'] (B >>= e.f) := ⟨e.mapEquiv eqv.some⟩

protected def id : T.Extension T where
  f := pure
  emb := by
    simp_rw [Theory.subst, bind_pure, Set.image_id']
    exact Theory.Embedding.id T

protected noncomputable def comp (e : T.Extension T') (e' : T'.Extension T'') :
    T.Extension T'' where
  f x := e.f x >>= e'.f -- this is `f := e.f >=> e'.f` but Bind.kleisliRight has no API :/
  emb := by
    refine Theory.Embedding.comp ?_ e'.emb
    intro A hA
    obtain ⟨hT, hA'⟩ := Classical.choose_spec hA
    have D : (T'.subst e'.f)⇓((Classical.choose hA >>= e.f) >>= e'.f) :=
      e.emb (Classical.choose hA >>= e.f) ⟨_, hT, rfl⟩ |>.substAtom e'.f
    simpa [hA'] using D

end Cslib.Logic.PL.Theory.Extension

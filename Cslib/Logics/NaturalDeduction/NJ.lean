/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.SDiff

/-!
# Gentzen's NJ - natural deduction for intuitionistic propositional logic
-/

universe u

variable {Atom : Type u} [DecidableEq Atom]

namespace IPL

/-- Propositions. We view negation as a defined connective ~A := A → ⊥ -/
inductive Proposition (Atom : Type u) : Type u where
  /-- Propositional atoms -/
  | atom (x : Atom)
  /-- Falsum -/
  | bot
  /-- Conjunction -/
  | conj (a b : Proposition Atom)
  /-- Disjunction -/
  | disj (a b : Proposition Atom)
  /-- Implication -/
  | impl (a b : Proposition Atom)
deriving DecidableEq, BEq


namespace NJ

open Proposition

/-- Contexts are finsets of propositions. -/
abbrev Ctx (Atom) := Finset (Proposition Atom)

/-- Sequents {A₁, ..., Aₙ} ⊢ B -/
abbrev Sequent (Atom) := Ctx Atom × Proposition Atom

/-- A derivation of {A₁, ..., Aₙ} ⊢ B demonstrates B using (undischarged) assumptions among Aᵢ. -/
inductive Derivation : Sequent Atom → Type _ where
  /-- Axiom (or assumption) -/
  | ax (Γ : Ctx Atom) (A : Proposition Atom) : Derivation ⟨insert A Γ, A⟩
  /-- Falsum elimination (ex falso quodlibet) -/
  | botE {Γ : Ctx Atom} (A : Proposition Atom) : Derivation ⟨Γ, bot⟩ → Derivation ⟨Γ, A⟩
  /-- Conjunction introduction -/
  | conjI {Γ : Ctx Atom} {A B : Proposition Atom} :
      Derivation ⟨Γ, A⟩ → Derivation ⟨Γ, B⟩ → Derivation ⟨Γ, conj A B⟩
  /-- Conjunction elimination left -/
  | conjE₁ {Γ : Ctx Atom} {A B : Proposition Atom} : Derivation ⟨Γ, conj A B⟩ → Derivation ⟨Γ, A⟩
  /-- Conjunction elimination right -/
  | conjE₂ {Γ : Ctx Atom} {A B : Proposition Atom} : Derivation ⟨Γ, conj A B⟩ → Derivation ⟨Γ, B⟩
  /-- Disjunction introduction left -/
  | disjI₁ {Γ : Ctx Atom} {A B : Proposition Atom} : Derivation ⟨Γ, A⟩ → Derivation ⟨Γ, disj A B⟩
  /-- Disjunction introduction right -/
  | disjI₂ {Γ : Ctx Atom} {A B : Proposition Atom} : Derivation ⟨Γ, B⟩ → Derivation ⟨Γ, disj A B⟩
  /-- Disjunction elimination -/
  | disjE {Γ : Ctx Atom} {A B C : Proposition Atom} : Derivation ⟨Γ, disj A B⟩ →
      Derivation ⟨insert A Γ, C⟩ → Derivation ⟨insert B Γ, C⟩ → Derivation ⟨Γ, C⟩
  /-- Implication introduction -/
  | implI {A B : Proposition Atom} (Γ : Ctx Atom) :
      Derivation ⟨insert A Γ, B⟩ → Derivation ⟨Γ, impl A B⟩
  /-- Implication elimination -/
  | implE {Γ : Ctx Atom} {A B : Proposition Atom} :
      Derivation ⟨Γ, impl A B⟩ → Derivation ⟨Γ, A⟩ → Derivation ⟨Γ, B⟩

def Derivable (S : Sequent Atom) := Nonempty (Derivation S)

def Proposition.PDerivable (A : Proposition Atom) := Nonempty (Derivation ⟨∅,A⟩)

def Proposition.equiv (A B : Proposition Atom) := Derivation ⟨{A},B⟩ × Derivation ⟨{B},A⟩
def Proposition.Equiv (A B : Proposition Atom) := Derivable ⟨{A},B⟩ ∧ Derivable ⟨{B},A⟩

open Derivation

def Derivation.size {S : Sequent Atom} : Derivation S → Nat
  | ax _ _ => 1
  | botE _ D => D.size + 1
  | conjI D D' => D.size + D'.size + 1
  | conjE₁ D => D.size + 1
  | conjE₂ D => D.size + 1
  | disjI₁ D => D.size + 1
  | disjI₂ D => D.size + 1
  | disjE D D' D'' => D.size + D'.size + D''.size + 1
  | implI _ D => D.size + 1
  | implE D D' => D.size + D'.size + 1

def Proposition.top : Proposition Atom := impl bot bot

def derivationTop : Derivation (Atom := Atom) ⟨∅,Proposition.top⟩ := by
  apply implI
  exact ax (Atom := Atom) ∅ bot

theorem top_derivable : Proposition.PDerivable (Atom := Atom) Proposition.top := ⟨derivationTop⟩

/-! ### Common proof patterns -/

def Derivation.ax' {Γ : Ctx Atom} {A : Proposition Atom} (h : A ∈ Γ) : Derivation ⟨Γ,A⟩ := by
  have : Γ = insert A Γ := by grind
  rw [this]
  apply ax

/-- Weakening is a derived rule. -/
def Derivation.weak {Γ : Ctx Atom} {A : Proposition Atom} (Δ : Ctx Atom)
    (D : Derivation ⟨Γ, A⟩) : Derivation ⟨Γ ∪ Δ, A⟩ := by
  match D with
  | ax Γ A =>
    rw [Finset.insert_union A Γ Δ]
    exact ax (Γ ∪ Δ) A
  | botE A D => exact botE A <| D.weak Δ
  | conjI D D' => exact conjI (D.weak Δ) (D'.weak Δ)
  | conjE₁ D => exact conjE₁ <| D.weak Δ
  | conjE₂ D => exact conjE₂ <| D.weak Δ
  | disjI₁ D => exact disjI₁ <| D.weak Δ
  | disjI₂ D => exact disjI₂ <| D.weak Δ
  | @disjE _ _ _ A B _ D D' D'' =>
    apply disjE (D.weak Δ)
    · rw [←Finset.insert_union A Γ Δ]; exact D'.weak Δ
    · rw [←Finset.insert_union B Γ Δ]; exact D''.weak Δ
  | @implI _ _ A B Γ D =>
    apply implI
    rw [←Finset.insert_union A Γ Δ]; exact D.weak Δ
  | implE D D' => exact implE (D.weak Δ) (D'.weak Δ)

theorem Derivable.weak {Γ : Ctx Atom} {A : Proposition Atom} (Δ : Ctx Atom)
    (h : Derivable ⟨Γ, A⟩) : Derivable ⟨Γ ∪ Δ, A⟩ := by
  let ⟨D⟩ := h
  exact ⟨D.weak Δ⟩

def Derivation.weak' {Γ Δ : Ctx Atom} {A : Proposition Atom} (h : Γ ⊆ Δ) (D : Derivation ⟨Γ, A⟩) :
    Derivation ⟨Δ, A⟩ := Finset.union_sdiff_of_subset h ▸ D.weak (Δ \ Γ)

theorem Derivable.weak' {Γ Δ : Ctx Atom} {A : Proposition Atom} (h_ext : Γ ⊆ Δ)
    (h : Derivable ⟨Γ, A⟩) : Derivable ⟨Δ, A⟩ := by
  let ⟨D⟩ := h
  exact ⟨D.weak' h_ext⟩

/-- Substitution -/
def Derivation.subs {Γ Δ : Ctx Atom} {A B : Proposition Atom}
    (D : Derivation ⟨Γ, B⟩) (E : Derivation ⟨Δ, A⟩) : Derivation ⟨(Γ \ {A}) ∪ Δ, B⟩ := by
  match D with
  | ax _ _ =>
    by_cases B = A
    case pos h =>
      rw [h, Finset.union_comm]
      exact E.weak _
    case neg h =>
      have : B ∉ ({A} : Finset (Proposition Atom)) := Finset.notMem_singleton.mpr h
      rw [Finset.insert_sdiff_of_notMem (h := this)]
      exact (ax _ B).weak _
  | botE _ D => exact botE B <| D.subs E
  | conjI D D' => exact conjI (D.subs E) (D'.subs E)
  | conjE₁ D => exact conjE₁ <| D.subs E
  | conjE₂ D => exact conjE₂ <| D.subs E
  | disjI₁ D => exact disjI₁ <| D.subs E
  | disjI₂ D => exact disjI₂ <| D.subs E
  | @disjE _ _ _ C C' B D D' D'' =>
    apply disjE (D.subs E)
    · by_cases C = A
      case pos h =>
        rw [h] at D' ⊢
        have : insert A ((Γ \ {A}) ∪ Δ) = (insert A Γ) ∪ Δ := by grind
        rw [this]
        exact D'.weak _
      case neg h =>
        have : insert C ((Γ \ {A}) ∪ Δ) = ((insert C Γ) \ {A}) ∪ Δ := by grind
        rw [this]
        exact D'.subs E
    · by_cases C' = A
      case pos h =>
        rw [h] at D'' ⊢
        have : insert A ((Γ \ {A}) ∪ Δ) = (insert A Γ) ∪ Δ := by grind
        rw [this]
        exact D''.weak _
      case neg h =>
        have : insert C' ((Γ \ {A}) ∪ Δ) = ((insert C' Γ) \ {A}) ∪ Δ := by grind
        rw [this]
        exact D''.subs E
  | @implI _ _ A' B _ D =>
    apply implI
    by_cases A' = A
    case pos h =>
      rw [h] at D ⊢
      have : insert A (Γ \ {A} ∪ Δ) = insert A Γ ∪ Δ := by grind
      rw [this]
      exact D.weak Δ
    case neg h =>
      have : insert A' ((Γ \ {A}) ∪ Δ) = ((insert A' Γ) \ {A}) ∪ Δ := by grind
      rw [this]
      exact D.subs E
  | implE D D' => exact implE (D.subs E) (D'.subs E)

theorem Derivable.subs {Γ Δ : Ctx Atom} {A B : Proposition Atom}
    (h₁ : Derivable ⟨Γ, B⟩) (h₂ : Derivable ⟨Δ, A⟩) : Derivable ⟨(Γ \ {A}) ∪ Δ, B⟩ :=
  let ⟨D⟩ := h₁; let ⟨E⟩ := h₂; ⟨D.subs E⟩

def Derivation.subs' {Γ : Ctx Atom} {A B : Proposition Atom}
    (D : Derivation ⟨{A}, B⟩) (E : Derivation ⟨Γ, A⟩) : Derivation ⟨Γ, B⟩ := by
  have : Γ = ({A} \ {A}) ∪ Γ := by grind
  rw [this]
  exact D.subs E

theorem Derivable.subs' {Γ : Ctx Atom} {A B : Proposition Atom}
    (h : Derivable ⟨{A}, B⟩) (h' : Derivable ⟨Γ, A⟩) : Derivable ⟨Γ, B⟩ :=
  let ⟨D⟩ := h; let ⟨E⟩ := h'; ⟨D.subs' E⟩

/-! ### Properties of NJ-equivalence -/

theorem Proposition.derivable_iff (A : Proposition Atom) :
    PDerivable A ↔ Proposition.Equiv A top := by
  constructor <;> intro h
  · constructor
    · exact ⟨derivationTop.weak' (Δ := {A}) (by grind)⟩
    · let ⟨D⟩ := h
      exact ⟨D.weak' (Δ := {Proposition.top}) (by grind)⟩
  · let ⟨D⟩ := h.2
    exact ⟨D.subs' derivationTop⟩

def mapEquivConclusion (Γ : Ctx Atom) {A B : Proposition Atom} (e : Proposition.equiv A B) :
    Derivation ⟨Γ, A⟩ → Derivation ⟨Γ, B⟩ := e.1.subs'

theorem equivalent_derivability (Γ : Ctx Atom) {A B : Proposition Atom} (h : Proposition.Equiv A B)
    : Derivable ⟨Γ, A⟩ ↔ Derivable ⟨Γ, B⟩ := ⟨h.1.subs', h.2.subs'⟩

def mapEquivHypothesis (Γ : Ctx Atom) {A B : Proposition Atom} (e : Proposition.equiv A B)
    (C : Proposition Atom) (D : Derivation ⟨insert A Γ, C⟩) : Derivation ⟨insert B Γ, C⟩ := by
  have : insert B Γ = (insert A Γ \ {A}) ∪ (insert B Γ) := by grind
  rw [this]
  refine D.subs ?_
  exact e.2.weak' (by grind)

theorem equivalent_hypotheses (Γ : Ctx Atom) {A B : Proposition Atom} (h : Proposition.Equiv A B)
    (C : Proposition Atom) : Derivable ⟨insert A Γ, C⟩ ↔ Derivable ⟨insert B Γ, C⟩ := by
  let ⟨⟨D⟩, ⟨D'⟩⟩ := h
  constructor
  · intro ⟨DA⟩
    have : insert B Γ = (insert A Γ \ {A}) ∪ (insert B Γ) := by grind
    rw [this]
    refine ⟨DA.subs ?_⟩
    exact D'.weak' (by grind)
  · intro ⟨DB⟩
    have : insert A Γ = (insert B Γ \ {B}) ∪ (insert A Γ) := by grind
    rw [this]
    refine ⟨DB.subs ?_⟩
    exact D.weak' (by grind)

def reflEquiv (A : Proposition Atom) : Proposition.equiv A A :=
  let D : Derivation ⟨{A},A⟩ := ax' <| by grind;
  ⟨D,D⟩

def commEquiv {A B : Proposition Atom} (e : Proposition.equiv A B) : Proposition.equiv B A :=
  ⟨e.2, e.1⟩

def transEquiv {A B C : Proposition Atom} (e : Proposition.Equiv A B) (e' : Proposition.Equiv B C) :
    Proposition.Equiv A C := ⟨e'.1.subs' e.1, e.2.subs' e'.2⟩

theorem equivalent_refl (A : Proposition Atom) : Proposition.Equiv A A := by
  have : Derivable ⟨{A},A⟩ := ⟨ax' <| by grind⟩
  grind [Proposition.Equiv]

theorem equivalent_comm {A B : Proposition Atom} :
    Proposition.Equiv A B → Proposition.Equiv B A := by grind [Proposition.Equiv]

theorem equivalent_trans {A B C : Proposition Atom} :
    Proposition.Equiv A B → Proposition.Equiv B C → Proposition.Equiv A C := by
  grind [Proposition.Equiv, Derivable.subs']

theorem equivalent_equivalence : Equivalence (Proposition.Equiv (Atom := Atom)) :=
  ⟨equivalent_refl, equivalent_comm, equivalent_trans⟩

protected def propositionSetoid : Setoid (Proposition Atom) :=
  ⟨Proposition.Equiv, equivalent_equivalence⟩

/-!
### Negation theorems

The following are valid in minimal logic, so we use `impl (-) C` over `~(-) := impl (-) bot`.
-/

/-- Double negation introduction -/
def Derivation.dni {A B : Proposition Atom} : Derivation ⟨{A},impl (impl A B) B⟩ := by
  apply implI (A := A.impl B)
  apply implE (A := A) <;> apply ax' (by grind)

theorem Derivable.dni {A B : Proposition Atom} : Derivable ⟨{A},impl (impl A B) B⟩ :=
  ⟨Derivation.dni⟩

def Derivation.dni' {Γ : Ctx Atom} {A B : Proposition Atom} (D : Derivation ⟨Γ, A⟩) :
    Derivation ⟨Γ, impl (impl A B) B⟩ := Derivation.dni.subs' D

theorem Derivable.dni' {Γ : Ctx Atom} {A B : Proposition Atom} (h : Derivable ⟨Γ, A⟩) :
    Derivable ⟨Γ, impl (impl A B) B⟩ := let ⟨D⟩ := h; ⟨D.dni'⟩

def Derivation.notNotLEM {A B : Proposition Atom} :
    Derivation ⟨∅, (A.disj <| impl A B).impl B |>.impl B⟩ := by
  apply implI
  rw [insert_empty_eq]
  apply implE (A := A.disj (A.impl B)) (ax' <| by grind)
  apply disjI₂
  apply implI
  apply implE (A := A.disj (A.impl B)) (ax' <| by grind)
  apply disjI₁
  apply ax' <| by grind

theorem Derivable.not_not_lem {A B : Proposition Atom} :
    Derivable ⟨∅, (A.disj <| impl A B).impl B |>.impl B⟩ := ⟨Derivation.notNotLEM⟩

/-- Triple negation elimination -/
def Derivation.tne {A B : Proposition Atom} :
    Derivation ⟨{((A.impl B).impl B).impl B}, A.impl B⟩ := by
  apply implI
  apply implE (A := (A.impl B).impl B) (ax' <| by grind)
  exact Derivation.dni.weak' (Γ := {A}) (by grind)

theorem Derivable.tne {A B : Proposition Atom} :
    Derivable ⟨{((A.impl B).impl B).impl B}, A.impl B⟩ := ⟨Derivation.tne⟩

def tneEquiv {A B : Proposition Atom} :
    Proposition.equiv (A.impl B) (((A.impl B).impl B).impl B) := ⟨Derivation.dni, Derivation.tne⟩

theorem tne_equivalent {A B : Proposition Atom} :
    Proposition.Equiv (A.impl B) (((A.impl B).impl B).impl B) := ⟨Derivable.dni, Derivable.tne⟩

/-- Modus tollens -/
def Derivation.modusTollens {A B : Proposition Atom} (C : Proposition Atom)
    (D : Derivation ⟨{A}, B⟩) : Derivation ⟨{B.impl C}, A.impl C⟩ := by
  apply implI
  apply implE (A := B)
  · apply ax' (by grind)
  · have : ({A, B.impl C} : Ctx Atom) = ({B} \ {B}) ∪ {A, B.impl C} := by grind
    rw [this]
    apply Derivation.subs
    · apply ax' (by grind)
    · exact D.weak {B.impl C}

theorem Derivable.modus_tollens {A B : Proposition Atom} (C : Proposition Atom)
    (h : Derivable ⟨{A}, B⟩) : Derivable ⟨{B.impl C}, A.impl C⟩ := let ⟨D⟩ := h; ⟨D.modusTollens C⟩

def Derivation.modusTollens' {Γ : Ctx Atom} {A B : Proposition Atom} (C : Proposition Atom)
    (D : Derivation ⟨insert A Γ, B⟩) : Derivation ⟨insert (B.impl C) Γ, A.impl C⟩ := by
  apply implI
  apply implE (A := B)
  · exact ax' (by grind)
  · exact D.weak' (h := by grind)

theorem Derivable.modus_tollens' {Γ : Ctx Atom} {A B : Proposition Atom} (C : Proposition Atom)
    (h : Derivable ⟨insert A Γ, B⟩) : Derivable ⟨insert (B.impl C) Γ, A.impl C⟩ :=
  let ⟨D⟩ := h; ⟨D.modusTollens' C⟩

/-!
### De Morgan laws

The following are valid in minimal logic, so we use `impl (-) C` over `~(-) := impl (-) bot`.
-/

def disjImpOfConjImps {A B C : Proposition Atom} :
    Derivation ⟨{conj (impl A C) (impl B C)}, impl (disj A B) C⟩ := by
  apply implI
  apply disjE (A := A) (B := B)
  · apply ax
  · apply implE (A := A)
    · apply conjE₁ (B := B.impl C)
      apply ax' (by grind)
    · apply ax
  · apply implE (A := B)
    · apply conjE₂ (A := A.impl C)
      apply ax' (by grind)
    · apply ax

theorem disj_imp_of_conj_imps {A B C : Proposition Atom} :
    Derivable ⟨{conj (impl A C) (impl B C)}, impl (disj A B) C⟩ := ⟨disjImpOfConjImps⟩

def conjImpsOfDisjImp {A B C : Proposition Atom} :
    Derivation ⟨{impl (disj A B) C}, conj (impl A C) (impl B C)⟩ := by
  apply conjI
  · apply implI
    apply implE (A := A.disj B)
    · apply ax' (by grind)
    · apply disjI₁
      apply ax
  · apply implI
    apply implE (A := A.disj B)
    · apply ax' (by grind)
    · apply disjI₂
      apply ax

theorem conj_imps_of_disj_imp {A B C : Proposition Atom} :
    Derivable ⟨{impl (disj A B) C}, conj (impl A C) (impl B C)⟩ := ⟨conjImpsOfDisjImp⟩

def disjImpConjImpsEquiv {A B C : Proposition Atom} :
    Proposition.equiv (impl (disj A B) C) (conj (impl A C) (impl B C)) :=
  ⟨conjImpsOfDisjImp, disjImpOfConjImps⟩

theorem disj_imp_conj_imps_equivalent {A B C : Proposition Atom} :
    Proposition.Equiv (impl (disj A B) C) (conj (impl A C) (impl B C)) :=
  ⟨conj_imps_of_disj_imp, disj_imp_of_conj_imps⟩

def conjImpOfDisjImps {A B C : Proposition Atom} :
    Derivation ⟨{disj (impl A C) (impl B C)}, impl (conj A B) C⟩ := by
  apply implI
  apply disjE (A := A.impl C) (B := B.impl C)
  · apply ax' (by grind)
  · apply implE (A := A)
    · apply ax
    · apply conjE₁ (B := B)
      apply ax' (by grind)
  · apply implE (A := B)
    · apply ax
    · apply conjE₂ (A := A)
      apply ax' (by grind)

theorem conj_imp_of_disj_imps {A B C : Proposition Atom} :
    Derivable ⟨{disj (impl A C) (impl B C)}, impl (conj A B) C⟩ := ⟨conjImpOfDisjImps⟩

end NJ

end IPL

/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
module

public import Cslib.Logics.Propositional.NaturalDeduction.Basic
public import Mathlib.Order.WithBot

/-! # Intuitionistic PL

This file introduces intuitionistic propositions (having a primitive falsum), and derivations
(including the "falsum elimination" rule ex falso quodlibet). These definitions match the existing
encodings of intuitionistic logic in minimal logic as follows:
- `propEquiv : Proposition (WithBot Atom) ≃ IProposition Atom` : intuitionistic propositions can be
  recovered by adjoining a bottom element to the atom type.
- `ITheory.IDerivation.toDerivation` : every intuitionistic derivation can be turned into a minimal
  one by adding efq to the collection of axioms.
- `Theory.Derivation.toIDerivation` : any minimal derivation in the "intuitionistic completion" of
  a theory (obtained by adding a bottom element and efq) can be turned into an intuitionistic
  derivation.
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Proposition Theory Derivation InferenceSystem DerivableIn

variable {Atom : Type u} [DecidableEq Atom]

inductive IProposition (Atom : Type u) : Type u where
  | atom (x : Atom) : IProposition Atom
  | or (A B : IProposition Atom) : IProposition Atom
  | and (A B : IProposition Atom) : IProposition Atom
  | impl (A B : IProposition Atom) : IProposition Atom
  | bot : IProposition Atom
  deriving DecidableEq

open IProposition

instance : Bot (IProposition Atom) := ⟨.bot⟩

/-- We view negation as a defined connective ~A := A → ⊥ -/
abbrev IProposition.neg [Bot Atom] : IProposition Atom → IProposition Atom :=
  (IProposition.impl · ⊥)

/-- A fixed choice of a derivable Iproposition (of course any two are equivalent). -/
abbrev IProposition.top : IProposition Atom := impl ⊥ ⊥

instance instTopIProposition : Top (IProposition Atom) := ⟨.top⟩

scoped infix:36 " ∧ " => IProposition.and
scoped infix:35 " ∨ " => IProposition.or
scoped infix:30 " → " => IProposition.impl
scoped prefix:40 " ¬ " => IProposition.neg

/-- Contexts are finsets of propositions. -/
abbrev ICtx (Atom) := Finset (IProposition Atom)

/-- Theories are sets of propositions. -/
abbrev ITheory (Atom) := Set (IProposition Atom)

open IProposition

/-- An intuitionistic `T`-derivation of {A₁, ..., Aₙ} ⊢ B demonstrates B using (undischarged)
assumptions among Aᵢ, possibly appealing to axioms from `T`. This adds ex falso quodlibet to
`T`.Derivation. -/
inductive ITheory.IDerivation {T : ITheory Atom} : ICtx Atom → IProposition Atom → Type u where
  /-- Axiom -/
  | ax {Γ : ICtx Atom} {A : IProposition Atom} (_ : A ∈ T) : IDerivation Γ A
  /-- Assumption -/
  | ass {Γ : ICtx Atom} {A : IProposition Atom} (_ : A ∈ Γ) : IDerivation Γ A
  /-- Conjunction introduction -/
  | conjI {Γ : ICtx Atom} {A B : IProposition Atom} :
      IDerivation Γ A → IDerivation Γ B → IDerivation Γ (A ∧ B)
  /-- Conjunction elimination left -/
  | conjE₁ {Γ : ICtx Atom} {A B : IProposition Atom} : IDerivation Γ (A ∧ B) → IDerivation Γ A
  /-- Conjunction elimination right -/
  | conjE₂ {Γ : ICtx Atom} {A B : IProposition Atom} : IDerivation Γ (A ∧ B) → IDerivation Γ B
  /-- Disjunction introduction left -/
  | disjI₁ {Γ : ICtx Atom} {A B : IProposition Atom} : IDerivation Γ A → IDerivation Γ (A ∨ B)
  /-- Disjunction introduction right -/
  | disjI₂ {Γ : ICtx Atom} {A B : IProposition Atom} : IDerivation Γ B → IDerivation Γ (A ∨ B)
  /-- Disjunction elimination -/
  | disjE {Γ : ICtx Atom} {A B C : IProposition Atom} : IDerivation Γ (A ∨ B) →
      IDerivation (insert A Γ) C → IDerivation (insert B Γ) C → IDerivation Γ C
  /-- Implication introduction -/
  | implI {A B : IProposition Atom} (Γ : ICtx Atom) :
      IDerivation (insert A Γ) B → IDerivation Γ (A → B)
  /-- Implication elimination -/
  | implE {Γ : ICtx Atom} {A B : IProposition Atom} :
      IDerivation Γ (A → B) → IDerivation Γ A → IDerivation Γ B
  /-- Ex falso quodlibet. -/
  | efq {Γ : ICtx Atom} (A : IProposition Atom) : IDerivation Γ ⊥ → IDerivation Γ A

open ITheory IDerivation

/-- Minimal to intuitionistic. -/
def Proposition.toIProposition : Proposition (WithBot Atom) → IProposition Atom
  | atom ⊥ => ⊥
  | atom (some x) => .atom x
  | and A B => A.toIProposition ∧ B.toIProposition
  | or A B => A.toIProposition ∨ B.toIProposition
  | impl A B => A.toIProposition → B.toIProposition

/-- Intuitionistic to minimal. -/
def IProposition.toProposition : IProposition Atom → Proposition (WithBot Atom)
  | atom x => .atom x
  | and A B => A.toProposition ∧ B.toProposition
  | or A B => A.toProposition ∨ B.toProposition
  | impl A B => A.toProposition → B.toProposition
  | bot => ⊥

/-- Equivalence of encoded with genuine intuitionistic propositions. -/
def propEquiv : Proposition (WithBot Atom) ≃ IProposition Atom where
  toFun := Proposition.toIProposition
  invFun := IProposition.toProposition
  left_inv A := by
    induction A
    case atom x => cases x <;> rfl
    all_goals simp_all [toIProposition, toProposition]
  right_inv A := by
    induction A
    all_goals simp_all [toIProposition, toProposition]
    rfl

/-- Map contexts along `Proposition.toIProposition`. -/
def Ctx.toICtx : Ctx (WithBot Atom) → ICtx Atom := Finset.image toIProposition

@[simp] lemma Ctx.toICtx_insert (A : Proposition (WithBot Atom)) (Γ : Ctx (WithBot Atom)) :
    (insert A Γ).toICtx = insert A.toIProposition Γ.toICtx := by simp [toICtx]

/-- Map contexts along `IProposition.toProposition`. -/
def ICtx.toCtx : ICtx Atom → Ctx (WithBot Atom) := Finset.image toProposition

@[simp] lemma ICtx.toCtx_insert (A : IProposition Atom) (Γ : ICtx Atom) :
    (insert A Γ).toCtx = insert A.toProposition Γ.toCtx := by simp [toCtx]

/-- Map theories along `Proposition.toIProposition`. -/
def Theory.toITheory (T : Theory Atom) : ITheory Atom :=
  toIProposition ∘ (WithBot.some <$> ·) '' T

/-- Map theories along `IProposition.toProposition`. -/
def ITheory.toTheory (T : ITheory Atom) : Theory (WithBot Atom) :=
  toProposition '' T ∪ IPL (WithBot Atom)

/-- Intuitionistic completion of a theory. -/
def Theory.iCompletion (T : Theory Atom) : Theory (WithBot Atom) :=
  WithBot.some <$> T ∪ IPL (WithBot Atom)

omit [DecidableEq Atom] in
lemma Theory.toTheory_toITheory (T : Theory Atom) : T.toITheory.toTheory = T.iCompletion := by
  have toTo (A : Proposition (WithBot Atom)) : A.toIProposition.toProposition = A :=
    propEquiv.left_inv A
  ext
  simp [toTheory, toITheory, iCompletion, Functor.map, toTo]

/-- Turn an intuitionistic derivation into a minimal one. -/
def ITheory.IDerivation.toDerivation {T : ITheory Atom} {Γ : ICtx Atom} {A : IProposition Atom} :
    (T.IDerivation Γ A) → (T.toTheory.Derivation Γ.toCtx A.toProposition)
  | ax hA => .ax <| Set.mem_union_left _ ⟨A, hA, rfl⟩
  | ass hA => .ass <| Finset.mem_image.mpr ⟨A, hA, rfl⟩
  | conjI DA DB => .andI DA.toDerivation DB.toDerivation
  | conjE₁ D => .andE₁ D.toDerivation
  | conjE₂ D => .andE₂ D.toDerivation
  | disjI₁ D => .orI₁ D.toDerivation
  | disjI₂ D => .orI₂ D.toDerivation
  | disjE D DA DB => .orE D.toDerivation
    (Γ.toCtx_insert _ ▸ DA.toDerivation) (Γ.toCtx_insert _ ▸ DB.toDerivation)
  | implI Γ D => .implI Γ.toCtx (Γ.toCtx_insert _ ▸ D.toDerivation)
  | implE D D' => .implE D.toDerivation D'.toDerivation
  | efq A D => .implE (A := ⊥) (.ax (Set.mem_union_right _ ⟨A.toProposition, rfl⟩)) D.toDerivation

/-- Turnn a minimal derivation in the intuitionistic completion into an ordinary intuitionistic
derivation. -/
noncomputable def Theory.Derivation.toIDerivation {T : Theory Atom} {Γ : Ctx (WithBot Atom)}
    {A : Proposition (WithBot Atom)} :
    T.iCompletion.Derivation Γ A → T.toITheory.IDerivation Γ.toICtx A.toIProposition
  | ax hA => by
    by_cases hA' : A ∈ IPL (WithBot Atom)
    · rw [←Classical.choose_spec hA']
      exact .implI _ <| .efq _ <| .ass (Finset.mem_insert_self ..)
    · apply ITheory.IDerivation.ax
      obtain ⟨A', hAT, rfl⟩ : ∃ A' ∈ T, WithBot.some <$> A' = A := by
        simpa [iCompletion, hA', Functor.map] using hA
      use (discharger := rfl) A', hAT
  | ass hA => ITheory.IDerivation.ass <| by simpa [Ctx.toICtx, Finset.mem_image] using ⟨A, hA, rfl⟩
  | andI DA DB => DA.toIDerivation.conjI DB.toIDerivation
  | andE₁ D => D.toIDerivation.conjE₁
  | andE₂ D => D.toIDerivation.conjE₂
  | orI₁ D => D.toIDerivation.disjI₁
  | orI₂ D => D.toIDerivation.disjI₂
  | orE D DA DB => D.toIDerivation.disjE
    (Γ.toICtx_insert _ ▸ DA.toIDerivation) (Γ.toICtx_insert _ ▸ DB.toIDerivation)
  | implI Γ D => (Γ.toICtx_insert _ ▸ D.toIDerivation).implI _
  | implE D D' => D.toIDerivation.implE D'.toIDerivation

end Cslib.Logic.PL

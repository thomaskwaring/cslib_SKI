/-
Copyright (c) 2026 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
module

public import Cslib.Logics.Propositional.NaturalDeduction.Theory
public import Cslib.Foundations.Logic.LogicalEquivalence

/-! # Auxilliary natural deduction lemmas -/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Proposition Theory InferenceSystem DerivableIn Derivation IsIntuitionistic IsClassical

variable {Atom : Type u} [DecidableEq Atom] {T : Theory Atom}

namespace Theory

/-- Apply `and` to a pair of derivations. -/
def Derivation.andAnd {A A' B B' : Proposition Atom} (DA : T⇓({A} ⊢ A')) (DB : T⇓({B} ⊢ B')) :
    T⇓({A ∧ B} ⊢ A' ∧ B') := by
  apply andI
  · refine Derivation.cut (Γ := {A ∧ B}) (Δ := ∅) ?_ DA
    exact andE₁ (B := B) <| ass <| by grind
  · refine Derivation.cut (Γ := {A ∧ B}) (Δ := ∅) ?_ DB
    exact andE₂ (A := A) <| ass <| by grind

/-- Apply `and` to a pair of equivalences. -/
def equiv.andAnd {A A' B B' : Proposition Atom} (eA : T.equiv A A') (eB : T.equiv B B') :
    T.equiv (A ∧ B) (A' ∧ B') := ⟨eA.mp.andAnd eB.mp, eA.mpr.andAnd eB.mpr⟩

lemma DerivableIn.and_and {A A' B B' : Proposition Atom} (hA : DerivableIn T ({A} ⊢ A'))
    (hB : DerivableIn T ({B} ⊢ B')) : DerivableIn T ({A ∧ B} ⊢ A' ∧ B') := ⟨hA.some.andAnd hB.some⟩

lemma Equiv.and_and {A A' B B' : Proposition Atom} (hA : A ≡[T] A') (hB : B ≡[T] B') :
    (A ∧ B) ≡[T] (A' ∧ B') := ⟨hA.some.andAnd hB.some⟩

/-- Apply `or` to a pair of derivations. -/
def Derivation.orOr {A A' B B' : Proposition Atom} (DA : T⇓({A} ⊢ A')) (DB : T⇓({B} ⊢ B')) :
    T⇓({A ∨ B} ⊢ A' ∨ B') := by
  apply orE (ass <| Finset.mem_singleton_self (A ∨ B))
  · exact orI₁ <| DA.weakCtx <| by grind
  · exact orI₂ <| DB.weakCtx <| by grind

/-- Apply `or` to a pair of equivalences. -/
def equiv.orOr {A A' B B' : Proposition Atom} (eA : T.equiv A A') (eB : T.equiv B B') :
    T.equiv (A ∨ B) (A' ∨ B') := ⟨eA.mp.orOr eB.mp, eA.mpr.orOr eB.mpr⟩

lemma DerivableIn.or_or {A A' B B' : Proposition Atom} (hA : DerivableIn T ({A} ⊢ A'))
    (hB : DerivableIn T ({B} ⊢ B')) : DerivableIn T ({A ∨ B} ⊢ A' ∨ B') := ⟨hA.some.orOr hB.some⟩

lemma Equiv.or_or {A A' B B' : Proposition Atom} (hA : A ≡[T] A') (hB : B ≡[T] B') :
    (A ∨ B) ≡[T] (A' ∨ B') := ⟨hA.some.orOr hB.some⟩

/-- Apply `impl` to a pair of derivations. Note that `· → ·` is contravariant in its first
argument. -/
def Derivation.implImpl {A A' B B' : Proposition Atom} (DA : T⇓({A} ⊢ A')) (DB : T⇓({B} ⊢ B')) :
    T⇓({A' → B} ⊢ A → B') := by
  apply implI
  refine cut (A := B) (Γ := {A, A' → B}) (Δ := ∅) ?_ DB |>.weakCtx (by grind)
  exact implE (A := A') (ass <| by grind) (DA.weakCtx <| by grind)

/-- Apply `impl` to a pair of equivalences. -/
def equiv.implImpl {A A' B B' : Proposition Atom} (eA : T.equiv A A') (eB : T.equiv B B') :
    T.equiv (A → B) (A' → B') := ⟨eA.mpr.implImpl eB.mp, eA.mp.implImpl eB.mpr⟩

lemma DerivableIn.impl_impl {A A' B B' : Proposition Atom} (hA : DerivableIn T ({A} ⊢ A'))
    (hB : DerivableIn T ({B} ⊢ B')) : DerivableIn T ({A' → B} ⊢ A → B') :=
  ⟨hA.some.implImpl hB.some⟩

lemma Equiv.impl_impl {A A' B B' : Proposition Atom} (hA : A ≡[T] A') (hB : B ≡[T] B') :
    (A → B) ≡[T] (A' → B') := ⟨hA.some.implImpl hB.some⟩

/-- Apply `not` to a pair of derivations. -/
def Derivation.modusTollens [Bot Atom] {A B : Proposition Atom} (D : T⇓({A} ⊢ B)) :
    T⇓({¬ B} ⊢ ¬ A) := D.implImpl (ass <| Finset.mem_singleton_self ⊥)

/-- Apply `not` to an equivalence. -/
def equiv.not [Bot Atom] {A B : Proposition Atom} (e : T.equiv A B) :
    T.equiv (¬ A) (¬ B) := ⟨e.mpr.modusTollens, e.mp.modusTollens⟩

lemma DerivableIn.modus_tollens [Bot Atom] {A B : Proposition Atom} (h : DerivableIn T ({A} ⊢ B)) :
    DerivableIn T ({¬ B} ⊢ ¬ A) := ⟨h.some.modusTollens⟩

def Equiv.not [Bot Atom] {A B : Proposition Atom} (h : A ≡[T] B) :
    (¬ A) ≡[T] (¬ B) := ⟨h.some.not⟩

/-- Transform a derivation of `B` depending on a hypothesis `A` to a derivation of `¬ A` depending
on `¬ B`. -/
def Derivation.modusTollensSwap [Bot Atom] {Γ : Ctx Atom} {A B : Proposition Atom}
    (D : T⇓(insert A Γ ⊢ B)) : T⇓(insert (¬ B) Γ ⊢ ¬ A) :=
  implI _ <| implE (A := B) (ass <| by grind) (D.weakCtx <| by grind)

lemma DerivableIn.modus_tollens_swap [Bot Atom] {Γ : Ctx Atom} {A B : Proposition Atom}
    (h : DerivableIn T (insert A Γ ⊢ B)) : DerivableIn T (insert (¬ B) Γ ⊢ ¬ A) :=
  ⟨h.some.modusTollensSwap⟩

end Theory

/-- Transform a family of equivalences for each `Atom` into an equivalence of the
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
a context `Γ` and proposition `A`, which is valid if `Γ ⊢ A` is derivable in `T`. Judgement contexts
have two cases, for whether the hole is in the context or the conclusion.
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
  eqvFillValid h c hA := by
    cases c with
    | conc => exact equiv_iff_equiv_derivableIn.mp h _ |>.mp hA
    | hyp => exact equiv_iff_equiv_derivableIn_hypothesis.mp h _ _ |>.mp hA

end Cslib.Logic.PL

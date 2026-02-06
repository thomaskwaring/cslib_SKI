/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
import Cslib.Logics.Propositional.NaturalDeduction.Basic

/-! # Miscellaneous natural-deduction derivations

Rather than endeavouring to be exhaustive, we prove results as they are needed for applications.

## Main results

- Order theory: the fact that, modulo equivalence, the order `⊢[T]` and the logical operations give
a well-defined generalized Heyting algebra structure on the collection of propositions. If `T` is
intuitionistic, this is a bona-fide Heyting algebra, and if `T` is classical it is a Boolean
algebra.
-/

/-! ### Order theoretic results

The following amount to showing that "Propositions modulo equivalence" form a Heyting algebra: that
the operations are well-defined on equivalence classes, and the validity of the axioms.
-/

namespace PL

open Proposition Theory Derivation

variable {Atom : Type _} [DecidableEq Atom] {T : Theory Atom}

theorem Theory.le_wd (A B A' B' : Proposition Atom) (hA : A ≡[T] A') (hB : B ≡[T] B') :
    {A} ⊢[T] B ↔ {A'} ⊢[T] B' := by
  trans {A'} ⊢[T] B
  · exact T.equiv_iff_equiv_hypothesis.mp hA ∅ B
  · exact T.equiv_iff_equiv_conclusion.mp hB {A'}

theorem Theory.le_refl {A : Proposition Atom} : {A} ⊢[T] A := ⟨ass <| by grind⟩

theorem Theory.le_trans {A B C : Proposition Atom} (hAB : {A} ⊢[T] B)
    (hBC : {B} ⊢[T] C) : {A} ⊢[T] C := hAB.cut (Δ := ∅) hBC

theorem Theory.le_antisymm {A B : Proposition Atom} (hAB : {A} ⊢[T] B)
    (hBA : {B} ⊢[T] A) : A ≡[T] B := by grind

def infWD (A B A' B' : Proposition Atom) :
    T.equiv A A' → T.equiv B B' → T.equiv (A ⋏ B) (A' ⋏ B')
  | ⟨D,D'⟩, ⟨E,E'⟩ => by
    constructor
    · apply conjI
      · refine Theory.Derivation.cut (Γ := {A ⋏ B}) (Δ := ∅) ?_ D
        exact conjE₁ (B := B) <| ass <| by grind
      · refine Theory.Derivation.cut (Γ := {A ⋏ B}) (Δ := ∅) ?_ E
        exact conjE₂ (A := A) <| ass <| by grind
    · apply conjI
      · refine Theory.Derivation.cut (Γ := {A' ⋏ B'}) (Δ := ∅) ?_ D'
        exact conjE₁ (B := B') <| ass <| by grind
      · refine Theory.Derivation.cut (Γ := {A' ⋏ B'}) (Δ := ∅) ?_ E'
        exact conjE₂ (A := A') <| ass <| by grind

theorem Theory.inf_wd (A B A' B' : Proposition Atom) :
    A ≡[T] A' → B ≡[T] B' → (A ⋏ B) ≡[T] (A' ⋏ B')
  | ⟨D,D'⟩, ⟨E,E'⟩ => ⟨infWD _ _ _ _ ⟨D,D'⟩ ⟨E,E'⟩⟩

def supWD (A B A' B' : Proposition Atom) :
    T.equiv A A' → T.equiv B B' → T.equiv (A ⋎ B) (A' ⋎ B')
  | ⟨D,D'⟩, ⟨E,E'⟩ => by
    constructor
    · apply disjE (A := A) (B := B) (ass <| by grind)
      · apply disjI₁
        exact D.weak_ctx (by grind)
      · apply disjI₂
        exact E.weak_ctx (by grind)
    · apply disjE (A := A') (B := B') (ass <| by grind)
      · apply disjI₁
        exact D'.weak_ctx (by grind)
      · apply disjI₂
        exact E'.weak_ctx (by grind)

theorem Theory.sup_wd (A B A' B' : Proposition Atom) :
    A ≡[T] A' → B ≡[T] B' → (A ⋎ B) ≡[T] (A' ⋎ B')
  | ⟨D,D'⟩, ⟨E,E'⟩ => ⟨supWD _ _ _ _ ⟨D,D'⟩ ⟨E,E'⟩⟩

theorem Theory.inf_le_left {A B : Proposition Atom} : {A ⋏ B} ⊢[T] A :=
  ⟨conjE₁ (B := B) <| ass <| by grind⟩

theorem Theory.inf_le_right {A B : Proposition Atom} : {A ⋏ B} ⊢[T] B :=
  ⟨conjE₂ (A := A) <| ass <| by grind⟩

theorem Theory.le_inf {A B C : Proposition Atom} :
    {A} ⊢[T] B → {A} ⊢[T] C → {A} ⊢[T] (B ⋏ C)
  | ⟨D⟩, ⟨E⟩ => ⟨conjI (D.weak_ctx <| by grind) (E.weak_ctx <| by grind)⟩

theorem Theory.le_sup_left {A B : Proposition Atom} : {A} ⊢[T] (A ⋎ B) :=
  ⟨disjI₁ <| ass <| by grind⟩

theorem Theory.le_sup_right {A B : Proposition Atom} : {B} ⊢[T] (A ⋎ B) :=
  ⟨disjI₂ <| ass <| by grind⟩

theorem Theory.sup_le {A B C : Proposition Atom} :
    {A} ⊢[T] C → {B} ⊢[T] C → {A ⋎ B} ⊢[T] C
  | ⟨D⟩, ⟨E⟩ =>
    ⟨disjE (A := A) (B := B) (ass <| by grind) (D.weak_ctx <| by grind) (E.weak_ctx <| by grind)⟩

theorem Theory.le_top [Inhabited Atom] {A : Proposition Atom} : {A} ⊢[T] ⊤ :=
  ⟨derivationTop.weak_ctx (by grind)⟩

theorem Theory.bot_le [Bot Atom] {A : Proposition Atom} [IsIntuitionistic T] :
    {⊥} ⊢[T] A := ⟨implE (A := ⊥) (ax <| by grind) (ass <| by grind)⟩

def himpWD (A B A' B' : Proposition Atom) :
    T.equiv A A' → T.equiv B B' → T.equiv (A ⟶ B) (A' ⟶ B')
  | ⟨D,D'⟩, ⟨E,E'⟩ => by
    constructor
    · apply implI
      apply mapEquivConclusion _ ⟨E,E'⟩
      apply implE (A := A)
      · exact ass <| by grind
      · apply mapEquivConclusion _ ⟨D',D⟩
        exact ass <| by grind
    · apply implI
      apply mapEquivConclusion _ ⟨E',E⟩
      apply implE (A := A')
      · exact ass <| by grind
      · apply mapEquivConclusion _ ⟨D,D'⟩
        exact ass <| by grind

theorem Theory.himp_wd (A B A' B' : Proposition Atom) :
    A ≡[T] A' → B ≡[T] B' → (A ⟶ B) ≡[T] (A' ⟶ B')
  | ⟨eA⟩, ⟨eB⟩ => ⟨himpWD _ _ _ _ eA eB⟩

theorem Theory.le_himp_iff {A B C : Proposition Atom} :
    {A} ⊢[T] (B ⟶ C) ↔ {A ⋏ B} ⊢[T] C := by
  constructor <;> intro ⟨D⟩ <;> constructor
  · apply implE (A := B)
    · refine Theory.Derivation.cut (Γ := {A ⋏ B}) (Δ := ∅) ?_ D
      exact conjE₁ (B := B) <| ass <| by grind
    · exact conjE₂ (A := A) <| ass <| by grind
  · apply implI
    rw [← show ({B,A} : Ctx Atom) ∪ ∅ = {B,A} by grind]
    refine Theory.Derivation.cut (Γ := {B,A}) (Δ := ∅) ?_ D
    apply conjI <;> exact ass <| by grind

theorem Theory.compl_wd [Bot Atom] (A A' : Proposition Atom) :
    A ≡[T] A' → (~A) ≡[T] (~A') := (Theory.himp_wd A ⊥ A' ⊥ · (equivalent_refl ⊥))

theorem lem [Bot Atom] [IsClassical T] {A : Proposition Atom} : ⊢[T] (A ⋎ ~A) := by
  constructor
  apply implE (A := ~~(A ⋎ ~A)) (ax <| by grind)
  apply implI
  apply implE (A := A ⋎ ~A) (ass <| by grind)
  apply disjI₂
  apply implI
  refine implE (A := A) ?_ (ass <| by grind)
  apply implI
  apply implE (A := A ⋎ ~A) (ass <| by grind)
  apply disjI₁
  exact ass <| by grind

/-! ### Negation theorems -/

class PseudoBot (Atom : Type _) where
  r : Proposition Atom

section Neg

abbrev pseudoNeg [h : PseudoBot Atom] := (· ⟶ h.r)

scoped notation "⊥ᵣ" => PseudoBot.r
scoped prefix:40 "~ᵣ" => pseudoNeg

instance [Bot Atom] : PseudoBot Atom where
  r := ⊥

variable [PseudoBot Atom]

def conjNotNotDisj {A B : Proposition Atom} : T.equiv (~ᵣA ⋏ ~ᵣB) (~ᵣ(A ⋎ B)) := by
  constructor
  · apply implI
    apply disjE (A := A) (B := B) (ass <| by grind)
    · refine implE (A := A) ?_ (ass <| by grind)
      apply conjE₁ (B := ~ᵣB) (ass <| by grind)
    · refine implE (A := B) ?_ (ass <| by grind)
      apply conjE₂ (A := ~ᵣA) (ass <| by grind)
  · apply conjI
    · apply implI
      refine implE (A := A ⋎ B) (ass <| by grind) ?_ --(ass <| by grind)
      apply disjI₁ <| ass <| by grind
    · apply implI
      refine implE (A := A ⋎ B) (ass <| by grind) ?_ --(ass <| by grind)
      apply disjI₂ <| ass <| by grind

theorem Theory.conj_not_not_disj {A B : Proposition Atom} : (~ᵣA ⋏ ~ᵣB) ≡[T] (~ᵣ(A ⋎ B)) :=
  ⟨conjNotNotDisj⟩

def notConjOfDisjNot {A B : Proposition Atom} : T.Derivation ⟨{~ᵣA ⋎ ~ᵣB}, ~ᵣ(A ⋏ B)⟩ := by
  apply implI
  apply disjE (A := ~ᵣA) (B := ~ᵣB) (ass <| by grind)
  · apply implE (A := A) (ass <| by grind)
    apply conjE₁ (B := B) <| ass <| by grind
  · apply implE (A := B) (ass <| by grind)
    apply conjE₂ (A := A) <| ass <| by grind

theorem Theory.not_conj_of_disj_not {A B : Proposition Atom} : {~ᵣA ⋎ ~ᵣB} ⊢[T] (~ᵣ(A ⋏ B)) :=
  ⟨notConjOfDisjNot⟩

def conjDnShift {A B : Proposition Atom} : T.equiv (~ᵣ~ᵣA ⋏ ~ᵣ~ᵣB) (~ᵣ~ᵣ(A ⋏ B)) := by
  constructor
  · apply implI
    apply implE (A := ~ᵣA) (conjE₁ (B := ~ᵣ~ᵣB) <| ass <| by grind)
    apply implI
    apply implE (A := ~ᵣB) (conjE₂ (A := ~ᵣ~ᵣA) <| ass <| by grind)
    apply implI
    apply implE (A := A ⋏ B) (ass <| by grind)
    apply conjI <;> exact ass <| by grind
  · apply conjI
    · apply implI
      apply implE (A := ~ᵣ(A ⋏ B)) (ass <| by grind)
      apply implI
      apply implE (A := A) (ass <| by grind)
      exact conjE₁ (B := B) (ass <| by grind)
    · apply implI
      apply implE (A := ~ᵣ(A ⋏ B)) (ass <| by grind)
      apply implI
      apply implE (A := B) (ass <| by grind)
      exact conjE₂ (A := A) (ass <| by grind)

def Theory.conj_dn_shift {A B : Proposition Atom} : (~ᵣ~ᵣA ⋏ ~ᵣ~ᵣB) ≡[T] (~ᵣ~ᵣ(A ⋏ B)) :=
  ⟨conjDnShift⟩

def doubleNegOfSelf {A : Proposition Atom} : T.Derivation ⟨{A},~ᵣ~ᵣA⟩ := by
  apply implI; apply implE (A := A) <;> exact ass <| by grind

def Theory.Derivation.modusTollens {Γ : Ctx Atom} {A B : Proposition Atom}
    (D : T.Derivation ⟨insert A Γ, B⟩) : T.Derivation ⟨insert (~ᵣB) Γ, ~ᵣA⟩ := by
  apply implI; apply implE (A := B) (ass <| by grind); exact D.weak_ctx <| by grind

def tripleNeg {A : Proposition Atom} : T.equiv (~ᵣ~ᵣ~ᵣA) (~ᵣA) :=
  ⟨doubleNegOfSelf.modusTollens (Γ := ∅), doubleNegOfSelf⟩

def equivNotOfEquiv {A B : Proposition Atom} (e : T.equiv A B) : T.equiv (~ᵣA) (~ᵣB) :=
  ⟨e.2.modusTollens (Γ := ∅), e.1.modusTollens (Γ := ∅)⟩

def notNotDisjNotOfNotConj {A B : Proposition Atom} :
    T.equiv (~ᵣ(A ⋏ B)) (~ᵣ~ᵣ(~ᵣA ⋎ ~ᵣB)) := by
  refine transEquiv (B := ~ᵣ(~ᵣ~ᵣA ⋏ ~ᵣ~ᵣB)) ?_ ?_
  · refine transEquiv (B := ~ᵣ~ᵣ~ᵣ(A ⋏ B)) ?_ ?_
    · exact commEquiv tripleNeg
    · apply equivNotOfEquiv
      exact commEquiv conjDnShift
  · apply equivNotOfEquiv
    exact conjNotNotDisj





end Neg

end PL

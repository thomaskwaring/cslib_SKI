/-
Copyright (c) 2026 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
module

public import Cslib.Logics.Propositional.Semantics.Heyting

/-! # Two-valued semantics -/

namespace Cslib.Logic.PL

open Theory Derivation InferenceSystem Proposition Valuation Bool

universe u

variable {Atom : Type u} [DecidableEq Atom] {T : Theory Atom}

namespace Proposition

def flip [Bot Atom] (v : Valuation Atom Bool) (A : Proposition Atom) :=
  match v⟦A⟧ with
  | true => A
  | false => ¬A

omit [DecidableEq Atom] in
lemma flip_def [Bot Atom] (v : Valuation Atom Bool) (A : Proposition Atom) :
    A.flip v = match v⟦A⟧ with
      | true => A
      | false => ¬ A := rfl

def atoms : Proposition Atom → List Atom
  | atom x => [x]
  | and A B | or A B | impl A B => A.atoms ++ B.atoms

variable (x : Atom) (A B : Proposition Atom)

def derivationFlip [Bot Atom] [IsIntuitionistic T] [IsClassical T] (Γ : Ctx Atom)
    (A : Proposition Atom) (v : Valuation Atom Bool) (h : ∀ x ∈ A.atoms, (atom x).flip v ∈ Γ) :
    T.Derivation Γ (A.flip v) :=
  match A with
  | atom x => ass (h x <| by simp [atoms])
  | Proposition.and A B => by
    rw [flip, interp_and]
    match hA : v⟦A⟧ with
    | true =>
      match hB : v⟦B⟧ with
      | true =>
        apply conjI
        · rw [show A = A.flip v by simp [Proposition.flip, hA]]
          exact A.derivationFlip Γ v (by grind [atoms])
        · rw [show B = B.flip v by simp [Proposition.flip, hB]]
          exact B.derivationFlip Γ v (by grind [atoms])
      | false =>
        apply implI
        refine implE (A := B) ?_ ?_
        · rw [show (B → ⊥) = B.flip v by simp [Proposition.flip, hB]]
          exact B.derivationFlip _ v (by grind [atoms])
        · apply conjE₂ (A := A); exact ass <| Finset.mem_insert_self ..
    | false =>
      apply implI
      refine implE (A := A) ?_ ?_
      · rw [show (A → ⊥) = A.flip v by simp [Proposition.flip, hA]]
        exact A.derivationFlip _ v (by grind [atoms])
      · apply conjE₁ (B := B); exact ass <| Finset.mem_insert_self ..
  | Proposition.or A B => by
    rw [flip, interp_or]
    match hA : v⟦A⟧ with
    | true =>
      apply disjI₁
      rw [show A = A.flip v by simp [flip, hA]]
      exact A.derivationFlip Γ v (by grind [atoms])
    | false =>
      match hB : v⟦B⟧ with
      | true =>
        apply disjI₂
        rw [show B = B.flip v by simp [flip, hB]]
        exact B.derivationFlip Γ v (by grind [atoms])
      | false =>
        apply implI; apply disjE (ass <| Finset.mem_insert_self ..)
        · refine implE (A := A) ?_ (ass <| Finset.mem_insert_self ..)
          rw [show (A → ⊥) = A.flip v by simp [Proposition.flip, hA]]
          exact A.derivationFlip _ v (by grind [atoms])
        · refine implE (A := B) ?_ (ass <| Finset.mem_insert_self ..)
          rw [show (B → ⊥) = B.flip v by simp [Proposition.flip, hB]]
          exact B.derivationFlip _ v (by grind [atoms])
  | impl A B => by
    rw [flip, interp_impl]
    match hA : v⟦A⟧ with
    | true =>
      match hB : v⟦B⟧ with
      | true =>
        apply implI
        rw [show B = B.flip v by simp [Proposition.flip, hB]]
        exact B.derivationFlip _ v (by grind [atoms])
      | false =>
        apply implI; apply implE (A := B)
        · rw [show (B → ⊥) = B.flip v by simp [Proposition.flip, hB]]
          exact B.derivationFlip _ v (by grind [atoms])
        · apply implE (A := A) (ass <| Finset.mem_insert_self ..)
          rw [show A = A.flip v by simp [flip, hA]]
          exact A.derivationFlip _ v (by grind [atoms])
    | false =>
      simp only [himp, Bool.not_false, Bool.le_true, sup_of_le_right]
      apply implI; apply implE (A := ⊥) (T.efq B |>.weak_ctx <| by grind)
      refine implE (A := A) ?_ (ass <| Finset.mem_insert_self ..)
      rw [show (A → ⊥) = A.flip v by simp [Proposition.flip, hA]]
      exact A.derivationFlip _ v (by grind [atoms])

def byCases [Bot Atom] [IsClassical T] {A B : Proposition Atom} {Γ : Ctx Atom}
    (D : T⇓(insert A Γ ⊢ B)) (D' : T⇓(insert (¬ A) Γ ⊢ B)) : T⇓(Γ ⊢ B) :=
  (lem A |>.weak_ctx (Δ := Γ) <| Finset.empty_subset ..).disjE D D'

def derivationTautAux [Bot Atom] [IsIntuitionistic T] [IsClassical T] (xs : List Atom)
    (Γ : Ctx Atom) (A : Proposition Atom) (hA : ∀ u : Valuation Atom Bool, u⟦A⟧ = true)
    (v : Valuation Atom Bool) (hΓ : ∀ x ∈ A.atoms, x ∈ xs ∨ (atom x).flip v ∈ Γ) :
    T.Derivation Γ A := by
  have hA' : ∀ u : Valuation Atom Bool, A.flip u = A := by simp [flip, hA]
  match xs with
  | [] => exact hA' v ▸ derivationFlip Γ A v (by simpa using hΓ)
  | x :: xs =>
    apply byCases (A := atom x) (B := A) (Γ := Γ)
    · let v' : Valuation Atom Bool := fun y => if x = y then true else v y
      apply A.derivationTautAux xs (insert (atom x) Γ) hA v'
      intro y hy
      by_cases hxy : x = y
      case pos => rw [←hxy, show (atom x).flip v' = atom x by simp [v', flip]]; grind
      case neg =>
        rw [show (atom y).flip v' = (atom y).flip v by simp [flip, v', hxy]]
        grind
    · let v' : Valuation Atom Bool := fun y => if x = y then false else v y
      apply A.derivationTautAux xs (insert (¬ atom x) Γ) hA v'
      intro y hy
      by_cases hxy : x = y
      case pos => rw [←hxy, show (atom x).flip v' = (¬ atom x) by simp [v', flip]]; grind
      case neg =>
        rw [show (atom y).flip v' = (atom y).flip v by simp [flip, v', hxy]]
        grind

def derivationTaut [Bot Atom] [IsIntuitionistic T] [IsClassical T] (A : Proposition Atom)
    (hA : ∀ u : Valuation Atom Bool, u⟦A⟧ = true) : T⇓A :=
  A.derivationTautAux A.atoms ∅ hA (fun _ => true) (fun _ hx => Or.inl hx)

end Proposition

lemma Theory.lt_iff {T T' : Theory Atom} :
    T < T' ↔ T ≤ T' ∧ ∃ A ∈ T', ¬ DerivableIn T A := by
  simp [LE.le, LT.lt, WeakerThan]

-- theorem Theory.inconsistent_of_gt_CPL [Bot Atom] [IsIntuitionistic T] [IsClassical T]
--   (h : CPL < T) :
--     T.Inconsistent := by
--   obtain ⟨hle, ⟨A, h, h'⟩⟩ := Theory.lt_iff.mp h


end Cslib.Logic.PL

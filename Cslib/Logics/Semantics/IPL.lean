/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
import Cslib.Logics.NaturalDeduction.NJ
import Mathlib.Order.Heyting.Basic
import Mathlib.Data.Finset.Fold
import Mathlib.Order.Fin.Basic

/-! # Heyting-algebra semantics for intuitionistic propositional logic -/

universe u

variable {Atom : Type u} [DecidableEq Atom]

namespace IPL

namespace Semantics

abbrev Valuation (Atom : Type u) (H : Type _) [HeytingAlgebra H] := Atom → H

open Proposition NJ

section defs

variable {H : Type _} [HeytingAlgebra H] (v : Valuation Atom H)

/-- The interpretation of a compound formula in a Heyting algebra -/
def Proposition.interpret : Proposition Atom → H
  | atom x => v x
  | bot => ⊥
  | conj A B => (Proposition.interpret A) ⊓ (Proposition.interpret B)
  | disj A B => (Proposition.interpret A) ⊔ (Proposition.interpret B)
  | impl A B => (Proposition.interpret A) ⇨ (Proposition.interpret B)

scoped notation v "[" A "]" => Proposition.interpret v A

-- instance interpPropCoe : CoeFun (Valuation Atom H) (fun _ => Proposition Atom → H) where
--   coe := Proposition.interpret

def Ctx.interpret (Γ : Ctx Atom) : H := Γ.fold (· ⊓ ·) ⊤ (Proposition.interpret v)

scoped notation v "[" Γ "]" => Ctx.interpret v Γ

-- instance interpCtxCoe : CoeFun (Valuation Atom H) (fun _ => Ctx Atom → H) where
--   coe := Ctx.interpret

theorem Ctx.interpret_antitone {Γ Δ : Ctx Atom} (h : Γ ⊆ Δ) :
    v[Δ] ≤ v[Γ] := by
  have h_disj : Disjoint Γ (Δ \ Γ) := Finset.disjoint_sdiff
  have hΔ : Γ.disjUnion (Δ \ Γ) h_disj = Δ := by grind
  have h_top : ⊤ ⊓ ⊤ = (⊤ : H) := top_inf_eq ⊤
  unfold interpret
  nth_rw 1 [←h_top]
  rw [←hΔ, Finset.fold_disjUnion h_disj]
  exact inf_le_left

def Sequent.valid : Sequent Atom → Prop
  | ⟨Γ,A⟩ => (v[Γ]) ≤ (v[A])

end defs

section soundness

variable {H : Type _} [HeytingAlgebra H] (v : Valuation Atom H)

open Derivation

/-! ### Soundness -/

protected theorem sound {S : Sequent Atom} (D : Derivation S) : Sequent.valid v S := by
  induction D with
  | ax Γ A =>
    simp [Sequent.valid, Ctx.interpret]
  | botE _ _ ih =>
    dsimp! only at ih ⊢
    trans ⊥
    · assumption
    · exact OrderBot.bot_le _
  | conjI _ _ ih ih' =>
    dsimp! only at ih ih' ⊢
    exact le_inf ih ih'
  | @conjE₁ _ A B _ ih =>
    dsimp! only at ih ⊢
    trans v[A] ⊓ v[B]
    · assumption
    · exact inf_le_left
  | @conjE₂ _ A B _ ih =>
    dsimp! only at ih ⊢
    trans v[A] ⊓ v[B]
    · assumption
    · exact inf_le_right
  | @disjI₁ _ A _ _ ih =>
    dsimp! only at ih ⊢
    trans v[A]
    · assumption
    · exact le_sup_left
  | @disjI₂ _ _ B _ ih =>
    dsimp! only at ih ⊢
    trans v[B]
    · assumption
    · exact le_sup_right
  | @disjE Γ A B C _ _ _ ih₁ ih₂ ih₃ =>
    dsimp! only at ih₁ ih₂ ih₃ ⊢
    trans v[insert A Γ] ⊔ v[insert B Γ]
    · simp only [Ctx.interpret, Finset.fold_insert_idem]
      rw [←inf_sup_right]
      apply le_inf
      · assumption
      · rfl
    · apply sup_le <;> assumption
  | implI Γ _ ih =>
    dsimp! only at ih ⊢
    refine le_himp_iff.mpr ?_
    simpa [Ctx.interpret, inf_comm] using ih
  | @implE _ A B _ _ ih ih' =>
    dsimp! only at ih ih' ⊢
    trans (v[A] ⇨ v[B]) ⊓ v[A]
    · apply le_inf <;> assumption
    · exact himp_inf_le

protected theorem sound' {S : Sequent Atom} (h : Derivable S) : Sequent.valid v S :=
  let ⟨D⟩ := h; IPL.Semantics.sound v D

theorem not_lem_derivable (x : Atom) : ¬ Derivable ⟨∅, (atom x).disj <| impl (atom x) bot⟩ := by
  intro h
  let v : Atom → Fin 3 := fun _ => 1
  have h_sound : _ := IPL.Semantics.sound' v h
  simp [Sequent.valid, Ctx.interpret, Finset.fold_empty, Top.top, Proposition.interpret,
    v, Bot.bot, himp] at h_sound

theorem not_dne_derivable (x : Atom) : ¬ Derivable ⟨{impl (atom x) bot |>.impl bot}, atom x⟩ := by
  intro h
  let v : Atom → Fin 3 := fun _ => 1
  have h_sound : _ := IPL.Semantics.sound' v h
  simp [Sequent.valid, Ctx.interpret, Proposition.interpret, Finset.fold_singleton, v, Top.top,
    Bot.bot, himp] at h_sound

end soundness

section completeness

open Derivation

/-!
### Completeness

Completeness for the Heyting-algebra semantics follows from the fact that
{Propositions}/equivalence is itself a Heyting algebra, and a proposition maps under the obvious
valuation to the top element iff it is derivable.
-/

def propQuotient : Type _ := Quotient <| IPL.NJ.propositionSetoid (Atom := Atom)

instance propPO : PartialOrder <| propQuotient (Atom := Atom) where
  le := by
    apply Quotient.lift₂ (f := fun A B => Derivable ⟨{A},B⟩)
    intro A B A' B' hA hB
    rw [eq_iff_iff]
    constructor <;> intro h
    · apply (equivalent_derivability {A'} hB).mp
      have :_ := (equivalent_hypotheses (C := B) ∅ hA)
      rw [insert_empty_eq] at this
      exact this.mp h
    · apply (equivalent_derivability {A} hB).mpr
      have :_ := (equivalent_hypotheses (C := B') ∅ hA)
      rw [insert_empty_eq] at this
      exact this.mpr h
  le_refl := by
    apply Quotient.ind
    intro A
    simp_rw [Quotient.lift_mk]
    exact ⟨ax' (by grind)⟩
  le_trans := by
    apply Quotient.ind₂
    intro A B
    apply Quotient.ind
    intro C
    simp_rw [Quotient.lift_mk]
    intro ⟨AB⟩ ⟨BC⟩
    exact ⟨BC.subs' AB⟩
  le_antisymm := by
    apply Quotient.ind₂
    intro A B
    simp_rw [Quotient.lift_mk]
    intro hAB hBC
    simp only [NJ.propositionSetoid, propQuotient, Quotient.eq]
    exact ⟨hAB, hBC⟩

instance propLattice : Lattice <| propQuotient (Atom := Atom) where
  inf := by
    apply Quotient.lift₂ (f := fun A B => Quotient.mk NJ.propositionSetoid <| A.conj B)
    intro A B A' B' ⟨⟨DA'⟩, ⟨DA⟩⟩ ⟨⟨DB'⟩, ⟨DB⟩⟩
    simp only [NJ.propositionSetoid, Quotient.eq]
    constructor <;> constructor
    · apply conjI
      · apply DA'.subs' (Γ := {A.conj B})
        apply conjE₁ (B := B)
        apply ax' (by grind)
      · apply DB'.subs' (Γ := {A.conj B})
        apply conjE₂ (A := A)
        apply ax' (by grind)
    · apply conjI
      · apply DA.subs' (Γ := {A'.conj B'})
        apply conjE₁ (B := B')
        apply ax' (by grind)
      · apply DB.subs' (Γ := {A'.conj B'})
        apply conjE₂ (A := A')
        apply ax' (by grind)
  sup := by
    apply Quotient.lift₂ (f := fun A B => Quotient.mk NJ.propositionSetoid <| A.disj B)
    intro A B A' B' ⟨⟨DA'⟩, ⟨DA⟩⟩ ⟨⟨DB'⟩, ⟨DB⟩⟩
    simp only [NJ.propositionSetoid, Quotient.eq]
    constructor <;> constructor
    · apply disjE (A := A) (B := B)
      · apply ax' (by grind)
      · apply disjI₁
        exact DA'.weak' (Δ := {A, A.disj B}) (by grind)
      · apply disjI₂
        exact DB'.weak' (Δ := {B, A.disj B}) (by grind)
    · apply disjE (A := A') (B := B')
      · apply ax' (by grind)
      · apply disjI₁
        exact DA.weak' (Δ := {A', A'.disj B'}) (by grind)
      · apply disjI₂
        exact DB.weak' (Δ := {B', A'.disj B'}) (by grind)
  inf_le_left := by
    apply Quotient.ind₂
    simp only [Quotient.lift_mk, LE.le]
    intro A B
    constructor
    apply conjE₁ (B := B)
    apply ax' (by grind)
  inf_le_right := by
    apply Quotient.ind₂
    simp only [Quotient.lift_mk, LE.le]
    intro A B
    constructor
    apply conjE₂ (A := A)
    apply ax' (by grind)
  le_inf := by
    apply Quotient.ind₂
    intro A B
    apply Quotient.ind
    intro C
    simp only [Quotient.lift_mk, LE.le]
    intro ⟨AB⟩ ⟨AC⟩
    exact ⟨conjI AB AC⟩
  le_sup_left := by
    apply Quotient.ind₂
    simp only [Quotient.lift_mk, LE.le]
    intro A B
    constructor
    apply disjI₁
    apply ax' (by grind)
  le_sup_right := by
    apply Quotient.ind₂
    simp only [Quotient.lift_mk, LE.le]
    intro A B
    constructor
    apply disjI₂
    apply ax' (by grind)
  sup_le := by
    apply Quotient.ind₂
    intro A B
    apply Quotient.ind
    intro C
    simp only [Quotient.lift_mk, LE.le]
    intro ⟨AC⟩ ⟨BC⟩
    constructor
    apply disjE (Γ := {A.disj B}) (A := A) (B := B) (C := C)
    · apply ax' (by grind)
    · apply AC.weak' (Δ := {A, A.disj B})
      grind
    · apply BC.weak' (Δ := {B, A.disj B})
      grind

instance propHeyting : HeytingAlgebra <| propQuotient (Atom := Atom) where
  top := Quotient.mk NJ.propositionSetoid Proposition.top
  le_top := by
    apply Quotient.ind
    simp only [Quotient.lift_mk, LE.le]
    intro A
    exact ⟨derivationTop.weak' (Δ := {A}) (by grind)⟩
  bot := Quotient.mk NJ.propositionSetoid Proposition.bot
  bot_le := by
    apply Quotient.ind
    simp only [Quotient.lift_mk, LE.le]
    intro A
    constructor
    apply botE
    apply ax' (by grind)
  himp := by
    apply Quotient.lift₂ (f := fun A B => Quotient.mk NJ.propositionSetoid <| A.impl B)
    intro A B A' B' ⟨⟨DA'⟩, ⟨DA⟩⟩ ⟨⟨DB'⟩, ⟨DB⟩⟩
    simp only [NJ.propositionSetoid, Quotient.eq]
    constructor <;> constructor
    · apply implI
      apply DB'.subs'
      apply implE (A := A)
      · apply ax' (by grind)
      · exact DA.weak' (Δ := {A', A.impl B}) (by grind)
    · apply implI
      apply DB.subs'
      apply implE (A := A')
      · apply ax' (by grind)
      · exact DA'.weak' (Δ := {A, A'.impl B'}) (by grind)
  le_himp_iff := by
    apply Quotient.ind₂
    intro A B
    apply Quotient.ind
    intro C
    simp only [Quotient.lift₂_mk, LE.le, min, Lattice.inf]
    constructor <;> intro ⟨D⟩ <;> constructor
    · apply implE (A := B)
      · apply D.subs'
        apply conjE₁ (B := B)
        apply ax' (by grind)
      · apply conjE₂ (A := A)
        apply ax' (by grind)
    · apply implI
      apply D.subs'
      apply conjI <;> apply ax' (by grind)
  compl := by
    apply Quotient.lift (f := fun A => Quotient.mk NJ.propositionSetoid (A.impl bot))
    intro A B ⟨⟨AB⟩, ⟨BA⟩⟩
    simp only [NJ.propositionSetoid, Quotient.eq]
    constructor <;> constructor
    · apply implI
      apply implE (A := A)
      · apply ax' (by grind)
      · apply BA.weak'
        grind
    · apply implI
      apply implE (A := B)
      · apply ax' (by grind)
      · apply AB.weak'
        grind
  himp_bot := by
    apply Quotient.ind
    simp [NJ.propositionSetoid]

def canonicalValuation : (Valuation Atom <| propQuotient (Atom := Atom)) := fun x => ⟦atom x⟧

theorem canonicalValuation_spec (A : Proposition Atom) :
    Proposition.interpret canonicalValuation A = ⟦A⟧ := by
  induction A with
  | atom x => simp! [canonicalValuation]
  | bot => simp! [Bot.bot]
  | conj A B ihA ihB => simp! [min, SemilatticeInf.inf, Lattice.inf, ihA, ihB]
  | disj A B ihA ihB => simp! [max, SemilatticeSup.sup, ihA, ihB]
  | impl A B ihA ihB => simp! [himp, ihA, ihB]

protected theorem complete (A : Proposition Atom) (h : Sequent.valid canonicalValuation ⟨∅, A⟩) :
    Proposition.PDerivable A := by
  simp! only [canonicalValuation_spec, Ctx.interpret, Finset.fold_empty, Top.top, LE.le,
    Quotient.lift_mk] at h
  let ⟨D⟩ := h.subs' top_derivable
  exact ⟨D⟩

end completeness

end Semantics

end IPL

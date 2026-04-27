/-
Copyright (c) 2026 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
module

public import Cslib.Init
public import Mathlib.Order.Heyting.Basic
public import Mathlib.Order.WithBot

@[expose] public section

noncomputable instance WithTop.heyting {α : Type*} [GeneralizedHeytingAlgebra α] :
    GeneralizedHeytingAlgebra (WithTop α) where
  himp x y :=
    have : DecidableLE α := Classical.decRel LE.le
    y.recTopCoe ⊤ fun y' => x.recTopCoe ↑y' (fun x' => if x' ≤ y' then ⊤ else ↑(x' ⇨ y'))
  le_himp_iff a b c := by
    cases c with
    | top => simp
    | coe c' =>
      cases a with
      | top => cases b <;> simp
      | coe a' =>
        cases b with
        | top => simp
        | coe b' =>
          by_cases h : b' ≤ c'
          · simp only [recTopCoe_coe, h, ↓reduceIte, le_top, ← coe_inf, coe_le_coe, true_iff]
            exact inf_le_right.trans h
          · simp [h, ←coe_inf]

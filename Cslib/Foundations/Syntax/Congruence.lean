/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Foundations.Syntax.Context
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs

@[expose] public section

namespace Cslib

/-- An equivalence relation preserved by all contexts. -/
class Congruence (α : Type*) [HasContext α] (r : α → α → Prop) extends
  IsEquiv α r, covariant : CovariantClass (HasContext.Context α) α (·[·]) r

lemma Congruence.iff_covariantClass_and_equivalence {α : Type*} [HasContext α] (r : α → α → Prop) :
    Congruence α r ↔ CovariantClass (HasContext.Context α) α (·[· ]) r ∧ Equivalence r := by
  constructor
  · intro h
    refine ⟨⟨h.elim⟩, ?_, ?_, ?_⟩
    all_goals grind [h.refl, h.symm, h.trans]
  · intro ⟨hco, hrefl, hsymm, htrans⟩
    have : Std.Refl r := by grind [Std.Refl]
    have : Std.Symm r := by grind [Std.Symm]
    have : IsTrans α r := by grind [IsTrans]
    have : IsPreorder α r := by constructor
    have : IsEquiv α r := by constructor
    constructor

end Cslib

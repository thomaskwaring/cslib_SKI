/-
Copyright (c) 2026 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
module

public import Cslib.ForMathlib.Order.PFilter
public import Mathlib.Order.PrimeIdeal

@[expose] public section

namespace Order

variable {P : Type*} [Preorder P] (IF : Ideal.PrimePair P)

namespace Ideal.PrimePair

protected def dual : PrimePair P → PrimePair Pᵒᵈ
  | ⟨I, F, h⟩ => ⟨F.dual, {dual := I}, by
    rw [PFilter.dual_coe, ←h.compl_eq, PFilter.coe_mk,
      Set.image_compl_eq (Equiv.bijective OrderDual.toDual)]
    exact IsCompl.symm isCompl_compl
  ⟩

lemma dual_I_eq : IF.dual.I = IF.F.dual := rfl

lemma dual_F_dual_eq : IF.dual.F.dual = IF.I := rfl

end Ideal.PrimePair

variable {P : Type*} [SemilatticeSup P] {F : PFilter P}

namespace PFilter

theorem IsPrime.mem_or_mem (hF : F.IsPrime) {x y : P} : x ⊔ y ∈ F → x ∈ F ∨ y ∈ F := by
  contrapose!
  let I := hF.compl_ideal.toIdeal
  change x ∈ I ∧ y ∈ I → x ⊔ y ∈ I
  exact fun h => Ideal.sup_mem h.1 h.2

theorem IsPrime.iff_dual : F.IsPrime ↔ F.dual.IsPrime :=
  ⟨fun h => h.toPrimePair.dual.I_isPrime, fun h => h.toPrimePair.dual.F_isPrime⟩

end Order.PFilter

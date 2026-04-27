/-
Copyright (c) 2026 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
module

public import Cslib.ForMathlib.Order.PrimeIdeal
public import Cslib.ForMathlib.Order.Ideal
public import Mathlib.Order.PrimeSeparator

@[expose] public section

open Order OrderDual Ideal PFilter Set

variable {P : Type*} [DistribLattice P] [BoundedOrder P] {F : PFilter P} {I : Ideal P}

namespace DistribLattice

lemma mem_pFilter_sup_principal (x y : P) (F : PFilter P) :
    y ∈ F ⊔ PFilter.principal x ↔ ∃ f ∈ F, f ⊓ x ≤ y := by
  constructor
  · intro ⟨f, hf, g, hg, hle⟩
    rw [mem_dual] at hf hg
    use f, hf
    exact (inf_le_inf_left (ofDual f) hg).trans hle.dual
  · intro ⟨f, hf, hle⟩
    use f, hf, x, mem_principal_self, hle.dual

theorem prime_filter_of_disjoint_filter_ideal (hFI : Disjoint (F : Set P) (I : Set P)) :
    ∃ G : PFilter P, (IsPrime G) ∧ F ≤ G ∧ Disjoint (G : Set P) I := by
  have hFI_dual : Disjoint (I.dual : Set Pᵒᵈ) F.dual := by
    rw [Set.disjoint_iff] at hFI ⊢
    rintro _ ⟨⟨x, hx, rfl⟩, hx'⟩
    exact hFI ⟨hx', hx⟩
  obtain ⟨J, hJ, hle, hdisj⟩ := prime_ideal_of_disjoint_filter_ideal hFI_dual
  refine ⟨⟨J⟩, IsPrime.iff_dual.mpr hJ, hle, ?_⟩
  rw [Set.disjoint_iff] at hdisj ⊢
  intro x ⟨hx, hx'⟩
  exact hdisj ⟨⟨x, hx', rfl⟩, hx⟩

end DistribLattice

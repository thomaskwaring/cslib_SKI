/-
Copyright (c) 2026 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
module

public import Cslib.ForMathlib.Order.Ideal
public import Mathlib.Order.PFilter

@[expose] public section

open OrderDual

namespace Order

variable {P : Type*} [Preorder P] (F G : PFilter P)

def Ideal.dual (I : Ideal P) : PFilter Pᵒᵈ where
  dual := I.map (OrderIso.dualDual P)

lemma Ideal.dual_coe (I : Ideal P) : (I.dual : Set Pᵒᵈ) = toDual '' I := rfl

namespace PFilter

@[simp]
lemma mem_coe (x : P) (F : PFilter P) : x ∈ (F : Set P) ↔ x ∈ F := Iff.rfl

lemma principal_bot [OrderTop P] : (principal ⊤ : PFilter P) = ⊥ := rfl

lemma mem_dual (x : Pᵒᵈ) (F : PFilter P) : x ∈ F.dual ↔ ofDual x ∈ F := Iff.rfl

lemma dual_coe : (F.dual : Set Pᵒᵈ) = toDual '' F := by
  ext
  simp [mem_dual]

lemma coe_mk (I : Ideal Pᵒᵈ) : (PFilter.mk I : Set P) = ofDual '' I := by
  ext
  simp

@[simp]
lemma dual_le_dual (F G : PFilter P) : F.dual ≤ G.dual ↔ F ≤ G := Iff.rfl

def orderIsoDual : PFilter P ≃o Ideal Pᵒᵈ where
  toFun := PFilter.dual
  invFun := PFilter.mk
  map_rel_iff' := by
    intro _ _
    simp

section Lattice

variable {P : Type*} [SemilatticeInf P] [IsDirectedOrder P] {x : P} (F G : PFilter P)

instance instMin : Min (PFilter P) where
  min F G := {dual := F.dual ⊓ G.dual}

instance instMax : Max (PFilter P) where
  max F G := {dual := F.dual ⊔ G.dual}

@[simp]
lemma inf_dual : (F ⊓ G).dual = F.dual ⊓ G.dual := rfl

@[simp]
lemma sup_dual : (F ⊔ G).dual = F.dual ⊔ G.dual := rfl

instance instLattice : Lattice (PFilter P) where
  sup := (· ⊔ ·)
  le_sup_left := by simp [←dual_le_dual]
  le_sup_right := by simp [←dual_le_dual]
  sup_le := by simp only [← dual_le_dual, sup_dual, sup_le_iff]; grind
  inf := (· ⊓ ·)
  inf_le_left := by simp [←dual_le_dual]
  inf_le_right := by simp [←dual_le_dual]
  le_inf := by simp only [← dual_le_dual, inf_dual, le_inf_iff]; grind

@[simp]
lemma coe_sup : ↑(F ⊔ G) = {x | ∃ a ∈ F, ∃ b ∈ G, a ⊓ b ≤ x} := rfl

omit [IsDirectedOrder P] in
@[simp]
lemma coe_inf : ↑(F ⊓ G : Set P) = (F : Set P) ∩ G := rfl

@[simp]
lemma mem_sup : x ∈ F ⊔ G ↔ ∃ a ∈ F, ∃ b ∈ G, a ⊓ b ≤ x := Iff.rfl

@[simp]
lemma mem_inf : x ∈ F ⊓ G ↔ x ∈ F ∧ x ∈ G := Iff.rfl

end Lattice

end Order.PFilter

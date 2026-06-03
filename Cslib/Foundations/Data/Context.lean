/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Cslib.Init
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Lattice.Basic

@[expose] public section

namespace Cslib

class Adjoin (Elem : outParam Type*) (Coll : Type*) where
  adjoin : Elem → Coll → Coll
export Adjoin (adjoin)

instance (α : Type*) : Adjoin α (Set α) := ⟨insert⟩

instance (α : Type*) : Adjoin α (List α) := ⟨List.cons⟩

instance (α : Type*) : Adjoin α (Multiset α) := ⟨Multiset.cons⟩

instance (α : Type*) [DecidableEq α] : Adjoin α (Finset α) := ⟨insert⟩

class Context (Elem : outParam Type*) (Coll : Type*) extends
    Membership Elem Coll, HasSubset Coll, EmptyCollection Coll, Adjoin Elem Coll where
  subset_iff {a b : Coll} : a ⊆ b ↔ ∀ x ∈ a, x ∈ b
  not_mem_empty (x : Elem) : ¬x ∈ (∅ : Coll)
  mem_cons_iff {x z : Elem} {a : Coll} : x ∈ adjoin z a ↔ x = z ∨ x ∈ a

attribute [simp] Context.not_mem_empty Context.mem_cons_iff

attribute [grind .] Context.not_mem_empty

attribute [scoped grind =] Context.subset_iff Context.mem_cons_iff

class ExContext (Elem : outParam Type*) (Coll : Type*) extends
    Context Elem Coll where
  extend : Coll → Coll → Coll
  mem_extend_iff {a b : Coll} {x : Elem} : x ∈ extend a b ↔ x ∈ a ∨ x ∈ b

attribute [simp, grind =] ExContext.mem_extend_iff

scoped infixl:65 " ⊎ " => ExContext.extend

instance Set.context : ExContext α (Set α) where
  subset_iff := iff_of_eq Set.subset_def
  not_mem_empty := by simp
  mem_cons_iff := by simp [Adjoin.adjoin]
  extend := Set.union
  mem_extend_iff := Set.mem_union ..

instance List.context : ExContext α (List α) where
  subset_iff := List.subset_def
  not_mem_empty := by simp
  mem_cons_iff := by simp [Adjoin.adjoin]
  extend := List.append
  mem_extend_iff := List.mem_append

instance Multiset.context : ExContext α (Multiset α) where
  subset_iff := Multiset.subset_iff
  not_mem_empty := by simp
  mem_cons_iff := by simp [Adjoin.adjoin]
  extend := Multiset.add
  mem_extend_iff := Multiset.mem_add

instance Finset.context [DecidableEq α] : ExContext α (Finset α) where
  subset_iff := Finset.subset_iff
  not_mem_empty := by simp
  mem_cons_iff := by simp [Adjoin.adjoin]
  extend := (· ∪ ·)
  mem_extend_iff := Finset.mem_union

namespace Context

variable {Elem Coll : Type*} [Context Elem Coll]

instance : Singleton Elem Coll where
  singleton x := adjoin x ∅

@[scoped grind .]
lemma empty_subset {a : Coll} : ∅ ⊆ a := subset_iff.mpr (by grind)

@[scoped grind →]
lemma mem_of_mem {a b : Coll} (h : a ⊆ b) {x : Elem} : x ∈ a → x ∈ b := subset_iff.mp h x

@[scoped grind .]
lemma subset_adjoin (a : Coll) (x : Elem) : a ⊆ adjoin x a := subset_iff.mpr (by grind)

@[simp, scoped grind =]
lemma mem_singleton_iff (x y : Elem) : y ∈ ({x} : Coll) ↔ y = x := by
  simp [Singleton.singleton]

@[simp, scoped grind .]
lemma subset_refl (a : Coll) : a ⊆ a := by grind

@[grind <=]
lemma subset_trans (a b c : Coll) : a ⊆ b → b ⊆ c → a ⊆ c := by grind

def ExtEq (a b : Coll) : Prop := ∀ x, x ∈ a ↔ x ∈ b

instance (Elem Coll : Type*) [Context Elem Coll] : Setoid Coll where
  r := ExtEq
  iseqv := by constructor <;> grind [ExtEq]

@[grind =]
lemma extEq_def {a b : Coll} : a ≈ b ↔ ∀ x, x ∈ a ↔ x ∈ b := Iff.rfl

@[grind .]
lemma ExtEq.symm {a b : Coll} (h : a ≈ b) : b ≈ a := by grind

@[grind .]
lemma ExtEq.trans {a b c : Coll} (h : a ≈ b) (h' : b ≈ c) : a ≈ c := by grind

@[scoped grind ., grind =>]
lemma ExtEq.mem_iff_mem {a b : Coll} {x : Elem} (h : a ≈ b) : x ∈ a ↔ x ∈ b := h x

@[scoped grind →]
lemma ExtEq.subset {a b : Coll} (h : a ≈ b) : a ⊆ b := by grind

@[scoped grind →]
lemma ExtEq.supset {a b : Coll} (h : a ≈ b) : b ⊆ a := by grind

@[scoped grind =_]
lemma extEq_iff_subset_supset {a b : Coll} : a ≈ b ↔ a ⊆ b ∧ b ⊆ a := by grind

@[scoped grind =]
lemma adjoin_comm {a : Coll} {x y : Elem} : adjoin x (adjoin y a) ≈ adjoin y (adjoin x a) := by
  grind

@[scoped grind .]
lemma adjoin_congr {a b : Coll} {x : Elem} (h : a ≈ b) : adjoin x a ≈ adjoin x b := by grind

def toSet (a : Coll) : Set Elem := {x | x ∈ a}

@[simp, scoped grind =]
lemma mem_toSet {a : Coll} {x : Elem} : x ∈ toSet a ↔ x ∈ a := Iff.rfl

@[simp, scoped grind =]
lemma toSet_subset_toSet {a b : Coll} : toSet a ⊆ toSet b ↔ a ⊆ b := by
  rw [subset_iff, subset_iff]
  rfl

@[simp, scoped grind =]
lemma toSet_eq_toSet {a b : Coll} : toSet a = toSet b ↔ a ≈ b := by
  rw [Set.ext_iff]
  rfl

@[simp, grind =]
lemma toSet_adjoin {a : Coll} {x : Elem} : toSet (adjoin x a) = insert x (toSet a) := by
  ext y; simp

end Context

open Context

lemma Set.toSet_eq (s : Set α) : toSet s = s := rfl

namespace ExContext

variable {Elem Coll : Type*} [ExContext Elem Coll]

@[scoped grind! =>] lemma mem_extend_left (a b : Coll) (x : Elem) (hx : x ∈ a) :
    x ∈ a ⊎ b := mem_extend_iff.mpr (Or.inl hx)

@[scoped grind! =>] lemma mem_extend_right (a b : Coll) (x : Elem) (hx : x ∈ b) :
    x ∈ a ⊎ b := mem_extend_iff.mpr (Or.inr hx)

@[scoped grind .] lemma subset_extend_left (a b : Coll) : a ⊆ a ⊎ b :=
  Context.subset_iff.mpr (mem_extend_left a b)

@[scoped grind .] lemma subset_extend_right (a b : Coll) : b ⊆ a ⊎ b :=
  Context.subset_iff.mpr (mem_extend_right a b)

@[scoped grind =]
lemma extend_subset (a b c : Coll) : a ⊎ b ⊆ c ↔ a ⊆ c ∧ b ⊆ c := by grind

@[scoped grind! .]
lemma extend_empty (a : Coll) : (a ⊎ ∅) ≈ a := by grind

@[scoped grind! .]
lemma empty_extend (a : Coll) : ∅ ⊎ a ≈ a := by grind

@[scoped grind =]
lemma extend_symm (a b : Coll) : a ⊎ b ≈ b ⊎ a := by grind

@[scoped grind =]
lemma extend_extend (a b c : Coll) : a ⊎ (b ⊎ c) ≈ a ⊎ b ⊎ c := by grind

@[scoped grind! .]
lemma extend_self (a : Coll) : a ⊎ a ≈ a := by grind

@[scoped grind .]
lemma extend_congr {a a' b b' : Coll} (ha : a ≈ a') (hb : b ≈ b') : a ⊎ b ≈ a' ⊎ b' := by grind

@[scoped grind =]
lemma extend_singleton (a : Coll) (x : Elem) : a ⊎ {x} ≈ adjoin x a := by grind

@[scoped grind =]
lemma singleton_extend (a : Coll) (x : Elem) : {x} ⊎ a ≈ adjoin x a := by grind

end ExContext

end Cslib

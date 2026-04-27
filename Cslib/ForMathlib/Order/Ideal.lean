/-
Copyright (c) 2026 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
module

public import Cslib.Init
public import Mathlib.Order.Ideal
public import Mathlib.Order.RelIso.Set

@[expose] public section

namespace Order.Ideal

variable {α β : Type*} [LE α] [LE β]

@[simp]
lemma mem_coe (x : α) (I : Ideal α) : x ∈ (I : Set α) ↔ x ∈ I := Iff.rfl

def map {α β : Type*} [Preorder α] [Preorder β] (f : α ≃o β) (I : Ideal α) : Ideal β :=
  ⟨I.toLowerSet.map f, I.nonempty.image f, RelHomClass.directedOn I.directed⟩

end Order.Ideal

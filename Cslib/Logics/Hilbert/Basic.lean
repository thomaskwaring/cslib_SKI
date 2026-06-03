/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Cslib.Foundations.Logic.Axioms
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Data.Set.Insert

@[expose] public section

namespace Cslib.Logic

variable {α : Type*} [HasImpl α]

open InferenceSystem

namespace Hilbert

abbrev Theory (α : Type*) := Set α

inductive Theory.Derivation (T : Theory α) : α → Type _ where
  | ax {A : α} (hA : A ∈ T) : T.Derivation A
  | mp {A B : α} : T.Derivation (A → B) → T.Derivation A → T.Derivation B

open Theory

scoped notation D " ⋆ " E => Theory.Derivation.mp D E

variable {T : Theory α} {A B C : α}

instance [HasImpl α] (T : Theory α) : InferenceSystem T α where
  derivation A := T.Derivation A

class HasS (T : Theory α) where
  derS (A B C : α) : T⇓((A → B → C) → (A → B) → A → C)

class HasK (T : Theory α) where
  derK (A B : α) : T⇓(A → B → A)

class HasI (T : Theory α) where
  derI (A : α) : T⇓(A → A)

open HasS HasK HasI

instance [HasImpl α] (T : Theory α) [HasS T] [HasK T] : HasI T where
  derI A := (derS A (A → A) A ⋆ derK A (A → A)) ⋆ derK A A

class Deductive (T : Theory α) where
  derImplOfDerInsert {A B : α} : (insert A T : Theory α)⇓B → T⇓(A → B)

def Theory.Derivation.absSK [HasS T] [HasK T] [DecidableEq α] {A B : α} :
    (insert A T : Theory α)⇓B → T⇓(A → B)
  | ax hB => if heq : B = A then heq ▸ (derI B) else
      derK B A ⋆ (.ax <| T.mem_of_mem_insert_of_ne hB heq)
  | mp D E =>  (derS A _ B ⋆ D.absSK) ⋆ E.absSK

instance [HasS T] [HasK T] [DecidableEq α] : Deductive T where
  derImplOfDerInsert := Derivation.absSK

end Hilbert

end Cslib.Logic

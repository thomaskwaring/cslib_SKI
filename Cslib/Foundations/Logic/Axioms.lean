/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Cslib.Foundations.Logic.Operators.Impl
public import Cslib.Foundations.Logic.Operators.Not
public import Cslib.Foundations.Logic.InferenceSystem
public import Mathlib.Order.TypeTags

@[expose] public section

namespace Cslib.Logic

open InferenceSystem

variable {S α : Type*}

class HasMP (S α : Type*) [HasImpl α] [InferenceSystem S α] where
  mp {A B : α} : S⇓(A → B) → S⇓A → S⇓B

class HasEFQ (S α : Type*) [HasImpl α] [Bot α] [InferenceSystem S α] where
  derEFQ (A : α) : S⇓(⊥ → A)

class HasDNE (S α : Type*) [HasImpl α] [HasNot α] [InferenceSystem S α] where
  derDNE (A : α) : S⇓(¬¬A → A)

end Cslib.Logic

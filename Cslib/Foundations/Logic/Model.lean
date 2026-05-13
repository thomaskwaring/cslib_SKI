/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Cslib.Foundations.Logic.Connectives
public import Cslib.Foundations.Logic.InferenceSystem
public import Cslib.Logics.Modal.Basic

public section

namespace Cslib.Logic

/-- Objects of type `β` carry a forcing relation with the proposition type `α`. -/
class ModelClass (α : outParam (Type*)) (β : Type*) where
  /-- `Forces b a` has the intended semantics "`a` is valid in the model `b`". -/
  Forces : β → α → Prop

scoped notation "⊨[" b "] " a => ModelClass.Forces b a

/-- Objects of type `β` carry a forcing relation worlds of type `γ` and the proposition type `α`. -/
class ParamModelClass (α : outParam (Type*)) (β : Type*) where
  Param : β → Type*
  /-- Forcing relation associated to each parameter. -/
  ForcesAt (b : β) : (Param b) → α → Prop

scoped notation w " ⊨[" b "] " a => ParamModelClass.ForcesAt b w a

instance ParamModelClass.toModelClass {α β : Type*} [ParamModelClass α β] : ModelClass α β where
  Forces M A := ∀ w : ParamModelClass.Param M, w ⊨[M] A

/-- Bundled interpretation function. -/
structure Interp (α β : Type*) where
  /-- Interpret a proposition in a model. -/
  interp : α → β

/-- An `InterpModel` consists of an interpretation function, and a set specifying which
  interpretations are considered valid. -/
structure InterpModel (α β : Type*) extends Interp α β where
  /-- The set of valid interpretations. -/
  filter : Set β

instance {α β : Type*} : ModelClass α (InterpModel α β) where
  Forces M a := M.interp a ∈ M.filter

namespace Interp

class AlgebraicAnd {α β : Type*} [HasAnd α] [Min β] (M : Interp α β) where
  interp_and_eq (x y : α) : M.interp (x ∧ y) = M.interp x ⊓ M.interp y

class AlgebraicOr {α β : Type*} [HasOr α] [Max β] (M : Interp α β) where
  interp_or_eq (x y : α) : M.interp (x ∨ y) = M.interp x ⊔ M.interp y

class AlgebraicImpl {α β : Type*} [HasImpl α] [HImp β] (M : Interp α β) where
  interp_impl_eq (x y : α) : M.interp (x → y) = M.interp x ⇨ M.interp y

class AlgebraicNot {α β : Type*} [HasNot α] [Compl β] (M : Interp α β) where
  interp_not_eq (x : α) : M.interp (¬ x) = (M.interp x)ᶜ

end Interp

open ModelClass ParamModelClass InferenceSystem

def Sound {α β S : Type*} [ModelClass α β] [InferenceSystem S α] : Prop :=
  ∀ (A : α) (b : β) , DerivableIn S A → ⊨[b] A

def Complete {α β S : Type*} [ModelClass α β] [InferenceSystem S α] : Prop :=
  ∀ A : α, (∀ b : β, ⊨[b] A) → DerivableIn S A

def ParamModelClass.theory {α β : Type*} [ParamModelClass α β] {M : β} (w : Param M) : Set α :=
  {A : α | w ⊨[M] A}

def ModelClass.logic {α β : Type*} [ModelClass α β] (S : Set β) : Set α := {A | ∀ b ∈ S, ⊨[b] A}

namespace Modal

structure BundledModel (Atom : Type*) where
  World : Type*
  model : Model World Atom

def Model.toBundledModel {World Atom : Type*} (M : Model World Atom) : BundledModel Atom :=
  {World := World, model := M}

instance {Atom : Type*} : ParamModelClass (Proposition Atom) (BundledModel Atom) where
  Param M := M.World
  ForcesAt M w A := Satisfies M.model w A

example {World Atom : Type*} (S : Set (Model World Atom)) :
    logic S = ModelClass.logic (Model.toBundledModel '' S) := by
  simp [ModelClass.logic]
  rfl

end Modal

end Cslib.Logic

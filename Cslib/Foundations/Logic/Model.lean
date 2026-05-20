/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Cslib.Foundations.Logic.Connectives
public import Cslib.Foundations.Logic.InferenceSystem
public import Cslib.Logics.Modal.Basic
public import Cslib.Logics.Propositional.NaturalDeduction.Basic

/-! # Semantics for logical systems -/

public section

namespace Cslib.Logic

/-- Objects of type `β` carry a forcing relation with the proposition type `α`. -/
class ModelClass (α : outParam Type*) (β : Type*) where
  /-- `Forces b a` has the intended semantics "`a` is valid in the model `b`". -/
  Forces : β → α → Prop

scoped notation "⊨[" b "] " a => ModelClass.Forces b a

/-- Objects of type `β` carry a forcing relation worlds of type `γ` and the proposition type `α`. -/
class ParamModelClass (α : outParam Type*) (β : Type*) where
  Param : β → Type*
  /-- Forcing relation associated to each parameter. -/
  ForcesAt (b : β) : (Param b) → α → Prop

scoped notation w " ⊨[" b "] " a => ParamModelClass.ForcesAt b w a

instance ParamModelClass.toModelClass {α β : Type*} [ParamModelClass α β] : ModelClass α β where
  Forces M A := ∀ w : ParamModelClass.Param M, w ⊨[M] A

/-- Bundled interpretation function. -/
class HasInterp (α : outParam Type*) (β : Type*) where
  /-- Type carrying interpretation. -/
  Ground : β → Type*
  /-- Interpret a proposition in a model. -/
  interp : (b : β) → α → Ground b

/-- An `InterpModel` consists of an interpretation function, and a set specifying which
  interpretations are considered valid. -/
class InterpModelClass (α : outParam (Type*)) (β : Type*) extends HasInterp α β where
  /-- The set of valid interpretations. -/
  filter (b : β) : Set (Ground b)

instance InterpModelClass.instModelClass {α β : Type*} [InterpModelClass α β] : ModelClass α β where
  Forces b a := HasInterp.interp b a ∈ filter b

namespace HasInterp

class AlgebraicAnd (α β : Type*) [HasInterp α β] [HasAnd α] [∀ b : β, Min (Ground b)] where
  interp_and_eq (M : β) (x y : α) : interp M (x ∧ y) = interp M x ⊓ interp M y

class AlgebraicOr (α β : Type*) [HasInterp α β] [HasOr α] [∀ b : β, Max (Ground b)] where
  interp_or_eq (M : β) (x y : α) : interp M (x ∨ y) = interp M x ⊔ interp M y

class AlgebraicImpl (α β : Type*) [HasInterp α β] [HasImpl α] [∀ b : β, HImp (Ground b)] where
  interp_impl_eq (M : β) (x y : α) : interp M (x → y) = interp M x ⇨ interp M y

class AlgebraicNot (α β : Type*) [HasInterp α β] [HasNot α] [∀ b : β, Compl (Ground b)] where
  interp_not_eq (M : β) (x y : α) : interp M (¬ x) = (interp M x)ᶜ

end HasInterp

open ModelClass ParamModelClass InferenceSystem

variable {α β T} [ModelClass α β] [InferenceSystem T α]

def SoundFor (α β T) [ModelClass α β] [InferenceSystem T α] (S : Set β) : Prop :=
  ∀ (A : α), DerivableIn T A → ∀ M ∈ S, ⊨[M] A

lemma SoundFor.subset {S S' : Set β} (hS : S ⊆ S') : SoundFor α β T S' → SoundFor α β T S :=
  fun h A hA M hM => h A hA M (hS hM)

def CompleteFor (α β T : Type*) [ModelClass α β] [InferenceSystem T α] (S : Set β) : Prop :=
  ∀ A : α, (∀ M ∈ S, ⊨[M] A) → DerivableIn T A

lemma CompleteFor.supset {S S' : Set β} (hS : S ⊆ S') :
    CompleteFor α β T S → CompleteFor α β T S' := fun h A hA => h A (fun M hM => hA M (hS hM))

def IsCompleteModel (α β T) [ModelClass α β] [InferenceSystem T α] (M : β) : Prop :=
  ∀ (A : α), (⊨[M] A) → DerivableIn T A

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

example {World Atom : Type*} (m : Model World Atom) (w : World) :
    theory m w = ParamModelClass.theory (M := m.toBundledModel) w := by
  simp [theory, ParamModelClass.theory]
  rfl

end Modal

namespace PL

variable {Atom : Type*}

instance : HasAnd (Proposition Atom) := ⟨Proposition.and⟩
instance : HasOr (Proposition Atom) := ⟨Proposition.or⟩
instance : HasImpl (Proposition Atom) := ⟨Proposition.impl⟩
instance [Bot Atom] : HasNot (Proposition Atom) := ⟨Proposition.neg⟩

structure HeytingModel (Atom : Type*) where
  H : Type*
  [inst : GeneralizedHeytingAlgebra H]
  v : Atom → H

instance (M : HeytingModel Atom) : GeneralizedHeytingAlgebra M.H := M.inst

def HeytingModel.interp (M : HeytingModel Atom) : Proposition Atom → M.H
  | Proposition.atom x => M.v x
  | Proposition.and A B => M.interp A ⊓ M.interp B
  | Proposition.or A B => M.interp A ⊔ M.interp B
  | Proposition.impl A B => M.interp A ⇨ M.interp B

instance : InterpModelClass (Proposition Atom) (HeytingModel Atom) where
  Ground M := M.H
  interp := HeytingModel.interp
  filter _ := {⊤}

instance (M : HeytingModel Atom) : GeneralizedHeytingAlgebra (HasInterp.Ground M) := M.inst

instance : HasInterp.AlgebraicAnd (Proposition Atom) (HeytingModel Atom) where
  interp_and_eq _ _ _ := rfl

instance : HasInterp.AlgebraicOr (Proposition Atom) (HeytingModel Atom) where
  interp_or_eq _ _ _ := rfl

instance : HasInterp.AlgebraicImpl (Proposition Atom) (HeytingModel Atom) where
  interp_impl_eq _ _ _ := rfl

theorem HeytingModel.sound [DecidableEq Atom] {T : Theory Atom} :
    SoundFor (Proposition Atom) (HeytingModel Atom) T {M | ∀ A ∈ T, interp M A = ⊤} :=
  sorry -- i have this in a branch

def Theory.lindenbaum [DecidableEq Atom] (T : Theory Atom) : HeytingModel Atom :=
  sorry -- usual Heyting-algebra of propositions modulo equivalence

theorem Theory.lindenbaum_complete [DecidableEq Atom] {T : Theory Atom} :
    IsCompleteModel (Proposition Atom) (HeytingModel Atom) T T.lindenbaum :=
  sorry -- also in a branch

end PL

end Cslib.Logic

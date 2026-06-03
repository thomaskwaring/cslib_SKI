/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Cslib.Foundations.Logic.Axioms
public import Cslib.Foundations.Data.Context
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace Cslib.Logic

open Set Context ExContext

universe u v w

class ContextualInferenceSystem (S α β : Type*) where
  derivation (Γ : β) (A : α) : Sort v

scoped notation Γ " ⊢[" S "] " A => ContextualInferenceSystem.derivation S Γ A

class HasAss (S α β : Type*) [ContextualInferenceSystem S α β] [Context α β] where
  ass {Γ : β} {A : α} (hA : A ∈ Γ) : Γ ⊢[S] A

class HasWk (S α β : Type*) [ContextualInferenceSystem S α β] [Context α β] where
  derOfSubset {Γ Δ : β} {A : α} (h : Γ ⊆ Δ) : (Γ ⊢[S] A) → Δ ⊢[S] A

class Extensional (S α β : Type*) [ContextualInferenceSystem S α β] [Context α β] where
  derOfEquiv {Γ Δ : β} {A : α} (h : Γ ≈ Δ) : (Γ ⊢[S] A) → Δ ⊢[S] A

class HasAddMP (S α β : Type*) [ContextualInferenceSystem S α β] [Context α β] [HasImpl α] where
  mp {Γ : β} {A B : α} : (Γ ⊢[S] A → B) → (Γ ⊢[S] A) →  Γ ⊢[S] B

class HasMultMP (S α β : Type*) [ContextualInferenceSystem S α β] [ExContext α β] [HasImpl α] where
  mp {Γ Δ : β} {A B : α} : (Γ ⊢[S] A → B) → (Δ ⊢[S] A) → (Γ ⊎ Δ) ⊢[S] B

instance (S α β : Type*) [ContextualInferenceSystem S α β] [ExContext α β] [HasImpl α]
    [HasAddMP S α β] [HasWk S α β] : HasMultMP S α β where
  mp D E := HasAddMP.mp
    (HasWk.derOfSubset (ExContext.subset_extend_left ..) D)
    (HasWk.derOfSubset (ExContext.subset_extend_right ..) E)

@[reducible]
def instAddMPOfMulMP (S α β : Type*) [ContextualInferenceSystem S α β] [ExContext α β] [HasImpl α]
    [HasMultMP S α β] [Extensional S α β] : HasAddMP S α β where
  mp D E := Extensional.derOfEquiv (ExContext.extend_self _) (HasMultMP.mp D E)

instance (S α β : Type*) [ContextualInferenceSystem S α β] [Context α β] [HasWk S α β] :
    Extensional S α β where
  derOfEquiv h := HasWk.derOfSubset h.subset

open ContextualInferenceSystem HasAss HasWk HasAddMP

inductive axAssDer {α β : Type*} [HasImpl α] [Context α β] (T : Set α) :
    β → α → Type _ where
  | ax {Γ : β} {A : α} (hA : A ∈ T) : axAssDer T Γ A
  | ass {Γ : β} {A : α} (hA : A ∈ Γ) : axAssDer T Γ A
  | mp {Γ : β} {A B : α} : axAssDer T Γ (A → B) → axAssDer T Γ A → axAssDer T Γ B

variable {S α β : Type*} [ContextualInferenceSystem S α β] [Context α β] [HasImpl α] {T : Set α}

@[match_pattern]
def axAssDer.mp' {Γ : β} (A B : α) : axAssDer T Γ (A → B) → axAssDer T Γ A → axAssDer T Γ B :=
  axAssDer.mp

opaque Hilbert (T : Set α) : Type _ := T

scoped prefix:max "𝓗" => Hilbert

instance (T : Set α) : ContextualInferenceSystem (𝓗 T) α β where
  derivation := axAssDer T

instance : HasAss (𝓗 T) α β where ass := axAssDer.ass

instance : HasAddMP (𝓗 T) α β where mp := axAssDer.mp

def axAssDer.weak {Γ Δ : β} {A : α} (h : Γ ⊆ Δ) : (Γ ⊢[𝓗 T] A) → Δ ⊢[𝓗 T] A
  | ax hA => ax hA
  | ass hA => ass (mem_of_mem h hA)
  | mp D E => (D.weak h).mp (E.weak h)

instance : HasWk (𝓗 T) α β where derOfSubset := axAssDer.weak

class Deductive (S α β : Type*) [ContextualInferenceSystem S α β] [Context α β] [HasImpl α] where
  derImplOfDerAdjoin {Γ : β} {A B : α} : (adjoin A Γ ⊢[S] B) → Γ ⊢[S] A → B

class HasCut (S α β : Type*) [ContextualInferenceSystem S α β] [ExContext α β] where
  derExtendOfDerOfDer {Γ Δ : β} {A B : α} : (adjoin A Γ ⊢[S] B) → (Δ ⊢[S] A) → (Γ ⊎ Δ) ⊢[S] B

instance (S α β : Type*) [ContextualInferenceSystem S α β] [ExContext α β] [HasImpl α]
    [Deductive S α β] [HasMultMP S α β] : HasCut S α β where
  derExtendOfDerOfDer D E := HasMultMP.mp (Deductive.derImplOfDerAdjoin D) E

def HasCut.cutSingleL {S α β : Type*} [ContextualInferenceSystem S α β] [ExContext α β]
    [HasCut S α β] [Extensional S α β] {Γ : β} {A B : α}
    (D : ({A} : β) ⊢[S] B) (E : Γ ⊢[S] A) : Γ ⊢[S] B :=
  Extensional.derOfEquiv (empty_extend Γ) <| HasCut.derExtendOfDerOfDer D E

def HasCut.cutSingleR {S α β : Type*} [ContextualInferenceSystem S α β] [ExContext α β]
    [HasCut S α β] [Extensional S α β] {Γ : β} {A B C : α}
    (D : adjoin B Γ ⊢[S] C) (E : ({A} : β) ⊢[S] B) : adjoin A Γ ⊢[S] C :=
  Extensional.derOfEquiv (extend_singleton Γ A) <| HasCut.derExtendOfDerOfDer D E

class HasS (S α β : Type*) [ContextualInferenceSystem S α β] [Context α β] [HasImpl α] where
  derS {Γ : β} (A B C : α) : Γ ⊢[S] (A → B → C) → (A → B) → A → C

class HasK (S α β : Type*) [ContextualInferenceSystem S α β] [Context α β] [HasImpl α] where
  derK {Γ : β} (A B : α) : Γ ⊢[S] A → B → A

class HasI (S α β : Type*) [ContextualInferenceSystem S α β] [Context α β] [HasImpl α] where
  derI {Γ : β} (A : α) : Γ ⊢[S] A → A

open Deductive HasS HasK HasI HasWk HasAddMP

instance [HasS S α β] [HasK S α β] [HasAddMP S α β] : HasI S α β where
  derI A := mp (mp (derS ..) <| derK ..) (derK A A)

def derImplOfDer [Deductive S α β] [HasWk S α β] {Γ : β} {A : α} (B : α) (D : Γ ⊢[S] A) :
    Γ ⊢[S] B → A := derImplOfDerAdjoin (derOfSubset (subset_adjoin Γ B) D)

def axAssDer.absSK [HasS (𝓗 T) α β] [HasK (𝓗 T) α β] [DecidableEq α] {Γ : β} {A B : α} :
    (adjoin A Γ ⊢[𝓗 T] B) → Γ ⊢[𝓗 T] A → B
  | ax hA => (derK B A : Γ ⊢[𝓗 T] B → A → B).mp (ax hA)
  | ass hA =>
      if heq : A = B then heq ▸ derI A else (derK B A : Γ ⊢[𝓗 T] B → A → B).mp (ass <| by grind)
  | mp' B C D E => (derS A B C : Γ ⊢[𝓗 T] _).mp D.absSK |>.mp E.absSK

instance [HasS (𝓗 T) α β] [HasK (𝓗 T) α β] [DecidableEq α] : Deductive (𝓗 T) α β where
  derImplOfDerAdjoin := axAssDer.absSK

class HasBotImpl (S α β : Type*) [ContextualInferenceSystem S α β] [Context α β] [HasImpl α]
    [Bot α] where
  botImpl (A : α) : (∅ : β) ⊢[S] ⊥ → A

def HasBotImpl.botImpl' [HasImpl α] [Bot α] [HasBotImpl S α β] [HasWk S α β] (Γ : β) (A : α) :
  Γ ⊢[S] ⊥ → A := derOfSubset empty_subset (botImpl A)

def HasBotImpl.derOfDerBot [HasImpl α] [Bot α] [HasBotImpl S α β] [HasWk S α β] [HasAddMP S α β]
    {Γ : β} (A : α) : (Γ ⊢[S] (⊥ : α)) → Γ ⊢[S] A := mp (botImpl' Γ A)

class HasDNImpl (S α β : Type*) [ContextualInferenceSystem S α β] [Context α β] [HasImpl α]
    [HasNot α] where
  dnImpl (A : α) : (∅ : β) ⊢[S] ¬¬A → A

def HasDNImpl.dnImpl' [HasNot α] [HasDNImpl S α β] [HasWk S α β] (Γ : β) (A : α) :
    Γ ⊢[S] ¬¬A → A := HasWk.derOfSubset empty_subset (dnImpl A)

def HasDNImpl.derOfDerDN [HasNot α] [HasDNImpl S α β] [HasAddMP S α β] [HasWk S α β] {Γ : β}
    {A : α} : (Γ ⊢[S] ¬¬A) → Γ ⊢[S] A := mp (dnImpl' Γ A)

def HasDNImpl.notE [Bot α] [ImplNot α] [HasDNImpl S α β] [Deductive S α β] [HasWk S α β]
    [HasAddMP S α β] {Γ : β} {A : α} (D : adjoin (¬ A) Γ ⊢[S] (⊥ : α)) : Γ ⊢[S] A := by
  apply derOfDerDN
  rw [ImplNot.not_eq_impl_bot]
  exact derImplOfDerAdjoin D

instance [Bot α] [ImplNot α] [HasDNImpl S α β] [Deductive S α β] [HasWk S α β] [HasAddMP S α β]
    [HasAss S α β] : HasBotImpl S α β where
  botImpl A := derImplOfDerAdjoin <| HasDNImpl.notE <| HasAss.ass <| by grind

def HasDNImpl.pierce [Bot α] [ImplNot α] [HasDNImpl S α β] [Deductive S α β] [HasWk S α β]
    [HasAddMP S α β] [HasAss S α β] {Γ : β} {A B : α} : Γ ⊢[S] ((A → B) → A) → A := by
  apply derImplOfDerAdjoin; apply notE
  rw [ImplNot.not_eq_impl_bot]
  apply HasAddMP.mp (A := A) (ass <| by grind)
  apply HasAddMP.mp (A := A → B) (ass <| by grind)
  apply derImplOfDerAdjoin; apply HasBotImpl.derOfDerBot
  apply HasAddMP.mp (A := A) <;> exact ass <| by grind

structure ContextualInferenceSystem.Equivalence {α : Type*} (S β : Type*) [Context α β]
    [ContextualInferenceSystem S α β] (A B : α) where
  fwd : ({A} : β) ⊢[S] B
  bwd : ({B} : β) ⊢[S] A

scoped notation A " ≡[" S "," β "] " B => ContextualInferenceSystem.Equivalence S β A B

namespace ContextualInferenceSystem.Equivalence

variable {S α β : Type*} [ContextualInferenceSystem S α β]

def symm [Context α β] {A B : α} (e : A ≡[S,β] B) : B ≡[S,β] A where
  fwd := e.bwd
  bwd := e.fwd

def mapConcl [ExContext α β] [HasCut S α β] [Extensional S α β] {Γ : β} {A B : α} (e : A ≡[S,β] B)
    (D : Γ ⊢[S] A) : Γ ⊢[S] B := HasCut.cutSingleL e.fwd D

def mapHyp [ExContext α β] [HasCut S α β] [Extensional S α β] {Γ : β} {A B C : α} (e : A ≡[S,β] B)
    (D : adjoin A Γ ⊢[S] C) : adjoin B Γ ⊢[S] C := HasCut.cutSingleR D e.bwd

def trans [ExContext α β] [HasCut S α β] [Extensional S α β] {A B C : α} (e : A ≡[S,β] B)
    (e' : B ≡[S,β] C) : A ≡[S,β] C where
  fwd := HasCut.cutSingleL e'.fwd e.fwd
  bwd := HasCut.cutSingleL e.bwd e'.bwd

end ContextualInferenceSystem.Equivalence

end Cslib.Logic

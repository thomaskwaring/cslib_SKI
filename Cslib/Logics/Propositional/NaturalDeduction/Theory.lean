/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
module

public import Cslib.Logics.Propositional.NaturalDeduction.Basic

/-! # Results on propositional theories -/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Proposition Theory InferenceSystem DerivableIn Derivation IsIntuitionistic IsClassical

variable {Atom : Type u} [DecidableEq Atom] [Bot Atom]

namespace Theory

protected structure Embedding (T T' : Theory Atom) where
  derOfMem {A : Proposition Atom} (hA : A ∈ T) : T'⇓A

class Embeds (T T' : Theory Atom) where
  emb : T.Embedding T'

open Embedding Embeds

variable {T T' : Theory Atom}

def Embedding.ofSubset (h : T ⊆ T') : T.Embedding T' where
  derOfMem hA := ax (h hA)

instance Embeds.ofSubset (h : T ⊆ T') : T.Embeds T' where
  emb := Embedding.ofSubset h

def Derivation.mapEmbedding (emb : T.Embedding T') {Γ : Ctx Atom} {A : Proposition Atom} :
    T.Derivation Γ A → T'.Derivation Γ A
  | ax hA => (emb.derOfMem hA).weak_ctx (Finset.empty_subset Γ)
  | ass hA => ass hA
  | andI D E => andI (D.mapEmbedding emb) (E.mapEmbedding emb)
  | andE₁ D => andE₁ (D.mapEmbedding emb)
  | andE₂ D => andE₂ (D.mapEmbedding emb)
  | orI₁ D => orI₁ (D.mapEmbedding emb)
  | orI₂ D => orI₂ (D.mapEmbedding emb)
  | orE D DA DB => orE (D.mapEmbedding emb) (DA.mapEmbedding emb) (DB.mapEmbedding emb)
  | implI _ D => implI _ (D.mapEmbedding emb)
  | implE D E => implE (D.mapEmbedding emb) (E.mapEmbedding emb)

def Derivation.mapEmbedding' [T.Embeds T'] {Γ : Ctx Atom} {A : Proposition Atom} :
    T.Derivation Γ A → T'.Derivation Γ A := Derivation.mapEmbedding emb

instance instIsIntuitionisticIPL : IsIntuitionistic Atom (IPL Atom) where
  efq A := ax (efq_mem_ipl A)

@[implicit_reducible]
def instIsIntuitionisticOfEmbedding [IsIntuitionistic Atom T] [inst : T.Embeds T'] :
    IsIntuitionistic Atom T' where
  efq A := (efq A : T⇓(⊥ → A)).mapEmbedding'

instance instIsIntuitionisticOfEmbeddingIPL [(IPL Atom).Embeds T'] :
  IsIntuitionistic Atom T' where
    efq A := (efq A : (IPL Atom)⇓(⊥ → A)).mapEmbedding'

def IsIntuitionistic.efqCtx [IsIntuitionistic Atom T] (Γ : Ctx Atom) (A : Proposition Atom)
    : T⇓(Γ ⊢ ⊥ → A) := (efq A : T⇓(⊥ → A)).weak_ctx (Finset.empty_subset Γ)

def IsIntuitionistic.efqRule [IsIntuitionistic Atom T] (Γ : Ctx Atom) (A : Proposition Atom)
    (D : T⇓(Γ ⊢ ⊥)) : T⇓(Γ ⊢ A) :=
  implE (A := ⊥) (efqCtx Γ A) D

def IsIntuitionistic.contra [IsIntuitionistic Atom T] {Γ : Ctx Atom} (A B : Proposition Atom)
    (hΓ : A ∈ Γ) (hΓ' : (¬A) ∈ Γ) : T⇓(Γ ⊢ B) :=
  efqRule Γ B <| implE (ass hΓ') (ass hΓ)

instance instIsClassicalCPL : IsClassical Atom (CPL Atom) where
  dne A := ax (dne_mem_cpl A)

@[implicit_reducible]
def instIsClassicalOfEmbedding [IsClassical Atom T] [T.Embeds T'] :
    IsClassical Atom T' where
  dne A := (dne A : T⇓(¬¬A → A)).mapEmbedding'

instance instIsClassicalOfEmbeddingCPL [(CPL Atom).Embeds T'] :
    IsClassical Atom T' where
  dne A := (dne A : (CPL Atom)⇓(¬¬A → A)).mapEmbedding'

def LEM (Atom : Type u) [Bot Atom] : Theory Atom := {A ∨ ¬ A | A : Proposition Atom}

omit [DecidableEq Atom] in
lemma lem_mem_lem (A : Proposition Atom) : (A ∨ ¬ A) ∈ LEM Atom := ⟨A, rfl⟩

def Pierce (Atom : Type u) [Bot Atom] : Theory Atom :=
  {((A → B) → A) → A | (A : Proposition Atom) (B : Proposition Atom)}

omit [DecidableEq Atom] in
lemma pierce_mem_pierce (A B : Proposition Atom) : (((A → B) → A) → A) ∈ Pierce Atom := ⟨A, B, rfl⟩

instance instIsClassicalLEM : IsClassical Atom (LEM Atom ∪ IPL Atom : Theory Atom) where
  dne A := by
    have : IsIntuitionistic Atom (LEM Atom ∪ IPL Atom : Theory Atom) :=
      instIsIntuitionisticOfEmbedding (inst := .ofSubset Set.subset_union_right)
    apply implI
    apply orE (ax <| Set.mem_union_left _ <| lem_mem_lem A)
    · exact ass (Finset.mem_insert_self A _)
    · apply contra (¬A) A <;> grind

instance instIsClassicalPierce : IsClassical Atom (Pierce Atom ∪ IPL Atom : Theory Atom) where
  dne A := by
    have : IsIntuitionistic Atom (Pierce Atom ∪ IPL Atom : Theory Atom) :=
      instIsIntuitionisticOfEmbedding (inst := .ofSubset Set.subset_union_right)
    apply implI
    apply implE (A := (A → ⊥) → A) (ax <| Set.mem_union_left _ <| pierce_mem_pierce A ⊥)
    apply implI
    apply contra (¬ A) A <;> grind

end Cslib.Logic.PL.Theory

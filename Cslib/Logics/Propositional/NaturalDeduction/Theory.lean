/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
module

public import Cslib.Logics.Propositional.NaturalDeduction.Lemmas

@[expose] public section

namespace Cslib.Logic.PL.Theory

variable {Atom : Type u} [DecidableEq Atom] {T : Theory Atom}

open Theory Derivation InferenceSystem Proposition Finset

class IsIntuitionisticAtom [Bot Atom] (T : Theory Atom) : Prop where
  efq_atom_mem' (x : Atom) : (⊥ → atom x) ∈ T

omit [DecidableEq Atom] in
lemma efq_atom_mem [Bot Atom] {T : Theory Atom} [IsIntuitionisticAtom T] (x : Atom) :
    (⊥ → atom x) ∈ T := IsIntuitionisticAtom.efq_atom_mem' x

def IPLAtom [Bot Atom] : Theory Atom := {⊥ → atom x | x : Atom}

instance [Bot Atom] : IsIntuitionisticAtom (Atom := Atom) IPLAtom := ⟨fun x => ⟨x, rfl⟩⟩

/-- Extend ex falso quodlibet from atoms to general propositions. -/
def efqOfAtomDerivation [Bot Atom] (Ds : ∀ x, ⇓(⊢[T] ⊥ → atom x)) :
    (A : Proposition Atom) → ⇓(⊢[T] ⊥ → A)
  | atom x => Ds x
  | Proposition.or A B =>
    implI ∅ <| disjI₁ <|
      implE (efqOfAtomDerivation Ds A |>.weak_ctx (empty_subset ..)) (ass <| mem_insert_self ⊥ ∅)
  | Proposition.and A B =>
    implI ∅ <| conjI
      (implE (efqOfAtomDerivation Ds A |>.weak_ctx (empty_subset ..)) (ass <| mem_insert_self ⊥ ∅))
      (implE (efqOfAtomDerivation Ds B |>.weak_ctx (empty_subset ..)) (ass <| mem_insert_self ⊥ ∅))
  | impl A B =>
    implI ∅ <| implI {⊥} <|
      implE (efqOfAtomDerivation Ds B |>.weak_ctx (empty_subset ..)) (ass <| by grind)

def efqOfAtom [Bot Atom] [IsIntuitionisticAtom T] (A : Proposition Atom) : ⇓(⊢[T] ⊥ → A) :=
    efqOfAtomDerivation (ax <| efq_atom_mem ·) A

/-- Embed IPL into an atomically-intuitionistic theory. -/
noncomputable def IPLEmbedOfAtom [Bot Atom] (T : Theory Atom) [IsIntuitionisticAtom T] :
    IPL.Embedding T :=
  fun _ hA => Classical.choose_spec hA ▸ efqOfAtom (Classical.choose hA)

noncomputable def friedmanA' [Bot Atom] :
    (IPLAtom (Atom := Atom)).Extension (MPL (Atom := Atom)) where
  f := (atom · ∨ ⊥)
  emb A hA := by
    have hA := Classical.choose_spec hA
    have hx := Classical.choose_spec hA.1
    rw [←hA.2, ←hx]
    apply implI
    apply disjI₂
    apply disjE (A := ⊥) (B := ⊥) <;> exact (ass <| Finset.mem_insert_self ..)

noncomputable def friedmanA [Bot Atom] :
    (IPL (Atom := Atom)).Extension (MPL (Atom := Atom)) :=
  (IPLEmbedOfAtom IPLAtom).toExtension.comp friedmanA'

end Cslib.Logic.PL.Theory

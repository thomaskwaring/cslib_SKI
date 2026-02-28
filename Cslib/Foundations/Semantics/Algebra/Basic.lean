/-
Copyright (c) 2026 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Cslib.Foundations.Syntax.Term.Basic
public import Mathlib.Data.Setoid.Basic

public section

namespace Cslib

universe u v

class SAlgebra (S : Signature.{v}) (A : Type u) : Type (max (u + 1) (v + 1)) where
  interp (f : S.Sym) : (Fin (S.arity f) → A) → A

namespace SAlgebra

variable {S : Signature} {A B C : Type u} [SAlgebra S A] [SAlgebra S B] [SAlgebra S C]

structure SAlgHom (S : Signature) (A B : Type u) [iA : SAlgebra S A] [iB : SAlgebra S B] where
  toFun : A → B
  map_interp' {f : S.Sym} (xs : Fin (S.arity f) → A) : toFun (interp f xs) = interp f (toFun ∘ xs)

scoped notation A " →[" S "] " B => SAlgHom S A B

namespace SAlgHom

variable {ψ : B →[S] C} {φ : A →[S] B}

instance instFunLike : FunLike (A →[S] B) A B where
  coe := SAlgHom.toFun
  coe_injective' φ ψ h := by cases φ; cases ψ; grind

@[simp]
lemma map_interp (φ : A →[S] B) {f : S.Sym} (xs : Fin (S.arity f) → A) :
    φ (interp f xs) = interp f (φ ∘ xs) := SAlgHom.map_interp' ..

def id (A : Type u) [SAlgebra S A] : A →[S] A where
  toFun x := x
  map_interp' _ := rfl

lemma id_apply (x : A) : @id S A _ x = x := by rfl

def comp (ψ : B →[S] C) (φ : A →[S] B) : A →[S] C where
  toFun := ψ ∘ φ
  map_interp' xs := by simp [Function.comp_assoc]

lemma comp_apply (x : A) : (ψ ∘ φ) x = ψ (φ x) := rfl

-- comp_id, id_comp, etc etc

end SAlgHom

structure SAlgIso (S : Signature) (A B : Type u) [iA : SAlgebra S A] [iB : SAlgebra S B] where
  toHom : A →[S] B
  invHom : B →[S] A
  left_inv : Function.LeftInverse invHom toHom
  right_inv : Function.RightInverse invHom toHom

scoped notation A " ≅[" S "] " B => SAlgIso S A B

-- TODO composition, coercions etc for `SAlgIso`

structure Congruence (S : Signature) (A : Type u) [SAlgebra S A] where
  toRel : A → A → Prop
  iseqv : Equivalence toRel
  map_interp {f : S.Sym} {xs ys : Fin (S.arity f) → A} (hxs : ∀ i, toRel (xs i) (ys i)) :
      toRel (interp f xs) (interp f ys)

namespace Congruence

protected def Setoid (r : Congruence S A) : Setoid A where
  r := r.toRel
  iseqv := r.iseqv

lemma setoid_coe (r : Congruence S A) : (r.Setoid : A → A → Prop) = r.toRel := by
  rw [Setoid.r, Congruence.Setoid]

set_option quotPrecheck false in
scoped notation:max A "⧸" r => Quotient (r : Congruence S A).Setoid

/--
It's possible to make this computable but only because the indexing type `Fin (S.arity f)` is a
Fintype (see `Setoid.piQuotientEquiv`). It would involve some horrible fold though which I can't
bring myself to code. The result `Congruence.quotient_interp_mk_eq` ensures this definition matches
the "real" one.
-/
noncomputable instance instSAlgebraQuotient (r : Congruence S A) :
    SAlgebra S A⧸r where
  interp f ps := Quotient.mk'' (interp f <| fun i => (ps i).out)

lemma interp_def {r : Congruence S A} {f : S.Sym} (ps : Fin (S.arity f) → A⧸r) :
    interp f ps = ⟦interp f <| fun i => (ps i).out⟧ := rfl

theorem quotient_mk_interp_eq (r : Congruence S A) {f : S.Sym} (xs : Fin (S.arity f) → A) :
    Quotient.mk r.Setoid (interp f xs) =
      interp (A := A⧸r) f (Quotient.mk r.Setoid ∘ xs) := by
  symm
  apply Quotient.sound
  apply r.map_interp
  simp_rw [←setoid_coe]
  exact fun i => Quotient.mk_out' (xs i)

def mk_hom (r : Congruence S A) : A →[S] (A⧸r) where
  toFun := Quotient.mk r.Setoid
  map_interp' := r.quotient_mk_interp_eq

lemma mk_hom_surjective (r : Congruence S A) : Function.Surjective r.mk_hom :=
  Quotient.mk_surjective

def ofSAlgHom (φ : SAlgHom S A B) : Congruence S A where
  toRel x y := φ x = φ y
  iseqv := (Setoid.ker φ).iseqv
  map_interp h := by
    rw [φ.map_interp, φ.map_interp]
    congr 1
    ext i
    exact h i

protected def lift {r : Congruence S A} (φ : A →[S] B) (h : ∀ x y : A, r.toRel x y → φ x = φ y) :
    (A⧸r) →[S] B where
  toFun := Quotient.lift φ h
  map_interp' xs := by
    rw [r.interp_def, Quotient.lift_mk, φ.map_interp]
    congr 1
    ext i
    rw [Function.comp_apply, Function.comp_apply, ←Quotient.out_eq (q := xs i), Quotient.lift_mk]
    simp

protected lemma lift_comp_mk {r : Congruence S A} (φ : A →[S] B)
    (h : ∀ x y : A, r.toRel x y → φ x = φ y) : (r.lift φ h).comp r.mk_hom = φ :=
  DFunLike.coe_injective' <| DFunLike.ext'_iff.mp rfl

end Congruence

-- might run into universe issues here?
instance instPiSAlgebra {κ : Type _} (As : κ → Type _) [∀ k, SAlgebra S (As k)] :
    SAlgebra S (Π k, As k) where
  interp f xs k := interp f (fun i => xs i k)

open Term PTree

variable {X : Type u}

instance instSAlgebraTerm (S : Signature) (X : Type u) : SAlgebra S (Term S X) where
  interp f xs := consNodeOfFn f xs

def liftTermAlgebra {A : Type u} [SAlgebra S A] (φ : X → A) (t : Term S X) : A :=
  match t with
  | ⟨leaf x, _⟩ => φ x
  | ⟨node f ts, h⟩ => interp f (fun i => liftTermAlgebra φ h.childTerms[i])
  termination_by t.t.size
  decreasing_by simpa only [WF.childTerms_get_coe] using size_getElem_lt_size ..

def liftTermAlgebraHom {A : Type u} [SAlgebra S A] (φ : X → A) : Term S X →[S] A where
  toFun := liftTermAlgebra φ
  map_interp' xs := by
    simp only [interp, consNodeOfFn_eq, liftTermAlgebra]
    congr; ext i; congr; ext
    rw [WF.childTerms_get_coe]
    simp

def Models (E : Term S X → Term S X → Prop) (A : Type u) [SAlgebra S A] : Prop :=
  ∀ (φ : Term S X →[S] A) (s t : Term S X), E s t → φ s = φ t

def IdentifiedIn (s t : Term S X) (A : Type u) [SAlgebra S A] : Prop :=
  ∀ (φ : Term S X →[S] A), φ s = φ t

notation A " ⊨ " E => Models E A
notation A " ⊨ " s " ≡ " t => IdentifiedIn s t A

def SemanticConsequence (E : Term S X → Term S X → Prop) (s t : Term S X) : Prop :=
  ∀ (A : Type u) [SAlgebra S A], (A ⊨ E) → (A ⊨ s ≡ t)

-- open SemanticConsequence

notation s " ≡[" E "] " t => SemanticConsequence E s t

lemma Models.semanticConsequence (E : Term S X → Term S X → Prop) (A : Type u)
    [SAlgebra S A] (hA : A ⊨ E) : A ⊨ (· ≡[E] ·) := fun φ _ _ hst => hst A hA φ

lemma Models.eq_of_semanticConsequence {E : Term S X → Term S X → Prop} {A : Type u} [SAlgebra S A]
    (hA : A ⊨ E) {s t : Term S X} (hst : s ≡[E] t) (φ : Term S X →[S] A) : φ s = φ t :=
  hst A hA φ

theorem SemanticConsequence.fully_invariant (E : Term S X → Term S X → Prop) (s t : Term S X)
    (h : s ≡[E] t) (φ : Term S X →[S] Term S X) : (φ s) ≡[E] (φ t) :=
  fun _ _ hA ψ => hA.semanticConsequence E _ (ψ.comp φ) s t h

theorem SemanticConsequence.equivalence (E : Term S X → Term S X → Prop) :
    Equivalence (· ≡[E] ·) where
  refl _ _ _ _ _ := rfl
  symm hst _ _ hA φ := (hA.eq_of_semanticConsequence hst φ).symm
  trans hst htu _ _ hA φ :=
    (hA.eq_of_semanticConsequence hst φ).trans (hA.eq_of_semanticConsequence htu φ)

def SemanticConsequence.congruence (E : Term S X → Term S X → Prop) : Congruence S (Term S X) where
  toRel := SemanticConsequence E
  iseqv := SemanticConsequence.equivalence E
  map_interp h A _ hA φ := by
    simp_rw [φ.map_interp]
    congr 1; ext i
    exact hA.eq_of_semanticConsequence (h i) φ

def RewriteEquiv.congruence (E : PTree S.Sym X → PTree S.Sym X → Prop) :
    Congruence S (Term S X) where
  toRel := Function.onFun (RewriteEquiv E) Term.t
  iseqv := Equivalence.comap RewriteEquiv.equivalence t
  map_interp := by
    intro f xs ys h
    simp only [Function.onFun, interp, consNodeOfFn_eq]
    exact RewriteEquiv.nodeClosed (E := E) |>.apply_ofFn f (t ∘ xs) (t ∘ ys) h

private noncomputable def outHom (E : PTree S.Sym X → PTree S.Sym X → Prop)
    (φ : Term S X →[S] Quotient (RewriteEquiv.congruence E).Setoid) : Term S X →[S] Term S X :=
  liftTermAlgebraHom (fun x => (φ <| ⟨leaf x, .leaf_wf⟩).out)

-- private lemma outHom_comp_mk (E : PTree S.Sym X → PTree S.Sym X → Prop)
--     (φ : Term S X →[S] Quotient (RewriteEquiv.congruence E).Setoid) :
--       Quotient.mk (RewriteEquiv.congruence E).Setoid ∘ (outHom E φ) = φ := by

/-- `→` direction amounts to showing the conditions of `RewriteEquiv.minimal`, and `←` to showing
that `RewriteEquiv E` is a `Congruence`, and that `Term S X ⧸ RewriteEquiv E ⊨ E`. -/
proof_wanted BirkoffTheorem (E : PTree S.Sym X → PTree S.Sym X → Prop) (s t : Term S X) :
  RewriteEquiv E s t ↔ s ≡[Function.onFun E Term.t] t

end Cslib.SAlgebra

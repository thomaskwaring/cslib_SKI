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

end Cslib.SAlgebra

/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Cslib.Languages.CombinatoryLogic.Basic
public import Mathlib.Data.PFun

/-! # SKI Realizers of data
-/

@[expose] public section

namespace Cslib.SKI

open Red MRed Relation

/-- Typeclasses for types `α` that can be "realized" by `SKI` terms. We require that realizers lift
along reductions. -/
class Realized (α : Type*) where
  /-- `Realizes x a` denotes that `x` is an `SKI` representation of the lean data `a`. -/
  Realizes' : SKI → α → Prop
  /-- If `y` realizes `a` and `x` reduces to `y`, then `x` realizes `a`. -/
  realizes_left_of_red {x y : SKI} {a : α} : Realizes' y a → x ⭢ y → Realizes' x a

variable {α β γ : Type*} [Realized α] [Realized β] [Realized γ] {x y : SKI}

/-- `Realizes x a` denotes that `x` is an `SKI` representation of the lean data `a`. -/
def Realizes : SKI → α → Prop := Realized.Realizes'

@[inherit_doc] scoped notation x " ⊩ " a:40 => Realizes x a

theorem Realizes.left_of_red {a : α} (hya : y ⊩ a) (hxy : x ⭢ y) : x ⊩ a :=
  Realized.realizes_left_of_red hya hxy

theorem Realizes.left_of_mRed {a : α} (hya : y ⊩ a) (hxy : x ↠ y) : x ⊩ a := by
  induction hxy with
  | refl => exact hya
  | tail _ htr ih => exact ih (hya.left_of_red htr)

open Realized

/-! ### Function types

Realizers for a function type `α → β` are defined by a logical relation: `xf ⊩ f` if for every
`xa ⊩ a`, `xf ⬝ xa ⊩ f a`. We provide realizer interpretations for some basic combinators.
-/

instance : Realized (α → β) where
  Realizes' xf f := ∀ {xa : SKI} {a : α}, xa ⊩ a → (xf ⬝ xa) ⊩ f a
  realizes_left_of_red h htr _ _ ha := (h ha).left_of_red <| red_head _ _ _ htr

theorem realizes_id : I ⊩ (id : α → α) := (·.left_of_red <| red_I _)

theorem realizes_const : K ⊩ (Function.const β : α → β → α) :=
  fun ha ↦ fun _ ↦ ha.left_of_red (red_K _ _)

theorem realizes_comp : B ⊩ (Function.comp : (β → γ) → (α → β) → α → γ) := by
  intro xf f hf xg g hg xa a ha
  exact (hf <| hg ha).left_of_mRed (B_def xf xg xa)

theorem realizes_swap : C ⊩ (Function.swap : (α → β → γ) → β → α → γ) := by
  intro xf f hf xb b hb xa a ha
  exact (hf ha hb).left_of_mRed (C_def xf xb xa)

/-! ### Booleans

`xu ⊩ u` if `xu` is βη-equivalent to the standard Church boolean.
-/

instance : Realized Bool where
  Realizes' xu u := ∀ (y z : SKI), (xu ⬝ y ⬝ z) ↠ (if u then y else z)
  realizes_left_of_red h htr y z := (@h y z).head <| red_head _ _ z <| red_head _ _ _ htr

/-- Standard `true`: `TT := λ x y. x`. -/
def TT : SKI := K

theorem realizes_true : TT ⊩ true := fun y z ↦ MRed.K y z

/-- Standard `false`: `FF := λ x y. y`. -/
def FF : SKI := (&1 : SKI.Polynomial 2).toSKI

theorem realizes_false : FF ⊩ false := fun y z ↦ SKI.Polynomial.toSKI_correct _ [y, z] rfl

/-- Boolean conditional. -/
def Cond : SKI := RotR

theorem Realizes.cond_app_red_ite {xu : SKI} {u : Bool} (hu : xu ⊩ u) (y z : SKI) :
    (Cond ⬝ y ⬝ z ⬝ xu) ↠ if u then y else z := (rotR_def y z xu).trans (hu y z)

theorem cond_realizes_ite : Cond ⊩ (fun (a b : α) (u : Bool) ↦ if u then a else b) := by
  rintro xa a ha xb b hb xu (_ | _) hu
  · exact hb.left_of_mRed (hu.cond_app_red_ite xa xb)
  · exact ha.left_of_mRed (hu.cond_app_red_ite xa xb)

/-!
### Pairs

`xp ⊩ ⟨a, b⟩` if `Fst ⬝ xp ⊩ a` and `Snd ⬝ xp ⊩ b`, where `Fst` and `Snd` are the canonical
projections. We note that this breaks the "Church encoding" pattern, which would define encodings
of a product by its recursor, ie `xp ⊩ ⟨a, b⟩` if for every `f`, `xp ⬝ f ↠ f ⬝ xa ⬝ xb` for some
`xa ⊩ a` and `xb ⊩ b`.
-/

/-- MkPair := λ a b. ⟨a, b⟩ -/
def MkPair : SKI := SKI.Cond

/-- First projection -/
def Fst : SKI := R ⬝ TT

/-- Second projection -/
def Snd : SKI := R ⬝ FF

@[scoped grind .]
theorem fst_correct (a b : SKI) : (Fst ⬝ (MkPair ⬝ a ⬝ b)) ↠ a := calc
  _ ↠ SKI.Cond ⬝ a ⬝ b ⬝ TT := R_def ..
  _ ↠ TT ⬝ a ⬝ b := rotR_def ..
  _ ⭢ a := red_K ..

@[scoped grind .]
theorem snd_correct (a b : SKI) : (Snd ⬝ (MkPair ⬝ a ⬝ b)) ↠ b := by calc
  _ ↠ SKI.Cond ⬝ a ⬝ b ⬝ FF := R_def _ _
  _ ↠ FF ⬝ a ⬝ b := rotR_def ..
  _ ⭢ I ⬝ b := red_head _ _ b <| red_K ..
  _ ⭢ b := red_I b

instance : Realized (α × β) where
  Realizes' xp p := (Fst ⬝ xp) ⊩ p.1 ∧ (Snd ⬝ xp) ⊩ p.2
  realizes_left_of_red hy htr :=
    ⟨hy.1.left_of_red (red_tail _ _ _ htr), hy.2.left_of_red (red_tail _ _ _ htr)⟩

theorem realizes_prodMk : MkPair ⊩ @Prod.mk α β := by
  intro xa a ha xb b hb
  exact ⟨ha.left_of_mRed (fst_correct ..), hb.left_of_mRed (snd_correct ..)⟩

theorem realizes_prodFst : Fst ⊩ @Prod.fst α β := fun hp ↦ hp.1

theorem realizes_prodSnd : Snd ⊩ @Prod.snd α β := fun hp ↦ hp.2

/-- Product recursor. -/
def prodRec : SKI := (&0 ⬝' (Fst ⬝' &1) ⬝' (Snd ⬝' &1) : SKI.Polynomial 2).toSKI

theorem realizes_prodRec : prodRec ⊩ (Prod.rec : (α → β → γ) → α × β → γ) := by
  intro xf f hf xp p ⟨ha, hb⟩
  exact (hf ha hb).left_of_mRed <| SKI.Polynomial.toSKI_correct _ [xf, xp] rfl

/-!
### Sums

`xab ⊩ s : α ⊕ β` if for every `f, g`, `xab ⬝ f ⬝ g` reduces to `f ⬝ xa`, for `s = .inl a` and
`xa ⊩ a`, or `g ⬝ xb`, for `s = .inr b` and `xb ⊩  b`.
-/

/-- Realizers for sums. -/
def realizesSum {α β : Type*} [Realized α] [Realized β] (x : SKI) : α ⊕ β → Prop
  | .inl a => ∃ xa, (xa ⊩ a) ∧ ∀ f g, (x ⬝ f ⬝ g) ↠ f ⬝ xa
  | .inr b => ∃ xb, (xb ⊩ b) ∧ ∀ f g, (x ⬝ f ⬝ g) ↠ g ⬝ xb

instance : Realized (α ⊕ β) where
  Realizes' := realizesSum
  realizes_left_of_red := by
    rintro x y (a | b) ⟨z, hz, hz'⟩ htr
    all_goals
      use z, hz
      exact fun f g ↦ (hz' f g).head (red_head _ _ _ <| red_head _ _ _ htr)

/-- Left-insertion for sums. -/
def Inl : SKI := (&1 ⬝' &0 : SKI.Polynomial 3).toSKI

theorem realizes_sumInl : Inl ⊩ @Sum.inl α β := by
  intro xa a ha
  use xa, ha, (SKI.Polynomial.toSKI_correct _ [xa, ·, ·] rfl)

/-- Right-insertion for sums. -/
def Inr : SKI := (&2 ⬝' &0 : SKI.Polynomial 3).toSKI

theorem realizes_sumInr : Inr ⊩ @Sum.inr α β := by
  intro xb b hb
  use xb, hb, (SKI.Polynomial.toSKI_correct _ [xb, ·, ·] rfl)

-- /-- Sum recursor. -/
def sumRec : SKI := SKI.RotR

theorem realizes_sumRec : sumRec ⊩ (Sum.rec : (α → γ) → (β → γ) → α ⊕ β → γ) := by
  rintro xf f hf xg g hg xab (a | b) ⟨x, hx, hx'⟩
  · exact (hf hx).left_of_mRed <| (rotR_def ..).trans <| hx' xf xg
  · exact (hg hx).left_of_mRed <| (rotR_def ..).trans <| hx' xf xg

/-!
### Partial values

A term `x` encodes a partial value `o` if `o = Part.none`, or `o = Part.some a` and `x ⊩ a`. We
specialize the definition of realizers for function types to partial functions `a →. β`.
-/

instance : Realized (Part α) where
  Realizes' x o := (h : o.Dom) → x ⊩ o.get h
  realizes_left_of_red h htr hdom := (h hdom).left_of_red htr

theorem realizes_part_iff_forall_mem {o : Part α} :
    x ⊩ o ↔ ∀ a ∈ o, x ⊩ a := by
  simp [Part.mem_eq]
  rfl

theorem realizes_of_mem {o : Part α} (ho : x ⊩ o) {a : α} (ha : a ∈ o) : x ⊩ a :=
  realizes_part_iff_forall_mem.mp ho a ha

@[simp] theorem realizes_partSome_iff {a : α} : x ⊩ Part.some a ↔ x ⊩ a := by
  simp [realizes_part_iff_forall_mem]

@[simp] theorem realizes_partNone : x ⊩ @Part.none α := by
  simp [realizes_part_iff_forall_mem]

instance : Realized (α →. β) := inferInstanceAs <| Realized (α → Part β)

theorem realizes_pfun_iff {f : α →. β} :
    x ⊩ f ↔ ∀ {a xa}, (ha : a ∈ f.Dom) → xa ⊩ a → (x ⬝ xa) ⊩ (f.fn a ha) := by
  constructor
  · intro h a xa ha hxa
    exact h hxa ha
  · intro h a xa ha hdom
    exact h hdom ha

end Cslib.SKI

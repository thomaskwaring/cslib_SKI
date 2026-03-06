/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Cslib.Languages.CombinatoryLogic.Basic
public import Cslib.Foundations.Semantics.Encoded

@[expose] public section

namespace Cslib.SKI

open Red MRed Relation Encoded IsEncoding

/-- A term `xf` encodes a function `f : α → β` if for every `xa ⊩ a : α`, `xf ⬝ a ⊩ f a`. -/
instance instEncodedPi (α β : Type*) [hα : Encoded α SKI] [hβ : Encoded β SKI] :
    Encoded (α → β) SKI where
  IsEncoding f z := ∀ {a : α} {x : SKI}, (x ⊩ a) → (z ⬝ x) ⊩ (f a)

instance instEncodedLiftPi (α β : Type*) [hα : Encoded α SKI] [hβ : EncodedLift β Red] :
    EncodedLift (α → β) Red where
  isEncoding_left_of_red := by
    intro f x y hy h a z hz
    apply EncodedLift.isEncoding_left_of_red (hy hz)
    exact red_head _ _ _ h

instance instEncodedDescPi (α β : Type*) [hα : Encoded α SKI] [hβ : EncodedDesc β Red] :
    EncodedDesc (α → β) Red where
  isEncoding_right_of_red := by
    intro f x y hy h a z hz
    apply EncodedDesc.isEncoding_right_of_red (hy hz)
    exact red_head _ _ _ h

-- instance instFaithfullyEncodedPi (α β : Type*) [hα : FullyEncoded α] [hβ : FaithfullyEncoded β] :
--     FaithfullyEncoded (α → β) where
--   eq_of_isEncoding_of_mJoin := by
--     intro f g x y hf hg h
--     ext a
--     obtain ⟨z, hz⟩ := hα.exists_isEncoding a
--     apply hβ.eq_of_isEncoding_of_mJoin (hf hz) (hg hz)
--     exact mJoin_red_head z h

/-!
### Pairs

`xp ⊩ ⟨a, b⟩` if `Fst ⬝ xp ⊩ a` and `Snd ⬝ xp ⊩ b`, where `Fst` and `Snd` are the canonical
projections. We note that this breaks the "Church encoding" pattern, which would define encodings
of a product by its recursor, ie `xp ⊩ ⟨a, b⟩` if for every `f`, `xp ⬝ f ↠ f ⬝ xa ⬝ xb` for some
`xa ⊩ a` and `xb ⊩ b`.
-/

/-- MkPair := λ a b. ⟨a,b⟩ -/
def MkPair : SKI := SKI.Cond
/-- First projection -/
def Fst : SKI := R ⬝ TT
/-- Second projection -/
def Snd : SKI := R ⬝ FF

@[scoped grind .]
theorem fst_correct (a b : SKI) : (Fst ⬝ (MkPair ⬝ a ⬝ b)) ↠ a := by calc
  _ ↠ SKI.Cond ⬝ a ⬝ b ⬝ TT := R_def _ _
  _ ↠ a := cond_correct TT a b true TT_correct

@[scoped grind .]
theorem snd_correct (a b : SKI) : (Snd ⬝ (MkPair ⬝ a ⬝ b)) ↠ b := by calc
  _ ↠ SKI.Cond ⬝ a ⬝ b ⬝ FF := R_def _ _
  _ ↠ b := cond_correct FF a b false FF_correct

instance instEncodedProd {α β : Type*} [Encoded α SKI] [Encoded β SKI] : Encoded (α × β) SKI where
  IsEncoding p x := ((Fst ⬝ x) ⊩ p.1)  ∧ (Snd ⬝ x) ⊩ p.2

instance instEncodedLiftProd {α β : Type*} [EncodedLift α Red] [EncodedLift β Red] :
    EncodedLift (α × β) Red where
  isEncoding_left_of_red := by
    intro p x y ⟨hp₁, hp₂⟩ h
    constructor
    · apply hp₁.left_of_mRed
      exact Relation.ReflTransGen.single <| red_tail Fst _ _ h
    · apply hp₂.left_of_mRed
      exact Relation.ReflTransGen.single <| red_tail Snd _ _ h

instance instEncodedDescProd {α β : Type*} [EncodedDesc α Red] [EncodedDesc β Red] :
    EncodedDesc (α × β) Red where
  isEncoding_right_of_red := by
    intro p x y ⟨hp₁, hp₂⟩ h
    constructor
    · apply hp₁.right_of_mRed
      exact Relation.ReflTransGen.single <| red_tail Fst _ _ h
    · apply hp₂.right_of_mRed
      exact Relation.ReflTransGen.single <| red_tail Snd _ _ h

/-- The pairing term `SKI.MkPair` indeed encodes `Prod.Mk`. -/
lemma isEncoding_mkPair {α β : Type*} [EncodedLift α Red] [EncodedLift β Red] :
    SKI.MkPair ⊩ (Prod.mk : α → β → α × β) := by
  intro a xa ha b xb hb
  constructor
  · exact ha.left_of_mRed <| fst_correct ..
  · exact hb.left_of_mRed <| snd_correct ..

lemma isEncoding_fst {α β : Type*} [Encoded α SKI] [Encoded β SKI] :
    SKI.Fst ⊩ (Prod.fst : α × β → α) := by
  intro _ _ h
  exact h.1

lemma isEncoding_snd {α β : Type*} [Encoded α SKI] [Encoded β SKI] :
    SKI.Snd ⊩ (Prod.snd : α × β → β) := by
  intro _ _ h
  exact h.2

-- instance instFullyEncodedProd {α β : Type*} [hα : FullyEncoded α SKI] [hβ : FullyEncoded β SKI]
--     [EncodedLift α Red] [EncodedLift β Red] : FullyEncoded (α × β) SKI where
--   exists_isEncoding
--     | ⟨a, b⟩ => by
--       obtain ⟨xa : SKI, ha⟩ := hα.exists_isEncoding a
--       obtain ⟨xb, hb⟩ := hβ.exists_isEncoding b
--       use SKI.MkPair ⬝ xa ⬝ xb
--       exact isEncoding_mkPair ha hb

-- instance instFaithfullyEncodedProd {α β : Type*} [FaithfullyEncoded α] [FaithfullyEncoded β] :
--     FaithfullyEncoded (α × β) where
--   eq_of_isEncoding_of_mJoin := by
--     intro p q xp xq ⟨hp₁, hp₂⟩ ⟨hq₁, hq₂⟩ h
--     rw [Prod.mk_inj]
--     constructor
--     · apply eq_of_isEncoding_of_mJoin hp₁ hq₁
--       exact mJoin_red_tail _ h
--     · apply eq_of_isEncoding_of_mJoin hp₂ hq₂
--       exact mJoin_red_tail _ h

def prodRecPoly : SKI.Polynomial 2 := &0 ⬝' (Fst ⬝' &1) ⬝' (Snd ⬝' &1)
/-- The term which will encode `Prod.rec`. -/
def prodRec := prodRecPoly.toSKI
lemma prodRec_def (xf xp : SKI) : (prodRec ⬝ xf ⬝ xp) ↠ xf ⬝ (Fst ⬝ xp) ⬝ (Snd ⬝ xp) :=
  prodRecPoly.toSKI_correct [xf, xp] (by simp)

theorem isEncoding_prod_rec {α β γ : Type*} [Encoded α SKI] [Encoded β SKI]
    [EncodedLift γ Red] : prodRec ⊩ (Prod.rec : (α → β → γ) → α × β → γ) := by
  intro f xf hf p xp hp
  exact (hf hp.1 hp.2).left_of_mRed <| prodRec_def ..

/-!
### Sums

`xab ⊩ s : α ⊕ β` if for every `f, g`, `xab ⬝ f ⬝ g` reduces to `f ⬝ xa`, for `s = .inl a` and
`xa ⊩ a`, or `g ⬝ xb`, for `s = .inr b` and `xb ⊩  b`.
-/

def isEncodingSum {α β : Type*} [Encoded α SKI] [Encoded β SKI] : α ⊕ β → SKI → Prop
  | .inl a, x => ∀ f g : SKI, ∃ xa : SKI, (xa ⊩ a) ∧ (x ⬝ f ⬝ g) ↠ f ⬝ xa
  | .inr b, x => ∀ f g : SKI, ∃ xb : SKI, (xb ⊩ b) ∧ (x ⬝ f ⬝ g) ↠ g ⬝ xb

instance instEncodedSum {α β : Type*} [Encoded α SKI] [Encoded β SKI] : Encoded (α ⊕ β) SKI where
  IsEncoding := isEncodingSum

instance instEncodedLiftSum {α β : Type*} [EncodedLift α Red] [EncodedLift β Red] :
    EncodedLift (α ⊕ β) Red where
  isEncoding_left_of_red := by
    intro ab x y hy h
    cases ab
    case inl a =>
      intro f g
      obtain ⟨xa, ha, hred⟩ := hy f g
      use xa, ha
      exact Relation.ReflTransGen.head (red_head _ _ g <| red_head _ _ f h) hred
    case inr b =>
      intro f g
      obtain ⟨xb, hb, hred⟩ := hy f g
      use xb, hb
      exact Relation.ReflTransGen.head (red_head _ _ g <| red_head _ _ f h) hred

-- instance instFaithfullyEncodedSum {α β : Type*} [FaithfullyEncoded α] [FaithfullyEncoded β] :
--     FaithfullyEncoded (α ⊕ β) where
--   eq_of_isEncoding_of_mJoin := by
--     intro ab ab' x y hx hy h
--     have hII : MJoin Red (x ⬝ I ⬝ I) (y ⬝ I ⬝ I) := mJoin_red_head I <| mJoin_red_head I h
--     have hTF : MJoin Red (x ⬝ (K ⬝ TT) ⬝ (K ⬝ FF)) (y ⬝ (K ⬝ TT) ⬝ (K ⬝ FF)) :=
--       mJoin_red_head _ <| mJoin_red_head _ h
--     cases ab
--     case inl a =>
--       cases ab'
--       case inl a' =>
--         obtain ⟨xa, ha, hred⟩ := hx I I
--         replace hred := hred.tail (red_I xa)
--         obtain ⟨xa', ha', hred'⟩ := hy I I
--         replace hred' := hred'.tail (red_I xa')
--         rw [Sum.inl.injEq]
--         apply eq_of_isEncoding_of_mJoin ha ha'
--         refine mJoin_red_equivalence.trans (y := x ⬝ I ⬝ I) (MJoin.single hred).symm ?_
--         exact mJoin_red_equivalence.trans (y := y ⬝ I ⬝ I) hII (MJoin.single hred')
--       case inr b' =>
--         obtain ⟨xa, ha, hred⟩ := hx (K ⬝ TT) (K ⬝ FF)
--         replace hred := hred.tail (red_K ..)
--         obtain ⟨xa', ha', hred'⟩ := hy (K ⬝ TT) (K ⬝ FF)
--         replace hred' := hred'.tail (red_K ..)
--         refine False.elim <| TF_nequiv ?_
--         refine mJoin_red_equivalence.trans (y := x ⬝ (K ⬝ TT) ⬝ (K ⬝ FF))
--           (MJoin.single hred).symm ?_
--         exact mJoin_red_equivalence.trans (y := y ⬝ (K ⬝ TT) ⬝ (K ⬝ FF))
--           hTF (MJoin.single hred')
--     case inr b =>
--       cases ab'
--       case inl a' =>
--         obtain ⟨xb, hb, hred⟩ := hx (K ⬝ TT) (K ⬝ FF)
--         replace hred := hred.tail (red_K ..)
--         obtain ⟨xa', ha', hred'⟩ := hy (K ⬝ TT) (K ⬝ FF)
--         replace hred' := hred'.tail (red_K ..)
--         refine False.elim <| TF_nequiv ?_
--         refine mJoin_red_equivalence.trans (y := y ⬝ (K ⬝ TT) ⬝ (K ⬝ FF))
--           (MJoin.single hred').symm ?_
--         exact mJoin_red_equivalence.trans (y := x ⬝ (K ⬝ TT) ⬝ (K ⬝ FF))
--           hTF.symm (MJoin.single hred)
--       case inr b' =>
--         obtain ⟨xa, ha, hred⟩ := hx I I
--         replace hred := hred.tail (red_I xa)
--         obtain ⟨xa', ha', hred'⟩ := hy I I
--         replace hred' := hred'.tail (red_I xa')
--         rw [Sum.inr.injEq]
--         apply eq_of_isEncoding_of_mJoin ha ha'
--         refine mJoin_red_equivalence.trans (y := x ⬝ I ⬝ I) (MJoin.single hred).symm ?_
--         exact mJoin_red_equivalence.trans (y := y ⬝ I ⬝ I) hII (MJoin.single hred')

def inlPoly : SKI.Polynomial 3 := &1 ⬝' &0
protected def Inl : SKI := inlPoly.toSKI
lemma inl_def (a f g : SKI) : (SKI.Inl ⬝ a ⬝ f ⬝ g) ↠ f ⬝ a :=
  inlPoly.toSKI_correct [a, f, g] (by simp)

lemma isEncoding_sum_inl {α β : Type*} [Encoded α SKI] [Encoded β SKI] :
    SKI.Inl ⊩ (Sum.inl : α → α ⊕ β) := by
  intro a xa ha f g
  use xa, ha, inl_def ..

def inrPoly : SKI.Polynomial 3 := &2 ⬝' &0
protected def Inr : SKI := inrPoly.toSKI
lemma inr_def (a f g : SKI) : (SKI.Inr ⬝ a ⬝ f ⬝ g) ↠ g ⬝ a :=
  inrPoly.toSKI_correct [a, f, g] (by simp)

lemma isEncoding_sum_inr {α β : Type*} [Encoded α SKI] [Encoded β SKI] :
    SKI.Inr ⊩ (Sum.inr : β → α ⊕ β) := by
  intro b xb hb f g
  use xb, hb, inr_def ..

-- instance instFullyEncodedSum {α β : Type*} [FullyEncoded α] [FullyEncoded β] :
--     FullyEncoded (α ⊕ β) where
--   exists_isEncoding
--     | .inl a => by
--       obtain ⟨xa, ha⟩ := FullyEncoded.exists_isEncoding a
--       use SKI.Inl ⬝ xa, isEncoding_sum_inl ha
--     | .inr b => by
--       obtain ⟨xb, hb⟩ := FullyEncoded.exists_isEncoding b
--       use SKI.Inr ⬝ xb, isEncoding_sum_inr hb

def sumRec : SKI := RotR

theorem isEncoding_sum_rec {α β γ : Type*} [Encoded α SKI] [Encoded β SKI] [EncodedLift γ Red] :
    sumRec ⊩ (Sum.rec : (α → γ) → (β → γ) → α ⊕ β → γ) := by
  intro f xf hf g xg hg ab xab hab
  cases ab with
  | inl a =>
    obtain ⟨xa, ha, hred⟩ := hab xf xg
    exact (hf ha).left_of_mRed <| (rotR_def ..).trans hred
  | inr b =>
    obtain ⟨xb, hb, hred⟩ := hab xf xg
    exact (hg hb).left_of_mRed <| (rotR_def ..).trans hred

instance instEncodedLiftBool : EncodedLift Bool Red where
  IsEncoding u z := ∀ x y : SKI, (z ⬝ x ⬝ y) ↠ (if u then x else y)
  isEncoding_left_of_red := by
    intro u x y hu h a b
    trans y ⬝ a ⬝ b
    · apply MRed.head; apply MRed.head; exact Relation.ReflTransGen.single h
    · exact hu a b
--   eq_of_isEncoding_of_mJoin := by
--     intro u v x y hx hy h
--     have h : MJoin Red (if u then S else K) (if v then S else K) := by
--       apply mJoin_red_equivalence.trans (y := x ⬝ S ⬝ K)
--       · apply mJoin_red_equivalence.symm
--         apply Relation.MJoin.single
--         exact hx S K
--       · apply mJoin_red_equivalence.trans (y := y ⬝ S ⬝ K)
--         · exact mJoin_red_head K <| mJoin_red_head S h
--         · apply Relation.MJoin.single
--           exact hy S K
--     grind [sk_nequiv, mJoin_red_equivalence.symm h]

lemma isEncoding_tt : TT ⊩ true := TT_correct

lemma isEncoding_ff : FF ⊩ false := FF_correct

lemma isEncoding_cond {α : Type*} [EncodedLift α Red] :
    SKI.Cond ⊩ (fun (a b : α) (u : Bool) => if u then a else b) := by
  intro a xa ha b xb hb u xu hu
  cases u
  case false =>
    apply hb.left_of_mRed
    simpa using cond_correct xu xa xb false hu
  case true =>
    apply ha.left_of_mRed
    simpa using cond_correct xu xa xb true hu

-- /-- A specialisation of `Church : Nat → SKI`. -/
-- private def churchK : Nat → SKI
--   | 0 => K
--   | n+1 => K ⬝ (churchK n)

-- private lemma churchK_church : (n : Nat) → churchK n = Church n K K
--   | 0 => rfl
--   | n+1 => by simp [churchK, Church, churchK_church n]

-- private lemma churchK_redexFree : (n : Nat) → RedexFree (churchK n)
--   | 0 => trivial
--   | n+1 => churchK_redexFree n

-- @[simp]
-- private lemma churchK_size : (n : Nat) → (churchK n).size = n + 1
--   | 0 => rfl
--   | n + 1 => by rw [churchK, size, size, churchK_size, Nat.add_comm]

-- private lemma churchK_injective : Function.Injective churchK :=
--   fun n m h => by simpa using congrArg SKI.size h

-- instance instEncodedLiftNat : EncodedLift ℕ Red where
--   IsEncoding := IsChurch
--   isEncoding_of_red := by
--     intro n x y hn h a b
--     trans y ⬝ a ⬝ b
--     · apply MRed.head; apply MRed.head; exact Relation.ReflTransGen.single h
--     · exact hn a b
--   eq_of_isEncoding_of_mJoin := by
--     intro n m x y hx hy h
--     suffices MJoin Red (churchK n) (churchK m) by
--       apply churchK_injective
--       exact eq_of_mJoin_red_redexFree this (churchK_redexFree n) (churchK_redexFree m)
--     apply mJoin_red_equivalence.trans (y := x ⬝ K ⬝ K)
--     · simp_rw [churchK_church]
--       exact mJoin_red_equivalence.symm <| Relation.MJoin.single (hx K K)
--     · apply mJoin_red_equivalence.trans (y := y ⬝ K ⬝ K)
--       · apply mJoin_red_head; apply mJoin_red_head; assumption
--       · simp_rw [churchK_church]
--         exact Relation.MJoin.single (hy K K)

-- instance instFullyEncodedNat : FullyEncoded Nat where
--   exists_isEncoding n := by
--     use toChurch n, toChurch_correct n

-- def Iter := R

-- lemma isEncoding_iter : Iter ⊩ (Nat.iterate (α := α)) := by
--   intro f xf hf n xn hn a xa ha
--   suffices IsEncoding (f^[n] a) (Church n xf xa) by
--     apply this.of_mRed
--     calc
--       _ ↠ xn ⬝ xf ⬝ xa := MRed.head _ <| R_def ..
--       _ ↠ Church n xf xa := hn ..
--   clear hn
--   induction n with
--   | zero => simpa
--   | succ n ih =>
--       rw [Function.iterate_succ']
--       exact hf ih

-- def Nat.recPairStep (f : Nat → α → α) : α × Nat → α × Nat
--   | ⟨y, m⟩ => ⟨f m y, m + 1⟩

-- lemma Nat.recPairStep_correct {α' : Type*} (a : α') (f : Nat → α' → α') (n : Nat) :
--     (Nat.recPairStep f)^[n] ⟨a, 0⟩ = ⟨Nat.rec a f n, n⟩ := by
--   induction n with
--   | zero => simp
--   | succ n ih =>
--     rw [Function.iterate_succ', Function.comp_apply, ih, recPairStep]

-- /-- We encode primitive recursion on `Nat` by the usual Kleene dentist trick. -/
-- def natRecAuxPoly : SKI.Polynomial 2 :=
--   SKI.MkPair ⬝' (&0 ⬝' (Snd ⬝' &1) ⬝' (Fst ⬝' &1)) ⬝' (SKI.Succ ⬝' (Snd ⬝' &1))
-- def natRecAux := natRecAuxPoly.toSKI
-- lemma natRecAux_def (f p : SKI) :
--     (natRecAux ⬝ f ⬝ p) ↠ SKI.MkPair ⬝ (f ⬝ (Snd ⬝ p) ⬝ (Fst ⬝ p)) ⬝ (SKI.Succ ⬝ (Snd ⬝ p)) :=
--   natRecAuxPoly.toSKI_correct [f, p] (by simp)

-- lemma natRecAux_correct {f : Nat → α → α} {xf : SKI} (hf : xf ⊩ f) :
--     (natRecAux ⬝ xf) ⊩ (Nat.recPairStep f) := by
--   intro p xp hp
--   suffices IsEncoding (Nat.recPairStep f p)
--       (SKI.MkPair ⬝ (xf ⬝ (Snd ⬝ xp) ⬝ (Fst ⬝ xp)) ⬝ (SKI.Succ ⬝ (Snd ⬝ xp))) by
--     exact this.of_mRed <| natRecAux_def ..
--   apply isEncoding_mkPair
--   · exact hf hp.2 hp.1
--   · exact SKI.succ_correct _ _ hp.2

-- lemma isEncoded_recPairStep_iter {a : α} {xa : SKI} (ha : xa ⊩ a)
--     {f : Nat → α → α} {xf : SKI} (hf : xf ⊩ f) {n : Nat} {xn : SKI} (hn : xn ⊩ n) :
--     (R ⬝ (natRecAux ⬝ xf) ⬝ xn ⬝ (MkPair ⬝ xa ⬝ SKI.Zero)) ⊩ (⟨Nat.rec a f n, n⟩ : α × Nat) := by
--   rw [←Nat.recPairStep_correct]
--   refine isEncoding_iter (natRecAux_correct hf) hn ?_
--   apply isEncoding_mkPair
--   · exact ha
--   · exact zero_correct

-- def natRecPoly : SKI.Polynomial 3 :=
--   Fst ⬝' (R ⬝' (natRecAux ⬝' &1) ⬝' &2 ⬝' (MkPair ⬝' &0 ⬝' SKI.Zero))
-- def natRec := natRecPoly.toSKI
-- lemma natRec_def (xa xf xn : SKI) :
--     (natRec ⬝ xa ⬝ xf ⬝ xn) ↠ Fst ⬝ (R ⬝ (natRecAux ⬝ xf) ⬝ xn ⬝ (MkPair ⬝ xa ⬝ SKI.Zero)) :=
--   natRecPoly.toSKI_correct [xa, xf, xn] (by simp)

-- /-- Primitive recursion on `Nat`. -/
-- theorem isEncoded_nat_rec :
--     natRec ⊩ (Nat.rec : α → (Nat → α → α) → Nat → α) := by
--   intro a xa ha f xf hf n xn hn
--   exact IsEncoding.of_mRed (isEncoded_recPairStep_iter ha hf hn).1 (natRec_def xa xf xn)

-- def IsEncodingList : List α → SKI → Prop
--   | [], cns => ∀ c n : SKI, (cns ⬝ c ⬝ n) ↠ n
--   | a :: as, cns => ∀ c n : SKI,
--       ∃ cx cxs : SKI, IsEncoding a cx ∧ IsEncodingList as cxs ∧
--         (cns ⬝ c ⬝ n) ↠ c ⬝ cx ⬝ (cxs ⬝ c ⬝ n)

-- instance instEncodedList : Encoded (List α) where
--   IsEncoding := IsEncodingList
--   isEncoding_of_red := by
--     intro as cns cns' has h
--     induction as generalizing cns cns' with
--     | nil =>
--       intro c n
--       refine Relation.ReflTransGen.head ?_ (has c n)
--       exact red_head _ _ _ <| red_head _ _ _ h
--     | cons a as ih =>
--       intro c n
--       obtain ⟨cx', cxs', hcx, hcxs, hred⟩ := has c n
--       use cx', cxs', hcx, hcxs
--       refine Relation.ReflTransGen.head ?_ hred
--       exact red_head _ _ _ <| red_head _ _ _ h

-- /-- nil = λ c n. n -/
-- def NilPoly : SKI.Polynomial 2 := &1
-- def Nil : SKI := NilPoly.toSKI
-- theorem nil_def (c n : SKI) : (Nil ⬝ c ⬝ n) ↠ n :=
--   NilPoly.toSKI_correct [c, n] (by simp)

-- theorem nil_correct : Nil ⊩ ([] : List α) := nil_def

-- /-- cons = λ x xs c n. c x (xs c n) -/
-- def ConsPoly : SKI.Polynomial 4 := &2 ⬝' &0 ⬝' (&1 ⬝' &2 ⬝' &3)
-- def Cons : SKI := ConsPoly.toSKI
-- theorem cons_def (x xs c n : SKI) :
--     (Cons ⬝ x ⬝ xs ⬝ c ⬝ n) ↠ c ⬝ x ⬝ (xs ⬝ c ⬝ n) :=
--   ConsPoly.toSKI_correct [x, xs, c, n] (by simp)

-- theorem cons_correct :
--     Cons ⊩ (List.cons : α → List α → List α) := by
--   intro a xa ha as xas has c n
--   use xa, xas, ha, has, cons_def ..

-- lemma exists_isEncoding_list {α : Type*} [FullyEncoded α] :
--     (as : List α) → (∃ xas : SKI, xas ⊩ as)
--   | [] => ⟨Nil, nil_correct⟩
--   | a :: as => by
--     obtain ⟨xa, ha⟩ := FullyEncoded.exists_isEncoding a
--     obtain ⟨xas, has⟩ := exists_isEncoding_list as
--     use Cons ⬝ xa ⬝ xas, cons_correct ha has

-- instance instFullyEncodedList {α : Type*} [FullyEncoded α] : FullyEncoded (List α) where
--   exists_isEncoding := exists_isEncoding_list

-- def FoldR := RotR

-- lemma isEncoding_list_foldr :
--     FoldR ⊩ (List.foldr : (α → β → β) → β → List α → β) := by
--   intro f xf hf b xb hb l xl hl
--   suffices (xl ⬝ xf ⬝ xb) ⊩ (l.foldr f b) by exact this.of_mRed <| rotR_def ..
--   induction l generalizing xl with
--   | nil => exact hb.of_mRed <| hl ..
--   | cons a l ih =>
--     obtain ⟨xa, xl', ha, hl', hred⟩ := hl xf xb
--     have : IsEncoding (f a (List.foldr f b l)) (xf ⬝ xa ⬝ (xl' ⬝ xf ⬝ xb)) :=
--       hf ha (ih hl')
--     exact this.of_mRed hred

-- def List.recPairStep (f : α → List α → β → β) : α → (β × List α) → (β × List α)
--   | a, ⟨y, as⟩ => ⟨f a as y, a :: as⟩

-- lemma List.recPairStep_foldr {α' β' : Type*} (b : β') (f : α' → List α' → β' → β') (as : List α') :
--     List.foldr (β := β' × List α') (List.recPairStep f) ⟨b, []⟩ as = ⟨List.rec b f as, as⟩ := by
--   induction as <;> simp_all [recPairStep]

-- def listRecAuxPoly : SKI.Polynomial 3 :=
--   SKI.MkPair ⬝' (&0 ⬝' &1 ⬝' (Snd ⬝' &2) ⬝' (Fst ⬝' &2)) ⬝' (Cons ⬝' &1 ⬝' (Snd ⬝' &2))
-- def listRecAux : SKI := listRecAuxPoly.toSKI
-- lemma listRecAux_def (xf xa xp : SKI) :
--     (listRecAux ⬝ xf ⬝ xa ⬝ xp) ↠
--       SKI.MkPair ⬝ (xf ⬝ xa ⬝ (Snd ⬝ xp) ⬝ (Fst ⬝ xp)) ⬝ (Cons ⬝ xa ⬝ (Snd ⬝ xp)) :=
--   listRecAuxPoly.toSKI_correct [xf, xa, xp] (by simp)

-- lemma listRecAux_correct {f : α → List α → β → β} {xf : SKI}
--     (hf : xf ⊩ f) : (listRecAux ⬝ xf) ⊩ (List.recPairStep f) := by
--   intro a xa ha p xp hp
--   refine IsEncoding.of_mRed ?_ (listRecAux_def xf xa xp)
--   apply isEncoding_mkPair
--   · exact hf ha hp.2 hp.1
--   · exact cons_correct ha hp.2

-- lemma isEncoding_recPairStep_foldr {b : β} {xb : SKI} (hb : xb ⊩ b)
--     {f : α → List α → β → β} {xf : SKI} (hf : xf ⊩ f) {as : List α} {xas : SKI} (has : xas ⊩ as) :
--     (SKI.RotR ⬝ (listRecAux ⬝ xf) ⬝ (MkPair ⬝ xb ⬝ Nil) ⬝ xas) ⊩
--       (⟨List.rec b f as, as⟩ : β × List α) := by
--   rw [←List.recPairStep_foldr]
--   refine isEncoding_list_foldr (listRecAux_correct hf) ?_ has
--   exact isEncoding_mkPair hb nil_correct

-- def listRecPoly : SKI.Polynomial 3 :=
--   Fst ⬝' (SKI.RotR ⬝' (listRecAux ⬝' &1) ⬝' (MkPair ⬝' &0 ⬝' Nil) ⬝' &2)
-- def listRec := listRecPoly.toSKI
-- lemma listRec_def (xb xf xas : SKI) :
--     (listRec ⬝ xb ⬝ xf ⬝ xas) ↠ Fst ⬝ (SKI.RotR ⬝ (listRecAux ⬝ xf) ⬝ (MkPair ⬝ xb ⬝ Nil) ⬝ xas) :=
--   listRecPoly.toSKI_correct [xb, xf, xas] (by simp)

-- theorem isEncoding_list_rec :
--     listRec ⊩ (List.rec : β → (α → List α → β → β) → List α → β) := by
--   intro b xb hb f xf hf as xas has
--   have := isEncoding_recPairStep_foldr hb hf has
--   exact this.1.of_mRed <| listRec_def ..

-- def Tail := (listRec ⬝ Nil ⬝ (&1 : SKI.Polynomial 3).toSKI)

-- lemma isEncoding_tail : Tail ⊩ (List.tail : List α → List α) := by
--   intro as xas has
--   have : (as.tail = as.rec [] (fun _ t _ => t)) := by cases as <;> rfl
--   rw [this]
--   refine isEncoding_list_rec nil_correct ?_ has
--   intro _ xs _ t xt ht _ xu _
--   apply ht.of_mRed <| (&1 : SKI.Polynomial 3).toSKI_correct [xs, xt, xu] (by simp)

end Cslib.SKI

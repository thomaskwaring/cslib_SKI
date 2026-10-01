/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring, Jesse Alama
-/

module

public import Cslib.Languages.CombinatoryLogic.Realized
public import Mathlib.Data.Nat.Pairing

/-!
# General recursion in the SKI calculus

In this file we implement general recursion functions (on the natural numbers), inspired by the
formalisation of `Mathlib.Computability.Partrec`. Since composition (`B`-combinator) and pairs
(`MkPair`, `Fst`, `Snd`) have been implemented in `Cslib.Computability.CombinatoryLogic.Basic`,
what remains are the following definitions and proofs of their correctness.

- Church numerals : a predicate `IsChurch n a` expressing that the term `a` is βη-equivalent to
the standard church numeral `n` — that is, `a ⬝ f ⬝ x ↠ f ⬝ (f ⬝ ... ⬝ (f ⬝ x)))`.
- SKI numerals : `Zero` and `Succ`, corresponding to `Partrec.zero` and `Partrec.succ`, and
correctness proofs `zero_correct` and `succ_correct`.
- Predecessor : a term `Pred` so that (`pred_correct`)
`IsChurch n a → IsChurch n.pred (Pred ⬝ a)`.
- Primitive recursion : a term `Rec` so that (`rec_correct_succ`) `IsChurch (n+1) a` implies
`Rec ⬝ x ⬝ g ⬝ a ↠ g ⬝ a ⬝ (Rec ⬝ x ⬝ g ⬝ (Pred ⬝ a))` and (`rec_correct_zero`) `IsChurch 0 a`
implies `Rec ⬝ x ⬝ g ⬝ a ↠ x`.
- Unbounded root finding (μ-recursion) : given a term  `f` representing a function `fℕ: Nat → Nat`,
which takes on the value 0 a term `RFind` such that (`rFind_correct`) `RFind ⬝ f ↠ a` such that
`IsChurch n a` for `n` the smallest root of `fℕ`.
- Integer square root : a term `Sqrt` so that (`sqrt_correct`)
`IsChurch n a → IsChurch n.sqrt (Sqrt ⬝ a)`.
- Nat pairing : a term `NatPair` so that (`natPair_correct`)
`IsChurch a x → IsChurch b y → IsChurch (Nat.pair a b) (NatPair ⬝ x ⬝ y)`.
- Nat unpairing : terms `NatUnpairLeft` and `NatUnpairRight` so that (`natUnpairLeft_correct`)
`IsChurch n a → IsChurch n.unpair.1 (NatUnpairLeft ⬝ a)` and (`natUnpairRight_correct`)
`IsChurch n a → IsChurch n.unpair.2 (NatUnpairRight ⬝ a)`.

## References

- For church numerals and recursion via the fixed-point combinator, see sections 3.2 and 3.3 of
Selinger's notes <https://www.mscs.dal.ca/~selinger/papers/papers/lambdanotes.pdf>

## TODO

- One could unify `is_bool`, `IsChurch` and `IsChurchPair` into a predicate
`represents : α → SKI → Prop`, for any type `α` "built from pieces that we understand" — something
along the lines of "pure finite types"
(see eg <https://en.wikipedia.org/wiki/Primitive_recursive_functional>). This would also clean up
the statement of `rfind_correct`.
- The predicate `∃ n : Nat, IsChurch n : SKI → Prop` is semidecidable: by confluence, it suffices
to normal-order reduce `a ⬝ f ⬝ x` for any "atomic" terms `f` and `x`. This could be implemented
by defining reduction on polynomials.
- With such a decision procedure, every SKI-term defines a partial function `Nat →. Nat`, in the
sense of `Mathlib.Data.Part` (as used in `Mathlib.Computability.Partrec`).
- The results of this file should define a surjection `SKI → Nat.Partrec`.
-/

@[expose] public section

namespace Cslib

namespace SKI

variable {α β γ : Type*} [Realized α] [Realized β] [Realized γ] {x y : SKI}

open Red MRed

instance : Realized ℕ where
  Realizes' xn n := ∀ f x, (xn ⬝ f ⬝ x) ↠ (f ⬝ ·)^[n] x
  realizes_left_of_red h htr f x := (h f x).head <| red_head _ _ _ <| red_head _ _ _ htr

/-! ### Church numeral basics -/

/-- Church zero := λ f x. x -/
protected def Zero : SKI := (&1 : SKI.Polynomial 2).toSKI
@[scoped grind .]
theorem realizes_zero : SKI.Zero ⊩ 0 := (SKI.Polynomial.toSKI_correct _ [·, ·] rfl)

/-- Church one := λ f x. f x -/
protected def One : SKI := I
@[scoped grind .]
theorem realizes_one : SKI.One ⊩ 1 := fun f x ↦ MRed.head x <| MRed.I f

/-- Church succ := λ a f x. a f (f x) -/
protected def Succ : SKI := (&0 ⬝' &1 ⬝' (&1 ⬝' &2) : SKI.Polynomial 3).toSKI
theorem realizes_succ : SKI.Succ ⊩ Nat.succ := by
  intro xn n hn f x
  exact (SKI.Polynomial.toSKI_correct _ [xn, f, x] rfl).trans <| hn f (f ⬝ x)

/-- Build the canonical SKI Church numeral for `n`. -/
def toChurch : ℕ → SKI
  | 0 => SKI.Zero
  | n + 1 => SKI.Succ ⬝ (toChurch n)

/-- `toChurch 0 = Zero`. -/
@[simp] lemma toChurch_zero : toChurch 0 = SKI.Zero := rfl
/-- `toChurch (n + 1) = Succ ⬝ toChurch n`. -/
@[simp] lemma toChurch_succ (n : ℕ) : toChurch (n + 1) = SKI.Succ ⬝ (toChurch n) := rfl

/-- `toChurch n` correctly represents `n`. -/
theorem toChurch_realizes (n : ℕ) : toChurch n ⊩ n := by
  induction n with
  | zero => exact realizes_zero
  | succ _ ih => exact realizes_succ ih

/-- Iteration on natural numbers. -/
def Iter : SKI := R

theorem realizes_natIterate : Iter ⊩ @Nat.iterate α := by
  intro xf f hf xn n hn xa a ha
  suffices (xf ⬝ ·)^[n] xa ⊩ f^[n] a from
    this.left_of_mRed <| (MRed.head _ <| R_def xf xn).trans (hn xf xa)
  clear hn
  induction n generalizing xa a with
  | zero => exact ha
  | succ _ ih => exact ih <| hf ha

/-- Auxilliary definition for primitive recursion on naturals (Kleene's "dentist trick"). -/
private def recPairStepNat (f : Nat → α → α) : α × Nat → α × Nat
  | ⟨y, m⟩ => ⟨f m y, m + 1⟩

private lemma iterate_recPairStepNat {α' : Type*} (a : α') (f : Nat → α' → α') (n : Nat) :
    (recPairStepNat f)^[n] ⟨a, 0⟩ = ⟨Nat.rec a f n, n⟩ := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ', Function.comp_apply, ih, recPairStepNat]

/-- `SKI` version on `recPairStepNat`. -/
private def recPairStepSKI : SKI := (SKI.MkPair ⬝'
  (&0 ⬝' (Snd ⬝' &1) ⬝' (Fst ⬝' &1)) ⬝' (SKI.Succ ⬝' (Snd ⬝' &1)) : SKI.Polynomial 2).toSKI

private lemma realizes_recPairStep : recPairStepSKI ⊩ @recPairStepNat α := by
  intro xf f hf xp p ⟨ha, hn⟩
  suffices (SKI.MkPair ⬝ (xf ⬝ (Snd ⬝ xp) ⬝ (Fst ⬝ xp)) ⬝ (SKI.Succ ⬝ (Snd ⬝ xp))) ⊩
    (recPairStepNat f p) from this.left_of_mRed <| SKI.Polynomial.toSKI_correct _ [xf, xp] rfl
  exact realizes_prodMk (hf hn ha) (realizes_succ hn)

private lemma realizes_recPairStep_iter {a : α} {xa : SKI} (ha : xa ⊩ a) {f : Nat → α → α}
    {xf : SKI} (hf : xf ⊩ f) {n : Nat} {xn : SKI} (hn : xn ⊩ n) :
    (Iter ⬝ (recPairStepSKI ⬝ xf) ⬝ xn ⬝ (MkPair ⬝ xa ⬝ SKI.Zero)) ⊩
      (⟨Nat.rec a f n, n⟩ : α × Nat) := by
  rw [← iterate_recPairStepNat]
  exact realizes_natIterate (realizes_recPairStep hf) hn <| realizes_prodMk ha realizes_zero

/-- Recursor for `Nat`. -/
def natRec : SKI :=
  (Fst ⬝' (Iter ⬝' ((SKI.MkPair ⬝' (&0 ⬝' (Snd ⬝' &1) ⬝' (Fst ⬝' &1)) ⬝'
    (SKI.Succ ⬝' (Snd ⬝' &1)) : SKI.Polynomial 2).toSKI ⬝' &1) ⬝' &2 ⬝'
    (MkPair ⬝' &0 ⬝' SKI.Zero)) : SKI.Polynomial 3).toSKI

/-- Primitive recursion on `Nat`. -/
theorem realizes_natRec : natRec ⊩ (Nat.rec : α → (Nat → α → α) → Nat → α) := by
  intro xa a ha xf f hf xn n hn
  refine Realizes.left_of_mRed (realizes_recPairStep_iter ha hf hn).1 ?_
  exact SKI.Polynomial.toSKI_correct _ [xa, xf, xn] rfl

def Pred : SKI := natRec ⬝ SKI.Zero ⬝ K

theorem realizes_pred : Pred ⊩ Nat.pred := by
  have : Nat.pred = Nat.rec 0 (Function.const ℕ) := by ext n; cases n <;> rfl
  rw [this]
  apply realizes_natRec realizes_zero
  exact realizes_const

/-- IsZero := λ n. n (K FF) TT -/
def IsZero : SKI := (&0 ⬝' (K ⬝ FF) ⬝' TT : SKI.Polynomial 1).toSKI

theorem realizes_beq_zero : IsZero ⊩ (· == 0 : ℕ → Bool) := by
  intro xn n hn
  apply Realizes.left_of_mRed ?_ (SKI.Polynomial.toSKI_correct _ [xn] rfl)
  cases n with
  | zero => exact realizes_true.left_of_mRed <| hn (K ⬝ FF) TT
  | succ n =>
    refine realizes_false.left_of_mRed <| (hn (K ⬝ FF) TT).trans ?_
    rw [Function.iterate_succ']
    exact MRed.K FF ((K ⬝ FF ⬝ ·)^[n] TT)

-- This *should* be superceded by the new approach...
-- theorem rec_correct' (base step : SKI) (r : ℕ → ℕ) (hbase : base ⊩ r 0)
--     (hstep : ∀ k : Nat, ∀ cb cp : SKI, cb ⊩ k + 1 → cp ⊩ r k → (step ⬝ cb ⬝ cp) ⊩ r (k + 1)) :
--     (natRec ⬝ base ⬝ step) ⊩ r := by

/-! ### Root-finding (μ-recursion) -/

/--
First define an auxiliary function `RFindAbove` that looks for roots above a fixed number n, as a
fixed point of R ↦ λ n f. if f n = 0 then n else R f (n + 1)
                 ~ λ n f. Cond ⬝ n (R f (Succ n)) (IsZero (f n))
-/
private def RFindAboveAuxPoly : SKI.Polynomial 3 :=
  IsZero ⬝' (&2 ⬝' &1) ⬝' &1 ⬝' (&0 ⬝' (SKI.Succ ⬝' &1) ⬝' &2)
-- /-- A term representing RFindAboveAux -/
-- private def RFindAboveAux : SKI := RFindAboveAuxPoly.toSKI
-- private lemma rfindAboveAux_def (R₀ f a : SKI) :
--     (RFindAboveAux ⬝ R₀ ⬝ a ⬝ f) ↠ SKI.Cond ⬝ a ⬝ (R₀ ⬝ (SKI.Succ ⬝ a) ⬝ f) ⬝ (IsZero ⬝ (f ⬝ a)) :=
--   RFindAboveAuxPoly.toSKI_correct [R₀, a, f] (by trivial)

-- theorem rfindAboveAux_base (R₀ f a : SKI) (hfa : IsChurch 0 (f ⬝ a)) :
--     (RFindAboveAux ⬝ R₀ ⬝ a ⬝ f) ↠ a := calc
--   _ ↠ SKI.Cond ⬝ a ⬝ (R₀ ⬝ (SKI.Succ ⬝ a) ⬝ f) ⬝ (IsZero ⬝ (f ⬝ a)) := rfindAboveAux_def _ _ _
--   _ ↠ if (Nat.beq 0 0) then a else (R₀ ⬝ (SKI.Succ ⬝ a) ⬝ f) := by
--       apply cond_correct
--       apply isZero_correct _ _ hfa
-- theorem rfindAboveAux_step (R₀ f a : SKI) {m : Nat} (hfa : IsChurch (m + 1) (f ⬝ a)) :
--     (RFindAboveAux ⬝ R₀ ⬝ a ⬝ f) ↠ R₀ ⬝ (SKI.Succ ⬝ a) ⬝ f := calc
--   _ ↠ SKI.Cond ⬝ a ⬝ (R₀ ⬝ (SKI.Succ ⬝ a) ⬝ f) ⬝ (IsZero ⬝ (f ⬝ a)) := rfindAboveAux_def _ _ _
--   _ ↠ if (Nat.beq (m+1) 0) then a else (R₀ ⬝ (SKI.Succ ⬝ a) ⬝ f) := by
--       apply cond_correct
--       apply isZero_correct _ _ hfa

/-- Find the minimal root of `fNat` above a number n -/
def RFindAbove : SKI :=
  (IsZero ⬝' (&2 ⬝' &1) ⬝' &1 ⬝' (&0 ⬝' (SKI.Succ ⬝' &1) ⬝' &2) : SKI.Polynomial 3).toSKI.fixedPoint

/-- One unfolding of `RFindAbove`: apply the fixed-point combinator once. -/
theorem RFindAbove_unfold (x g : SKI) : (RFindAbove ⬝ x ⬝ g) ↠
    (IsZero ⬝ (g ⬝ x)) ⬝ x ⬝ (RFindAbove ⬝ (SKI.Succ ⬝ x) ⬝ g) := by
  refine Relation.ReflTransGen.trans ?_ <| RFindAboveAuxPoly.toSKI_correct [RFindAbove, x, g] rfl
  apply MRed.head; apply MRed.head; exact fixedPoint_correct _

/-- Generalized root-finding that works with pointwise properties rather than a total
    function. At the root `m + n`, `f` yields Church 0; below, a nonzero Church numeral. -/
theorem RFindAbove_correct' (f x : SKI) (n m : Nat) (hx : x ⊩ m)
    (hf_root : ∀ y, y ⊩ (m + n) → (f ⬝ y) ⊩ 0)
    (hf_below : ∀ i < n, ∀ y, y ⊩ (m + i) → ∃ k, (f ⬝ y) ⊩ (k + 1)) :
    (RFindAbove ⬝ x ⬝ f) ⊩ (m + n) := by
  induction n generalizing m x with
  | zero =>
    apply hx.left_of_mRed
    exact (RFindAbove_unfold x f).trans <|
      realizes_beq_zero (hf_root x hx) x ((RFindAbove ⬝ (SKI.Succ ⬝ x) ⬝ f))
  | succ n ih =>
    have : (IsZero ⬝ (f ⬝ x)) ⊩ false :=
      realizes_beq_zero (hf_below 0 n.zero_lt_succ x hx).choose_spec
    refine Realizes.left_of_mRed ?_ ((RFindAbove_unfold x f).trans <| this ..)
    specialize ih (SKI.Succ ⬝ x) (m + 1) (realizes_succ hx) (by grind)
      (fun i hi y hy => hf_below (i + 1) (by lia) y (by grind))
    grind

theorem RFindAbove_correct {xf xm : SKI} {f : ℕ → ℕ} (hf : xf ⊩ f) {m : ℕ}
    (hm : xm ⊩ m) (n : Nat) (hroot : f (m + n) = 0) (hpos : ∀ i < n, f (m + i) ≠ 0) :
    (RFindAbove ⬝ xm ⬝ xf) ⊩ m + n := by
  apply RFindAbove_correct' xf xm n m hm
  · intro y hy
    exact hroot ▸ hf hy
  · intro i hi y hy
    use f (m + i) - 1, Nat.succ_pred_eq_of_ne_zero (hpos i hi) ▸ hf hy

/-- Ordinary root finding is root finding above zero -/
def RFind := RFindAbove ⬝ SKI.Zero
theorem RFind_correct {xf : SKI} {f : ℕ → ℕ} (hf : xf ⊩ f) (n : Nat) (hroot : f n = 0)
    (hpos : ∀ i < n, f i ≠ 0) : (RFind ⬝ xf) ⊩ n := by
  have : _ := RFindAbove_correct (n := n) (f := f) (hf := hf) (hm := realizes_zero)
  simp_rw [Nat.zero_add] at this
  exact this hroot hpos

-- /-! ### Further numeric operations -/

-- /-- Addition: λ n m. n Succ m -/
-- def AddPoly : SKI.Polynomial 2 := &0 ⬝' SKI.Succ ⬝' &1
-- /-- A term representing addition on church numerals -/
-- protected def Add : SKI := AddPoly.toSKI
-- theorem add_def (a b : SKI) : (SKI.Add ⬝ a ⬝ b) ↠ a ⬝ SKI.Succ ⬝ b :=
--   AddPoly.toSKI_correct [a, b] (by simp)

-- theorem add_correct (n m : Nat) (a b : SKI) (ha : IsChurch n a) (hb : IsChurch m b) :
--     IsChurch (n + m) (SKI.Add ⬝ a ⬝ b) := by
--   refine isChurch_trans (n + m) (a' := Church n SKI.Succ b) ?_ ?_
--   · calc
--     _ ↠ a ⬝ SKI.Succ ⬝ b := add_def a b
--     _ ↠ Church n SKI.Succ b := ha SKI.Succ b
--   · clear ha
--     induction n with
--       | zero => simp_rw [Nat.zero_add, Church]; exact hb
--       | succ n ih =>
--         simp_rw [Nat.add_right_comm, Church]
--         exact succ_correct _ _ ih

-- /-- Multiplication: λ n m. n (Add m) Zero -/
-- def MulPoly : SKI.Polynomial 2 := &0 ⬝' (SKI.Add ⬝' &1) ⬝' SKI.Zero
-- /-- A term representing multiplication on church numerals -/
-- protected def Mul : SKI := MulPoly.toSKI
-- theorem mul_def (a b : SKI) : (SKI.Mul ⬝ a ⬝ b) ↠ a ⬝ (SKI.Add ⬝ b) ⬝ SKI.Zero :=
--   MulPoly.toSKI_correct [a, b] (by simp)

-- theorem mul_correct {n m : Nat} {a b : SKI} (ha : IsChurch n a) (hb : IsChurch m b) :
--     IsChurch (n * m) (SKI.Mul ⬝ a ⬝ b) := by
--   refine isChurch_trans (n * m) (a' := Church n (SKI.Add ⬝ b) SKI.Zero) ?_ ?_
--   · exact Trans.trans (mul_def a b) (ha (SKI.Add ⬝ b) SKI.Zero)
--   · clear ha
--     induction n with
--       | zero => simp_rw [Nat.zero_mul, Church]; exact zero_correct
--       | succ n ih =>
--         simp_rw [Nat.add_mul, Nat.one_mul, Nat.add_comm, Church]
--         exact add_correct m (n * m) b (Church n (SKI.Add ⬝ b) SKI.Zero) hb ih

-- /-- Subtraction: λ n m. n Pred m -/
-- def SubPoly : SKI.Polynomial 2 := &1 ⬝' Pred ⬝' &0
-- /-- A term representing subtraction on church numerals -/
-- protected def Sub : SKI := SubPoly.toSKI
-- theorem sub_def (a b : SKI) : (SKI.Sub ⬝ a ⬝ b) ↠ b ⬝ Pred ⬝ a :=
--   SubPoly.toSKI_correct [a, b] (by simp)

-- theorem sub_correct (n m : Nat) (a b : SKI) (ha : IsChurch n a) (hb : IsChurch m b) :
--     IsChurch (n - m) (SKI.Sub ⬝ a ⬝ b) := by
--   refine isChurch_trans (n - m) (a' := Church m Pred a) ?_ ?_
--   · calc
--     _ ↠ b ⬝ Pred ⬝ a := sub_def a b
--     _ ↠ Church m Pred a := hb Pred a
--   · clear hb
--     induction m with
--       | zero => simp_rw [Nat.sub_zero, Church]; exact ha
--       | succ m ih =>
--         simp_rw [←Nat.sub_sub, Church]
--         exact pred_correct _ _ ih

-- /-- Comparison: (. ≤ .) := λ n m. IsZero ⬝ (Sub ⬝ n ⬝ m) -/
-- def LEPoly : SKI.Polynomial 2 := IsZero ⬝' (SKI.Sub ⬝' &0 ⬝' &1)
-- /-- A term representing comparison on church numerals -/
-- protected def LE : SKI := LEPoly.toSKI
-- theorem le_def (a b : SKI) : (SKI.LE ⬝ a ⬝ b) ↠ IsZero ⬝ (SKI.Sub ⬝ a ⬝ b) :=
--   LEPoly.toSKI_correct [a, b] (by simp)

-- theorem le_correct (n m : Nat) (a b : SKI) (ha : IsChurch n a) (hb : IsChurch m b) :
--     IsBool (n ≤ m) (SKI.LE ⬝ a ⬝ b) := by
--   simp only [← decide_eq_decide.mpr <| Nat.sub_eq_zero_iff_le]
--   apply isBool_trans (a' := IsZero ⬝ (SKI.Sub ⬝ a ⬝ b)) (h := le_def _ _)
--   apply isZero_correct
--   apply sub_correct <;> assumption

-- /-! ### Integer square root -/

-- /-- Inner condition for Sqrt: with &0 = n, &1 = k,
--     computes `if n < (k+1)² then 0 else 1`. -/
-- def SqrtCondPoly : SKI.Polynomial 2 :=
--   SKI.Cond ⬝' SKI.Zero ⬝' SKI.One
--            ⬝' (SKI.Neg ⬝' (SKI.LE ⬝' (SKI.Mul ⬝' (SKI.Succ ⬝' &1) ⬝' (SKI.Succ ⬝' &1)) ⬝' &0))

-- /-- SKI term for the inner condition of Sqrt -/
-- def SqrtCond : SKI := SqrtCondPoly.toSKI

-- /-- `SqrtCond ⬝ n ⬝ k` reduces to: return 0 if `(k+1)² > n`, else 1.
--     Used by `RFind` to locate the smallest such `k`, which is `√n`. -/
-- theorem sqrtCond_def (cn ck : SKI) :
--     (SqrtCond ⬝ cn ⬝ ck) ↠
--       SKI.Cond ⬝ SKI.Zero ⬝ SKI.One ⬝
--         (SKI.Neg ⬝ (SKI.LE ⬝ (SKI.Mul ⬝ (SKI.Succ ⬝ ck) ⬝ (SKI.Succ ⬝ ck)) ⬝ cn)) :=
--   SqrtCondPoly.toSKI_correct [cn, ck] (by simp)

-- /-- Sqrt n = smallest k such that (k+1)² > n, i.e., the integer square root.
--     Defined as `λ n. RFind (SqrtCond n)`. -/
-- def SqrtPoly : SKI.Polynomial 1 := RFind ⬝' (SqrtCond ⬝' &0)

-- /-- SKI term for integer square root -/
-- def Sqrt : SKI := SqrtPoly.toSKI

-- /-- `Sqrt ⬝ n` reduces to an `RFind` search for the smallest `k` with `(k+1)² > n`. -/
-- theorem sqrt_def (cn : SKI) : (Sqrt ⬝ cn) ↠ RFind ⬝ (SqrtCond ⬝ cn) :=
--   SqrtPoly.toSKI_correct [cn] (by simp)

-- /-- `Sqrt` correctly computes `Nat.sqrt`. -/
-- theorem sqrt_correct (n : Nat) (cn : SKI) (hcn : IsChurch n cn) :
--     IsChurch (Nat.sqrt n) (Sqrt ⬝ cn) := by
--   apply isChurch_trans _ (sqrt_def cn)
--   apply RFind_correct (fun k => if n < (k + 1) * (k + 1) then 0 else 1) (SqrtCond ⬝ cn)
--   · -- SqrtCond ⬝ cn correctly computes the function
--     intro i y hy
--     apply isChurch_trans _ (sqrtCond_def cn y)
--     have hsucc := succ_correct i y hy
--     have hle := le_correct _ n _ cn (mul_correct hsucc hsucc) hcn
--     have hneg := neg_correct _ _ hle
--     apply isChurch_trans _ (cond_correct _ _ _ _ hneg)
--     grind
--   · -- fNat (Nat.sqrt n) = 0
--     simp [Nat.lt_succ_sqrt]
--   · -- ∀ i < Nat.sqrt n, fNat i ≠ 0
--     grind [Nat.le_sqrt]

-- /-! ### Nat pairing (matching Mathlib's `Nat.pair`) -/

-- /-- NatPair a b = if a < b then b*b + a else a*a + a + b.
--     With &0 = a, &1 = b. The condition `a < b` is `¬(b ≤ a)`. -/
-- def NatPairPoly : SKI.Polynomial 2 :=
--   SKI.Cond ⬝' (SKI.Add ⬝' (SKI.Mul ⬝' &1 ⬝' &1) ⬝' &0)
--            ⬝' (SKI.Add ⬝' (SKI.Add ⬝' (SKI.Mul ⬝' &0 ⬝' &0) ⬝' &0) ⬝' &1)
--            ⬝' (SKI.Neg ⬝' (SKI.LE ⬝' &1 ⬝' &0))

-- /-- SKI term for Nat pairing -/
-- def NatPair : SKI := NatPairPoly.toSKI

-- /-- `NatPair ⬝ a ⬝ b` reduces to: if `a < b` then `b² + a`, else `a² + a + b`. -/
-- theorem natPair_def (ca cb : SKI) :
--     (NatPair ⬝ ca ⬝ cb) ↠
--       SKI.Cond ⬝ (SKI.Add ⬝ (SKI.Mul ⬝ cb ⬝ cb) ⬝ ca)
--                ⬝ (SKI.Add ⬝ (SKI.Add ⬝ (SKI.Mul ⬝ ca ⬝ ca) ⬝ ca) ⬝ cb)
--                ⬝ (SKI.Neg ⬝ (SKI.LE ⬝ cb ⬝ ca)) :=
--   NatPairPoly.toSKI_correct [ca, cb] (by simp)

-- /-- `NatPair` correctly computes `Nat.pair`. -/
-- theorem natPair_correct (a b : Nat) (ca cb : SKI)
--     (ha : IsChurch a ca) (hb : IsChurch b cb) :
--     IsChurch (Nat.pair a b) (NatPair ⬝ ca ⬝ cb) := by
--   simp only [Nat.pair]
--   apply isChurch_trans _ (natPair_def ca cb)
--   have hcond := neg_correct _ _ (le_correct b a cb ca hb ha)
--   apply isChurch_trans _ (cond_correct _ _ _ _ hcond)
--   by_cases hab : a < b
--   · grind [add_correct _ _ _ _ (mul_correct hb hb) ha]
--   · grind [add_correct _ _ _ _ (add_correct _ _ _ _ (mul_correct ha ha) ha) hb]

-- /-! ### Nat unpairing (matching Mathlib's `Nat.unpair`) -/

-- /-- `NatUnpairLeft n = if n - s² < s then n - s² else s` where `s = Nat.sqrt n`. -/
-- def NatUnpairLeftPoly : SKI.Polynomial 1 :=
--   let s := Sqrt ⬝' &0
--   let s2 := SKI.Mul ⬝' s ⬝' s
--   let diff := SKI.Sub ⬝' &0 ⬝' s2
--   let cond := SKI.Neg ⬝' (SKI.LE ⬝' s ⬝' diff)
--   SKI.Cond ⬝' diff ⬝' s ⬝' cond

-- /-- SKI term for left projection of Nat.unpair -/
-- def NatUnpairLeft : SKI := NatUnpairLeftPoly.toSKI

-- /-- `NatUnpairLeft ⬝ n` reduces to: let `s = √n` and `d = n - s²`;
--     return `d` if `d < s`, else `s`. -/
-- theorem natUnpairLeft_def (cn : SKI) :
--     (NatUnpairLeft ⬝ cn) ↠
--       SKI.Cond ⬝ (SKI.Sub ⬝ cn ⬝ (SKI.Mul ⬝ (Sqrt ⬝ cn) ⬝ (Sqrt ⬝ cn)))
--                ⬝ (Sqrt ⬝ cn)
--                ⬝ (SKI.Neg ⬝ (SKI.LE ⬝ (Sqrt ⬝ cn)
--                     ⬝ (SKI.Sub ⬝ cn ⬝ (SKI.Mul ⬝ (Sqrt ⬝ cn) ⬝ (Sqrt ⬝ cn))))) :=
--   NatUnpairLeftPoly.toSKI_correct [cn] (by simp)

-- /-- Common Church numeral witnesses for `Nat.sqrt` and the difference `n - (Nat.sqrt n)²`. -/
-- private theorem natUnpair_church (n : Nat) (cn : SKI) (hcn : IsChurch n cn) :
--     IsChurch (Nat.sqrt n) (Sqrt ⬝ cn) ∧
--     IsChurch (n - Nat.sqrt n * Nat.sqrt n)
--       (SKI.Sub ⬝ cn ⬝ (SKI.Mul ⬝ (Sqrt ⬝ cn) ⬝ (Sqrt ⬝ cn))) := by
--   have hs := sqrt_correct n cn hcn
--   exact ⟨hs, sub_correct n _ cn _ hcn (mul_correct hs hs)⟩

-- /-- `NatUnpairLeft` correctly computes the first component of `Nat.unpair`. -/
-- theorem natUnpairLeft_correct (n : Nat) (cn : SKI) (hcn : IsChurch n cn) :
--     IsChurch (Nat.unpair n).1 (NatUnpairLeft ⬝ cn) := by
--   apply isChurch_trans _ (natUnpairLeft_def cn)
--   obtain ⟨hs, hdiff⟩ := natUnpair_church n cn hcn
--   have hcond := neg_correct _ _ (le_correct _ _ _ _ hs hdiff)
--   apply isChurch_trans _ (cond_correct _ _ _ _ hcond)
--   by_cases h : n - n.sqrt ^ 2 < n.sqrt <;> grind [Nat.unpair]

-- /-- NatUnpairRight n = let s = sqrt n in if n - s² < s then s else n - s² - s. -/
-- def NatUnpairRightPoly : SKI.Polynomial 1 :=
--   let s := Sqrt ⬝' &0
--   let s2 := SKI.Mul ⬝' s ⬝' s
--   let diff := SKI.Sub ⬝' &0 ⬝' s2
--   let cond := SKI.Neg ⬝' (SKI.LE ⬝' s ⬝' diff)
--   SKI.Cond ⬝' s ⬝' (SKI.Sub ⬝' diff ⬝' s) ⬝' cond

-- /-- SKI term for right projection of Nat.unpair -/
-- def NatUnpairRight : SKI := NatUnpairRightPoly.toSKI

-- /-- `NatUnpairRight ⬝ n` reduces to: let `s = √n` and `d = n - s²`;
--     return `s` if `d < s`, else `d - s`. -/
-- theorem natUnpairRight_def (cn : SKI) :
--     (NatUnpairRight ⬝ cn) ↠
--       SKI.Cond ⬝ (Sqrt ⬝ cn)
--                ⬝ (SKI.Sub ⬝ (SKI.Sub ⬝ cn ⬝ (SKI.Mul ⬝ (Sqrt ⬝ cn) ⬝ (Sqrt ⬝ cn)))
--                             ⬝ (Sqrt ⬝ cn))
--                ⬝ (SKI.Neg ⬝ (SKI.LE ⬝ (Sqrt ⬝ cn)
--                     ⬝ (SKI.Sub ⬝ cn ⬝ (SKI.Mul ⬝ (Sqrt ⬝ cn) ⬝ (Sqrt ⬝ cn))))) :=
--   NatUnpairRightPoly.toSKI_correct [cn] (by simp)

-- /-- `NatUnpairRight` correctly computes the second component of `Nat.unpair`. -/
-- theorem natUnpairRight_correct (n : Nat) (cn : SKI) (hcn : IsChurch n cn) :
--     IsChurch (Nat.unpair n).2 (NatUnpairRight ⬝ cn) := by
--   apply isChurch_trans _ (natUnpairRight_def cn)
--   obtain ⟨hs, hdiff⟩ := natUnpair_church n cn hcn
--   have hcond := neg_correct _ _ (le_correct _ _ _ _ hs hdiff)
--   apply isChurch_trans _ (cond_correct _ _ _ _ hcond)
--   grind [Nat.unpair, sub_correct _ _ _ _ hdiff hs]

end SKI

end Cslib

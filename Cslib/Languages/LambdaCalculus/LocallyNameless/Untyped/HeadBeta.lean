/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring, Chris Henson
-/

import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta

/-!
# Head β reduction
-/

universe u

variable {Var : Type u}

namespace LambdaCalculus.LocallyNameless.Untyped.Term

/-- A single β-reduction step. -/
@[reduction_sys headBetaRs "βʰ"]
inductive HeadBeta : Term Var → Term Var → Prop
/-- Reduce an application to a lambda term. -/
| beta : LC (abs M) → LC N → HeadBeta (app (abs M) N) (M ^ N)
/-- Reduce a redex under an abstraction. -/
| abs (xs : Finset Var) : (∀ x ∉ xs, HeadBeta (M ^ fvar x) (N ^ fvar x)) →
    HeadBeta (abs M) (abs N)
| app : LC Z → ¬ M.Value → HeadBeta M N → HeadBeta (app M Z) (app N Z)

namespace HeadBeta

attribute [scoped grind] app

variable {M M' N N' : Term Var}

@[scoped grind _=_]
private lemma headBetaRs_Red_eq : M ⭢βʰ N ↔ HeadBeta M N := by
  have : (@headBetaRs Var).Red = HeadBeta := by rfl
  simp_all

/-- The left side of a reduction is locally closed. -/
@[scoped grind →]
lemma step_lc_l (step : M ⭢βʰ M') : LC M := by
  induction step <;> constructor
  all_goals assumption

variable [HasFresh Var] [DecidableEq Var]

omit [HasFresh Var] in

/-- Head reduction is a subrelation of full beta reduction. -/
lemma full_of_headBeta (step : M ⭢βʰ N) : M ⭢βᶠ N := by
  induction step
  case abs m n xs h ih =>
    apply FullBeta.abs (free_union Var)
    simpa
  all_goals constructor <;> first | grind | assumption

/-- Head reduction is deterministic. -/
lemma headBeta_deterministic (step : M ⭢βʰ N) (step' : M ⭢βʰ N') : N = N' := by
  induction step generalizing N'
  <;> cases step'
  case abs.abs m n xs step ih n' xs' hn' =>
    congr
    have ⟨fresh, _⟩ := fresh_exists <| free_union [fv] Var
    suffices n ^ fvar fresh = n' ^ fvar fresh by
      apply open_injective (x := fresh) <;> grind
    grind
  all_goals grind

/-- The right side of a reduction is locally closed. -/
@[scoped grind →]
lemma step_lc_r (step : M ⭢βʰ M') : LC M' := by
  induction step
  case' abs => constructor; assumption
  all_goals grind

/-- Substitution respects a single reduction step. -/
lemma redex_subst_cong (s s' : Term Var) (x y : Var) (step : s ⭢βʰ s') :
    s [ x := fvar y ] ⭢βʰ s' [ x := fvar y ] := by
  induction step
  case beta m n abs_lc n_lc =>
    cases abs_lc with | abs xs _ mem =>
      rw [subst_open x (fvar y) n m (by grind)]
      refine beta ?_ (by grind)
      exact subst_lc (LC.abs xs m mem) (LC.fvar y)
  case abs m' m xs mem ih =>
    apply abs (free_union Var)
    grind
  case app z m n z_lc hm_val h ih =>
    cases m <;> grind

/-- Abstracting then closing preserves a single reduction. -/
lemma step_abs_close {x : Var} (step : M ⭢βʰ M') : M⟦0 ↜ x⟧.abs ⭢βʰ M'⟦0 ↜ x⟧.abs := by
  apply abs ∅
  grind [redex_subst_cong]

/-- Abstracting then closing preserves multiple reductions. -/
lemma redex_abs_close {x : Var} (step : M ↠βʰ M') : (M⟦0 ↜ x⟧.abs ↠βʰ M'⟦0 ↜ x⟧.abs) :=  by
  induction step using Relation.ReflTransGen.trans_induction_on
  case refl => rfl
  case single ih => exact Relation.ReflTransGen.single (step_abs_close ih)
  case trans l r => exact .trans l r

/-- Multiple reduction of opening implies multiple reduction of abstraction. -/
theorem redex_abs_cong (xs : Finset Var) (cofin : ∀ x ∉ xs, (M ^ fvar x) ↠βʰ (M' ^ fvar x)) :
    M.abs ↠βʰ M'.abs := by
  have ⟨fresh, _⟩ := fresh_exists <| free_union [fv] Var
  rw [open_close fresh M 0 ?_, open_close fresh M' 0 ?_]
  all_goals grind [redex_abs_close]

end LambdaCalculus.LocallyNameless.Untyped.Term.HeadBeta

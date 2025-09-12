/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

import Cslib.Languages.LambdaCalculus.LocallyNameless.Context
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Properties
import Mathlib.Data.List.Sigma

/-! # Non-idempotent intersection types

A presentation of non-idempotent intersection types (Niit) for the lambda calculus, using the
locally nameless presentation.

### References

- See slides <https://pageperso.lis-lab.fr/~giulio.guerrieri/ECI2024/day4.pdf>
-/

universe u v

variable {Var : Type u} {Base : Type v} [DecidableEq Var]

open LambdaCalculus.LocallyNameless.Untyped Term

namespace LambdaCalculus.LocallyNameless.Niit

inductive LTy (Base : Type v)
  /-- Base type -/
  | base : Base → LTy Base
  /-- Arrow type -/
  | arrow : List (LTy Base) → LTy Base → LTy Base

inductive Ty (Base : Type v)
  /-- Linear types -/
  | lin : LTy Base → Ty Base
  /-- Multitypes -/
  | multi : List (LTy Base) → Ty Base

scoped infixr:70 " ⊸ " => LTy.arrow

open LTy Ty Context List

inductive Typing : Term Var → Ty Base → Context Var (List (LTy Base)) → Type _
  /-- Variables are typed with a sigleton -/
  | var {x : Var} {A : LTy Base} : Typing (fvar x) (lin A) [⟨x,[A]⟩]
  /-- Abstractions are typed with arrows, multitypes in argument position, linear in output -/
  | abs {M : List (LTy Base)} {Γ : Context Var (List (LTy Base))} {A : LTy Base}
      (t : Term Var) (L : Finset Var) :
    (∀ x ∉ L, Typing (t ^ fvar x) (lin A) (⟨x,M⟩ :: Γ)) → Typing t.abs  (lin <| M ⊸ A) Γ
  /-- Application -/
  | app {Γ Δ : Context Var (List (LTy Base))} {M : List (LTy Base)} {A : LTy Base}
      {s t : Term Var} :
    Typing s (lin <| M ⊸ A) Γ → Typing t (multi M) Γ → Typing (app s t) (lin A) (Γ ++ Δ)
  /-- Bang rule -/
  | bang {t : Term Var} :
      (Tys : List (LTy Base × Context Var (List <| LTy Base))) →
      (Ders : ∀ τ ∈ Tys, Typing t (lin τ.1) τ.2) →
    Typing t (multi <| Tys.map Prod.fst) (Tys.map Prod.snd).flatten
  -- Q: does this need permutation rule(s)

scoped notation:50 Γ " ⊢' " t " ∶ " A:arg => Typing t A Γ

variable {Γ : Context Var (List (LTy Base))} {A C : LTy Base}

[HasFresh Var]

example (D : Typing (abs (bvar 0)) (lin C) Γ) : ∃ B : LTy Base, C = [B] ⊸ B := by
  cases D
  case abs M A L h =>
    replace h := h (fresh L) (fresh_notMem L)
    simp only [open', openRec, ↓reduceIte] at h
    cases h
    use A

-- example (D : Typing (abs (app (bvar 0) (bvar 0))) (lin C) Γ) :
--     ∃ (M : List (LTy Base)) (B : LTy Base), C = ((M ⊸ B) :: M) ⊸ B := by
--   cases D
--   case abs N A L h =>
--     replace h := h (fresh L) (fresh_notMem L)
--     cases h


end Niit

end LambdaCalculus.LocallyNameless

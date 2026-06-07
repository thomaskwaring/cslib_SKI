/-
Copyright (c) 2026 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Cslib.Foundations.Semantics.LTS.Basic

/-!
# Finite executions of LTS
-/

@[expose] public section

namespace Cslib.LTS

variable {State Label : Type*} {lts : LTS State Label}

inductive Execution (lts : LTS State Label) : State → List Label → State → List State → Prop where
  | nil (s : State) : lts.Execution s [] s [s]
  | cons (h : lts.Tr s μ s') : lts.Execution s' μs s'' ss → lts.Execution s (μ :: μs) s'' (s :: ss)

namespace Execution

@[grind →]
lemma length_eq (h : lts.Execution s μs s' ss) : μs.length + 1 = ss.length := by
  induction h <;> simp_all

lemma mem_head?_states (h : lts.Execution s μs s' ss) : s ∈ ss.head? := by
  cases h <;> simp

@[grind .]
lemma getElem_zero_states (h : lts.Execution s μs s' ss) (hl : 0 < ss.length) :
  ss[0] = s := by cases h <;> rfl

lemma mem_getLast?_states (h : lts.Execution s μs s' ss) : s' ∈ ss.getLast? := by
  induction h <;> grind

lemma mTr (h : lts.Execution s μs s' ss) : lts.MTr s μs s' := by
  induction h with
  | nil => exact MTr.refl
  | cons h h' ih => exact MTr.stepL h ih

lemma of_cons (h : lts.Execution s (μ :: μs) s' (s0 :: ss)) :
    lts.Execution (ss[0]'(by grind)) μs s' ss := by
  cases h
  case cons htr hmtr => rwa [hmtr.getElem_zero_states]

end Execution

lemma MTr.exists_execution (h : lts.MTr s μs s') :
    ∃ ss, lts.Execution s μs s' ss := by
  induction h with
  | @refl s => use [s], .nil s
  | @stepL s μ s' μs s'' htr hmtr ih =>
    obtain ⟨ss, ih⟩ := ih
    use s :: ss, ih.cons htr

theorem mTr_iff_exists_execution :
    lts.MTr s μs s' ↔ ∃ ss, lts.Execution s μs s' ss :=
  ⟨MTr.exists_execution, fun ⟨_, h⟩ => h.mTr⟩

theorem Execution.comp (he : lts.Execution s μs s' ss) (he' : lts.Execution s' μs' s'' ss') :
    lts.Execution s (μs ++ μs') s'' (ss ++ ss'.tail) := by
  induction he with
  | nil s =>
    rw [←ss'.cons_head?_tail (a := s) he'.mem_head?_states] at he'
    simpa
  | @cons s μ smid μs s' ss htr he ih => exact (ih he').cons htr

theorem Execution.take (he : lts.Execution s μs s' ss) (n : ℕ) :
    lts.Execution s (μs.take n) (ss.getD n s') (ss.take (n + 1)) := by
  induction he generalizing n with
  | nil s => cases n <;> simpa using .nil s
  | @cons s μ s' μs s'' ss htr he ih =>
    cases n with
    | zero => simpa using .nil s
    | succ n => simpa using (ih n).cons htr

theorem Execution.drop (he : lts.Execution s μs s' ss) {n : ℕ}
    (hn : n < ss.length) : lts.Execution ss[n] (μs.drop n) s' (ss.drop n) := by
  induction he generalizing n with
  | nil s =>
    obtain rfl : n = 0 := by grind
    simpa using .nil s
  | @cons s μ s' μs s'' ss htr he ih =>
    cases n with
    | zero => simpa using he.cons htr
    | succ n => simpa using ih (n := n) (by grind)

end Cslib.LTS

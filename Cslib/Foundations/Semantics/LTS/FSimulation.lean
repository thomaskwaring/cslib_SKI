/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Cslib.Foundations.Data.Relation
public import Cslib.Foundations.Semantics.LTS.Bisimulation
public import Init.Data.Range.Polymorphic.Iterators
public import Mathlib.Data.Fin.SuccPredOrder


@[expose] public section

namespace Cslib.LTS

open Function Relation

variable {State State₁ State₂ Label : Type*} {lts : LTS State Label} {lts₁ : LTS State₁ Label}
  {lts₂ : LTS State₂ Label} {r : State₁ → State₂ → Prop}

def _root_.Function.Graph {α β : Type*} (f : α → β) : α → β → Prop := fun a b => f a = b

def IsFSimulation (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label)
    (f : State₁ → State₂) : Prop := ∀ s s' μ, lts₁.Tr s μ s' → lts₂.Tr (f s) μ (f s')

lemma IsFSimulation.isSimulation_graph {f : State₁ → State₂}
    (hf : IsFSimulation lts₁ lts₂ f) : IsSimulation lts₁ lts₂ f.Graph := by
  rintro s _ rfl μ s' h
  use (discharger := rfl) f s', hf s s' μ h

lemma isSimulation_graph_iff_isFSimulation (f : State₁ → State₂) :
    IsSimulation lts₁ lts₂ f.Graph ↔ IsFSimulation lts₁ lts₂ f := by
  refine ⟨?_, IsFSimulation.isSimulation_graph⟩
  intro h s₁ s₁' μ htr
  obtain ⟨_, htr', rfl⟩ := h s₁ (f s₁) rfl μ s₁' htr
  exact htr'

def IsOpFibration (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label)
    (f : State₁ → State₂) : Prop :=
  ∀ s₁ s₂ μ, lts₂.Tr (f s₁) μ s₂ → ∃ s₁', lts₁.Tr s₁ μ s₁' ∧ f s₁' = s₂

lemma IsOpFibration.isSimulation_flip_graph {f : State₁ → State₂} (hf : IsOpFibration lts₁ lts₂ f) :
    IsSimulation lts₂ lts₁ (flip f.Graph) := by
  rintro _ s₁ rfl μ s₂ htr
  obtain ⟨s₁', htr', rfl⟩ := hf _ _ _ htr
  use s₁', htr'
  rfl

lemma isOpFibration_iff_isSimulation_flip_graph (f : State₁ → State₂) :
    IsOpFibration lts₁ lts₂ f ↔ IsSimulation lts₂ lts₁ (flip f.Graph) := by
  refine ⟨IsOpFibration.isSimulation_flip_graph, ?_⟩
  intro h s₁ s₂ μ htr
  obtain ⟨s₁', htr', rfl⟩ := h (f s₁) s₁ rfl μ s₂ htr
  use s₁', htr'

theorem isBisimulation_graph_iff (f : State₁ → State₂) :
    IsBisimulation lts₁ lts₂ f.Graph ↔ IsFSimulation lts₁ lts₂ f ∧ IsOpFibration lts₁ lts₂ f := by
  rw [IsBisimulation.isSimulation_iff, isOpFibration_iff_isSimulation_flip_graph,
    isSimulation_graph_iff_isFSimulation]

structure _root_.Function.RelGraph {α β : Type*} (r : α → β → Prop) : Type _ where
  fst : α
  snd : β
  h : r fst snd

def relProd (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label) (r : State₁ → State₂ → Prop) :
    LTS r.RelGraph Label where
  Tr p μ p' := lts₁.Tr p.fst μ p'.fst ∧ lts₂.Tr p.snd μ p'.snd

lemma IsSimulation.isOpFibration_relGraph_fst (hr : IsSimulation lts₁ lts₂ r) :
    IsOpFibration (relProd lts₁ lts₂ r) lts₁ RelGraph.fst := by
  intro ⟨s₁, s₂, h⟩ s₁' μ (htr₁ : lts₁.Tr s₁ μ s₁')
  obtain ⟨s₂', htr₂, h'⟩ := hr _ _ h _ _ htr₁
  use! ⟨s₁', s₂', h'⟩, htr₁, htr₂

lemma IsSimulation.isOpFibration_relGraph_snd (hr : IsSimulation lts₂ lts₁ (flip r)) :
    IsOpFibration (relProd lts₁ lts₂ r) lts₂ RelGraph.snd := by
  intro ⟨s₁, s₂, h⟩ s₂' μ (htr₂ : lts₂.Tr s₂ μ s₂')
  obtain ⟨s₁', htr₁, h'⟩ := hr _ _ h _ _ htr₂
  use! ⟨s₁', s₂', h'⟩, htr₁, htr₂

lemma isFSimulation_relGraph_fst (r : State₁ → State₂ → Prop) :
    IsFSimulation (relProd lts₁ lts₂ r) lts₁ RelGraph.fst := by
  intro _ _ _ ⟨htr, _⟩
  exact htr

lemma isFSimulation_relGraph_snd (r : State₁ → State₂ → Prop) :
    IsFSimulation (relProd lts₁ lts₂ r) lts₂ RelGraph.snd := by
  intro _ _ _ ⟨_, htr⟩
  exact htr

def KernelPair {α β γ : Type*} (f : α → β) (g : α → γ) (b : β) (c : γ) : Prop :=
    ∃ a, f a = b ∧ g a = c

@[simp] lemma flip_kernelPair {α β γ : Type*} (f : α → β) (g : α → γ) :
    flip (KernelPair f g) = KernelPair g f := by grind [flip, KernelPair]

lemma RelGraph.kernelPair {α β : Type*} (r : α → β → Prop) :
    KernelPair (α := r.RelGraph) RelGraph.fst RelGraph.snd = r := by
  ext a b
  constructor
  · intro ⟨p, ha, hb⟩
    subst a b
    exact p.h
  · intro h
    use ⟨a, b, h⟩

lemma isSimulation_kernelPair {f : State → State₁} {g : State → State₂}
    (hf : IsOpFibration lts lts₁ f) (hg : IsFSimulation lts lts₂ g) :
    IsSimulation lts₁ lts₂ (KernelPair f g) := by
  rintro _ _ ⟨s, rfl, rfl⟩ μ s₁ htr₁
  obtain ⟨s', htr, rfl⟩ := hf s s₁ μ htr₁
  use g s', hg s s' μ htr, s'

theorem bisimilarity_iff_exists {State₁ State₂ : Type u} (lts₁ : LTS State₁ Label)
    (lts₂ : LTS State₂ Label) (s₁ : State₁) (s₂ : State₂) :
    s₁ ~[lts₁,lts₂] s₂ ↔ ∃ (State : Type u) (lts : LTS State Label)
      (f : State → State₁) (g : State → State₂),
      KernelPair f g s₁ s₂ ∧ IsFSimulation lts lts₁ f ∧ IsFSimulation lts lts₂ g ∧
        IsOpFibration lts lts₁ f ∧ IsOpFibration lts lts₂ g := by
  constructor
  · intro h
    use (Bisimilarity lts₁ lts₂).RelGraph, (relProd lts₁ lts₂ (Bisimilarity lts₁ lts₂)),
      RelGraph.fst, RelGraph.snd, ⟨⟨s₁, s₂, h⟩, rfl, rfl⟩, isFSimulation_relGraph_fst _,
      isFSimulation_relGraph_snd _
    constructor
    · exact IsSimulation.isOpFibration_relGraph_fst (Bisimilarity.isBisimulation _ _).isSimulation
    · apply IsSimulation.isOpFibration_relGraph_snd <|
        IsBisimulation.isSimulation_iff.mp (Bisimilarity.isBisimulation _ _) |>.2
  · rintro ⟨State, lts, f, g, hrel, hf, hg, hf', hg'⟩
    use KernelPair f g, hrel
    rw [IsBisimulation.isSimulation_iff, flip_kernelPair]
    constructor <;> apply isSimulation_kernelPair <;> assumption

def oneTr (μ : Label) : LTS Bool Label where
  Tr b1 μ' b2 := μ' = μ ∧ b1 = false ∧ b2 = true

lemma oneTr_tr : (oneTr μ).Tr false μ true := ⟨rfl, rfl, rfl⟩

lemma isFSimulation_oneTr_iff (μ : Label) (f : Bool → State) :
    IsFSimulation (oneTr μ) lts f ↔ lts.Tr (f false) μ (f true) := by
  constructor
  · intro h
    exact h false true μ oneTr_tr
  · rintro h _ _ _ ⟨rfl, rfl, rfl⟩
    exact h

theorem isOpFibration_iff (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label)
    (f : State₁ → State₂) : IsOpFibration lts₁ lts₂ f ↔ ∀ (μ : Label) (g : Bool → State₂)
    (_ : IsFSimulation (oneTr μ) lts₂ g) (s₁ : State₁) (_ : f s₁ = g false),
    ∃ g' : Bool → State₁, IsFSimulation (oneTr μ) lts₁ g' ∧ g' false = s₁ ∧ f ∘ g' = g := by
  simp_rw [isFSimulation_oneTr_iff]
  constructor
  · intro hf μ g hg s₁ heq
    obtain ⟨s₁', htr, heq'⟩ := hf s₁ (g true) μ (heq ▸ hg)
    refine ⟨Bool.rec s₁ s₁', htr, rfl, ?_⟩
    ext b
    cases b <;> simpa
  · intro h s₁ s₂ μ htr
    obtain ⟨g', hg', rfl, hcomp⟩ := h μ (Bool.rec (f s₁) s₂) htr s₁ rfl
    use g' true, hg'
    simpa using congr_fun hcomp true

-- abbrev Path (Label : Type*) (n : ℕ) := Fin n → Label

-- namespace Path

-- variable {p : Path Label n}

-- inductive Tr (p : Path Label n) : Fin (n + 1) → Label → Fin (n + 1) → Prop
--   | step (i : Fin n) : p.Tr i.castSucc (p i) i.succ

-- def lts (p : Path Label n) : LTS (Fin <| n + 1) Label := {Tr := p.Tr}

-- lemma mk_tr (i : Fin n) : p.lts.Tr i.castSucc (p i) i.succ := .step i

-- lemma tr_lts_iff (i j : Fin (n + 1)) (μ : Label) :
--     p.lts.Tr i μ j ↔ ∃ (i' : Fin n), μ = p i' ∧ i = i'.castSucc ∧ j = i'.succ := by
--   constructor
--   · rintro ⟨i⟩; use i
--   · rintro ⟨i, rfl, rfl, rfl⟩; exact mk_tr i

-- instance : p.lts.Deterministic where
--   deterministic s1 μ s2 s2':= by
--     simp_rw [tr_lts_iff]
--     rintro ⟨i', rfl, rfl, rfl⟩ ⟨i'', -, hi, rfl⟩
--     congr
--     exact Fin.castSucc_injective _ hi

-- -- lemma mk_mtr' {i k : ℕ} (h : i + k < n) :
-- --     p.lts.MTr ⟨i, by grind⟩
-- --       ((⟨i, by grind⟩...=⟨i + k, by grind⟩).toList.map p) ⟨i + k + 1, by grind⟩ := by
-- --   induction k generalizing i with
-- --   | zero =>
-- --     have : ((⟨i, by grind⟩...=⟨i + 0, by grind⟩).toList : List (Fin n)) = [⟨i, by grind⟩] := by
-- --       simp [Std.Rcc.toList_eq_if_roc, Std.Roc.toList_eq_nil_iff]
-- --     rw [this]
-- --     simpa using mk_tr ⟨i, by grind⟩
-- --   | succ k ih =>
-- --     rw [Std.Rcc.toList_eq_if_roc, Std.Roc.toList_eq_match]
-- --     have : i + 1 < n := by grind
-- --     simp only [Fin.mk_le_mk, Nat.le_add_right, ↓reduceIte, Fin.pRangeSucc?_eq, Fin.addNat?_eq_dif,
-- --       this, ↓reduceDIte, Nat.add_le_add_iff_left, Nat.le_add_left, List.map_cons]
-- --     simp_rw [← Nat.succ_add_eq_add_succ i k] at h ⊢
-- --     refine MTr.stepL (p.mk_tr ⟨i, by grind⟩) ?_
-- --     simpa [Std.Rcc.toList_eq_if_roc] using ih h

-- -- lemma mk_mtr {i j : Fin n} (h : i ≤ j) :
-- --     p.lts.MTr i.castSucc ((i...j).toList.map p) j.castSucc := by
-- --   rcases (Order.le_iff_eq_or_le_pred.mp h) with (rfl | h)
-- --   · sorry
-- --   · have hi : i.castSucc = ⟨i, by grind⟩ := by ext; simp
-- --     have hadd : (i : ℕ) + (Order.pred j - i) = Order.pred j := by grind
-- --     have hl : (i...j).toList =
-- --         ((⟨i, by grind⟩ : Fin n)...=⟨i + (Order.pred j - i), by grind⟩).toList := by
-- --       simp [hadd]
--     -- have hj : j.castSucc = ⟨i + (Order.pred j - i) + 1, by grind⟩ := by simp [Order.pred]

--     -- rw [hi, hj, hl]
--     -- apply mk_mtr'
--     -- grind

-- -- lemma mtr_iff (i j : Fin (n + 1)) (μs : List Label) :
-- --     p.lts.MTr i μs j ↔
-- --     ∃ (i' j' : Fin n), μs = (i'...j').toList.map p ∧ i ≤ j ∧ i = i'.castSucc ∧ j = j'.castSucc := by
-- --   constructor
-- --   ·

-- end Path

end Cslib.LTS

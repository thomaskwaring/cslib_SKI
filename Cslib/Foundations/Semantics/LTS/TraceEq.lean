/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Foundations.Semantics.LTS.Basic
public import Cslib.Foundations.Semantics.LTS.Simulation

/-!
# Trace Equivalence

Definitions and results on trace equivalence for `LTS`s.

## Main definitions

- `LTS.traces`: the set of traces of a state.
- `TraceEq s₁ s₂`: `s₁` and `s₂` are trace equivalent, i.e., they have the same sets of traces.

## Notations

- `s₁ ~tr[lts] s₂`: the states `s₁` and `s₂` are trace equivalent in `lts`.

## Main statements

- `TraceEq.eqv`: trace equivalence is an equivalence relation (see `Equivalence`).
- `Deterministic.isSimulation_traceEq`: in any deterministic `LTS`, trace equivalence is a
  simulation.

-/

@[expose] public section

namespace Cslib.LTS

open Deterministic

/-- The traces of a state `s` is the set of all lists of labels `μs` such that there is a multi-step
transition labelled by `μs` originating from `s`. -/
def traces (lts : LTS State Label) (s : State) := { μs : List Label | ∃ s', lts.MTr s μs s' }

lemma mem_traces_iff {lts : LTS State Label} (μs : List Label) :
  μs ∈ lts.traces s ↔ ∃ s', lts.MTr s μs s' := Iff.rfl

lemma mem_traces_singleton_iff {lts : LTS State Label} (μ : Label) :
    [μ] ∈ lts.traces s ↔ ∃ s', lts.Tr s μ s' := by
  simp_rw [mem_traces_iff, MTr.singleton_iff lts s μ]

lemma mem_traces_cons_iff {lts : LTS State Label} (μ : Label) (μs : List Label) :
    (μ :: μs) ∈ lts.traces s ↔ ∃ s', lts.Tr s μ s' ∧ μs ∈ lts.traces s' := by
  simp_rw [mem_traces_iff, MTr.cons_iff]
  grind

/-- If there is a multi-step transition from `s` labelled by `μs`, then `μs` is in the traces of
`s`. -/
theorem traces_in {lts : LTS State Label} (h : lts.MTr s μs s') : μs ∈ lts.traces s := by exists s'

theorem Tr.traces_eq_of_deterministic {lts : LTS State Label} [lts.Deterministic]
    (h : lts.Tr s μ s') : lts.traces s' = {μs | μ :: μs ∈ lts.traces s} := by
  ext μs
  constructor
  · intro ⟨s'', hmtr⟩
    use s'', MTr.stepL h hmtr
  · intro ⟨s'', hmtr⟩
    rcases hmtr with (_ | ⟨htr, hmtr⟩)
    rw [←deterministic _ _ _ _ h htr] at hmtr
    exact ⟨s'', hmtr⟩

theorem MTr.traces_eq_of_deterministic {lts : LTS State Label} [lts.Deterministic]
    (h : lts.MTr s μs s') : lts.traces s' = {μs' | μs ++ μs' ∈ lts.traces s} := by
  ext μs'
  constructor
  · intro ⟨s'', hmtr⟩
    use s'', h.comp _ hmtr
  · intro ⟨s'', hmtr⟩
    obtain ⟨smid, hmid, hmid'⟩ := hmtr.split
    rw [Deterministic.eq_of_mtr h hmid]
    use s'', hmid'

theorem IsSimulation.traces_subset (hr : IsSimulation lts₁ lts₂ r) (hrel : r s₁ s₂) :
    lts₁.traces s₁ ⊆ lts₂.traces s₂ := by
  intro μs ⟨s₁', h₁⟩
  obtain ⟨s₂', h₂, _⟩ := hr.sim_trace hrel μs s₁' h₁
  exact ⟨s₂', h₂⟩

/-- Two states are trace equivalent if they have the same set of traces. -/
def TraceEq (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label)
    (s₁ : State₁) (s₂ : State₂) :=
  lts₁.traces s₁ = lts₂.traces s₂

/--
Notation for trace equivalence.

Differently from standard pen-and-paper presentations, we require the LTSs to be mentioned
explicitly.
-/
scoped notation s " ~tr[" lts₁ "," lts₂ "] " s' => TraceEq lts₁ lts₂ s s'

/-- Homogeneous trace equivalence compares states on the same LTS. -/
abbrev HomTraceEq (lts : LTS State Label) := TraceEq lts lts

/-- Notation for homogeneous trace equivalence. -/
scoped notation s:max " ~tr[" lts "] " s':max => HomTraceEq lts s s'

/-- Homogeneous trace equivalence is reflexive. -/
@[refl] theorem HomTraceEq.refl (s : State) : s ~tr[lts] s := rfl

@[simp] theorem TraceEq.flip_eq : flip (TraceEq lts₁ lts₂) = TraceEq lts₂ lts₁ := by
  ext s₁ s₂
  grind [flip, TraceEq]

/-- Trace equivalence is symmetric. -/
theorem TraceEq.symm (h : s₁ ~tr[lts₁,lts₂] s₂) : s₂ ~tr[lts₂,lts₁] s₁ := by
  rwa [←flip_eq]

/-- Trace equivalence is transitive. -/
theorem TraceEq.trans (h1 : s₁ ~tr[lts₁,lts₂] s₂) (h2 : s₂ ~tr[lts₂,lts₃] s₃) :
    s₁ ~tr[lts₁,lts₃] s₃ := Eq.trans h1 h2

/-- Homogeneous trace equivalence is an equivalence relation. -/
theorem HomTraceEq.eqv : Equivalence (· ~tr[lts] ·) where
  refl := HomTraceEq.refl
  symm := TraceEq.symm
  trans := TraceEq.trans

/-- `calc` support for simulation equivalence. -/
instance : Trans (TraceEq lts₁ lts₂) (TraceEq lts₂ lts₃) (TraceEq lts₁ lts₃) where
  trans := TraceEq.trans

lemma TraceEq.exists_mtr_of_mtr {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label}
    (h : s₁ ~tr[lts₁,lts₂] s₂) (htr : lts₁.MTr s₁ μs s₁') : ∃ s₂', lts₂.MTr s₂ μs s₂' := by
  rw [←mem_traces_iff, ←h]
  exact ⟨s₁', htr⟩

lemma TraceEq.exists_tr_of_tr {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label}
    (h : s₁ ~tr[lts₁,lts₂] s₂) (htr : lts₁.Tr s₁ μ s₁') : ∃ s₂', lts₂.Tr s₂ μ s₂' := by
  rw [←mem_traces_singleton_iff, ←h, mem_traces_singleton_iff]
  exact ⟨s₁', htr⟩

lemma TraceEq.traceEq_of_tr_of_tr {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label}
    [hdet₁ : lts₁.Deterministic] [hdet₂ : lts₂.Deterministic] (h : s₁ ~tr[lts₁,lts₂] s₂)
    (htr₁ : lts₁.Tr s₁ μ s₁') (htr₂ : lts₂.Tr s₂ μ s₂') : s₁' ~tr[lts₁,lts₂] s₂' := by
  rw [TraceEq] at h
  simp_rw [TraceEq, htr₁.traces_eq_of_deterministic, htr₂.traces_eq_of_deterministic, h]

/-- In deterministic LTSs, trace equivalence is a simulation. -/
theorem Deterministic.isSimulation_traceEq {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label}
    [hdet₁ : lts₁.Deterministic] [hdet₂ : lts₂.Deterministic] :
    IsSimulation lts₁ lts₂ (TraceEq lts₁ lts₂) := by
  intro s₁ s₂ h μ s₁' htr1
  obtain ⟨s₂', htr2⟩ := h.exists_tr_of_tr htr1
  use s₂', htr2, h.traceEq_of_tr_of_tr htr1 htr2

theorem SimulationEquiv.traceEq (h : s₁ ≤≥[lts₁,lts₂] s₂) : s₁ ~tr[lts₁,lts₂] s₂ := by
  obtain ⟨⟨_, h, hr⟩, _, h', hr'⟩ := h
  exact (hr.traces_subset h).antisymm (hr'.traces_subset h')

theorem Deterministic.traceEq_iff_simulationEquiv {lts₁ : LTS State₁ Label}
    {lts₂ : LTS State₂ Label} [hdet₁ : lts₁.Deterministic] [hdet₂ : lts₂.Deterministic]
    (s₁ : State₁) (s₂ : State₂) : (s₁ ~tr[lts₁,lts₂] s₂) ↔ s₁ ≤≥[lts₁,lts₂] s₂ :=
  ⟨fun h =>
    ⟨⟨_, h, Deterministic.isSimulation_traceEq⟩, _, h.symm, Deterministic.isSimulation_traceEq⟩,
    SimulationEquiv.traceEq⟩

end Cslib.LTS

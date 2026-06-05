/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Thomas Waring
-/

module

public import Cslib.Foundations.Data.Relation
public import Cslib.Foundations.Semantics.LTS.Simulation
public import Cslib.Foundations.Semantics.LTS.TraceEq

/-! # Bisimulation and Bisimilarity

A bisimulation is a binary relation on the states of two `LTS`s, which establishes a tight semantic
correspondence. More specifically, if two states `s₁` and `s₂` are related by a bisimulation, then
`s₁` can mimic all transitions of `s₂` and vice versa. Furthermore, the derivatives reaches through
these transitions remain related by the bisimulation.

Bisimilarity is the largest bisimulation: given an `LTS`, it relates any two states that are related
by a bisimulation for that LTS.

Weak bisimulation (resp. bisimilarity) is the relaxed version of bisimulation (resp. bisimilarity)
whereby internal actions performed by processes can be ignored.

For an introduction to theory of bisimulation, we refer to [Sangiorgi2011].

## Main definitions

- `lts.IsBisimulation r`: the relation `r` is a bisimulation for the LTS `lts`.
- `Bisimilarity lts` is the binary relation on the states of `lts` that relates any two states
related by some bisimulation on `lts`.
- `lts.IsBisimulationUpTo r`: the relation `r` is a bisimulation up to bisimilarity (this is known
as one of the 'up to' techniques for bisimulation).

- `lts.IsWeakBisimulation r`: the relation `r` on the states of the LTS `lts` is a weak
bisimulation.
- `WeakBisimilarity lts` is the binary relation on the states of `lts` that relates any two states
related by some weak bisimulation on `lts`.
- `lts.IsSWBisimulation` is a more convenient definition for establishing weak bisimulations, which
we prove to be sound and complete.

## Notations

- `s₁ ~[lts] s₂`: the states `s₁` and `s₂` are bisimilar in the LTS `lts`.
- `s₁ ≈[lts] s₂`: the states `s₁` and `s₂` are weakly bisimilar in the LTS `lts`.

## Main statements

- `LTS.IsBisimulation.inv`: the inverse of a bisimulation is a bisimulation.
- `Bisimilarity.eqv`: bisimilarity is an equivalence relation (see `Equivalence`).
- `Bisimilarity.isBisimulation`: bisimilarity is itself a bisimulation.
- `IsBisimulation.le_bisimilarity`: bisimilarity is the largest bisimulation.
- `Bisimilarity.gfp`: the union of bisimilarity and any bisimulation is equal to bisimilarity.
- `LTS.IsBisimulationUpTo.isBisimulation`: any bisimulation up to bisimilarity is a bisimulation.
- `LTS.IsBisimulation.traceEq`: any bisimulation that relates two states implies that they are
trace equivalent (see `TraceEq`).
- `Bisimilarity.deterministic_bisim_eq_traceEq`: in a deterministic LTS, bisimilarity and trace
equivalence coincide.
- `Bisimilarity.symm_simulation`: bisimilarity can be characterized through symmetric simulations.
- `WeakBisimilarity.weakBisim_eq_swBisim`: weak bisimulation and sw-bisimulation coincide.
- `WeakBisimilarity.eqv`: weak bisimilarity is an equivalence relation.

-/

@[expose] public section

namespace Cslib.LTS

variable {State₁ State₂ Label : Type*} {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label}

section Bisimulation

/-- A relation is a bisimulation if, whenever it relates two states,
the transitions originating from these states mimic each other and the reached
derivatives are themselves related. -/
def IsBisimulation (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label)
    (r : State₁ → State₂ → Prop) : Prop :=
  ∀ ⦃s₁ s₂⦄, r s₁ s₂ → ∀ μ, (
    (∀ s₁', lts₁.Tr s₁ μ s₁' → ∃ s₂', lts₂.Tr s₂ μ s₂' ∧ r s₁' s₂')
    ∧
    (∀ s₂', lts₂.Tr s₂ μ s₂' → ∃ s₁', lts₁.Tr s₁ μ s₁' ∧ r s₁' s₂')
  )

/-- Helper for following a transition by the first state in a pair of a `Bisimulation`. -/
theorem IsBisimulation.follow_fst
    (hb : IsBisimulation lts₁ lts₂ r) (hr : r s₁ s₂) (htr : lts₁.Tr s₁ μ s₁') :
    ∃ s₂', lts₂.Tr s₂ μ s₂' ∧ r s₁' s₂' :=
  (hb hr μ).1 _ htr

/-- Helper for following a transition by the second state in a pair of a `Bisimulation`. -/
theorem IsBisimulation.follow_snd
    (hb : IsBisimulation lts₁ lts₂ r) (hr : r s₁ s₂) (htr : lts₂.Tr s₂ μ s₂') :
    ∃ s₁', lts₁.Tr s₁ μ s₁' ∧ r s₁' s₂' :=
  (hb hr μ).2 _ htr

/-! ## Relation to simulation -/

/-- Any bisimulation is also a simulation. -/
theorem IsBisimulation.isSimulation : IsBisimulation lts₁ lts₂ r → IsSimulation lts₁ lts₂ r := by
  grind [IsBisimulation, IsSimulation]

/-- A relation is a bisimulation iff both it and its inverse are simulations. -/
theorem IsBisimulation.isSimulation_iff :
    IsBisimulation lts₁ lts₂ r ↔ (IsSimulation lts₁ lts₂ r ∧ IsSimulation lts₂ lts₁ (flip r)) := by
  have _ (s₁ s₂) : r s₁ s₂ → flip r s₂ s₁ := id
  grind [IsBisimulation, IsSimulation, flip]

/-- A homogeneous bisimulation is a bisimulation where the underlying LTSs are the same. -/
abbrev IsHomBisimulation (lts : LTS State Label) := IsBisimulation lts lts

/-- Two states are bisimilar if they are related by some bisimulation. -/
@[scoped grind =]
def Bisimilarity (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label) : State₁ → State₂ → Prop :=
  fun s₁ s₂ => ∃ r : State₁ → State₂ → Prop, r s₁ s₂ ∧ IsBisimulation lts₁ lts₂ r

/--
Notation for bisimilarity.

Differently from standard pen-and-paper presentations, we require the LTSs to be mentioned
explicitly.
-/
scoped notation s:max " ~[" lts₁ "," lts₂ "] " s':max => Bisimilarity lts₁ lts₂ s s'

/-- Homogeneous bisimilarity is bisimilarity where the underlying LTSs are the same. -/
abbrev HomBisimilarity (lts : LTS State Label) := Bisimilarity lts lts

/-- Notation for homogeneous bisimilarity. -/
scoped notation s:max " ~[" lts "] " s':max => HomBisimilarity lts s s'

/-- Helper for following a transition by the first state in a pair of a `Bisimilarity`. -/
theorem Bisimilarity.follow_fst (hr : s₁ ~[lts₁,lts₂] s₂) (htr : lts₁.Tr s₁ μ s₁') :
    ∃ s₂', lts₂.Tr s₂ μ s₂' ∧ s₁' ~[lts₁,lts₂ ] s₂' := by grind [IsBisimulation]

/-- Helper for following a transition by the first state in a pair of a `Bisimilarity`. -/
theorem Bisimilarity.follow_snd (hr : s₁ ~[lts₁,lts₂] s₂) (htr : lts₂.Tr s₂ μ s₂') :
    ∃ s₁', lts₁.Tr s₁ μ s₁' ∧ s₁' ~[lts₁,lts₂] s₂' := by grind [IsBisimulation]

/-- Homogeneous bisimilarity is reflexive. -/
@[scoped grind ., refl]
theorem HomBisimilarity.refl (s : State) : s ~[lts] s := by
  exists Eq
  grind [IsBisimulation]

/-- The inverse of a bisimulation is a bisimulation. -/
@[scoped grind →]
theorem IsBisimulation.inv (h : IsBisimulation lts₁ lts₂ r) :
  IsBisimulation lts₂ lts₁ (flip r) := by grind [IsBisimulation, flip]

open scoped IsBisimulation in
/-- Bisimilarity is symmetric. -/
@[scoped grind →, symm]
theorem Bisimilarity.symm {lts₁ lts₂ : LTS State Label} {s₁ s₂ : State}
    (h : s₁ ~[lts₁,lts₂] s₂) : s₂ ~[lts₂,lts₁] s₁ := by
  grind [flip]

/-- The composition of two bisimulations is a bisimulation. -/
@[scoped grind .]
theorem IsBisimulation.comp
    (h1 : IsBisimulation lts₁ lts₂ r1) (h2 : IsBisimulation lts₂ lts₃ r2) :
  IsBisimulation lts₁ lts₃ (Relation.Comp r1 r2) := by grind [IsBisimulation, Relation.Comp]

/-- Bisimilarity is transitive. -/
@[scoped grind →]
theorem Bisimilarity.trans
    (h1 : s₁ ~[lts₁,lts₂] s₂) (h2 : s₂ ~[lts₂,lts₃] s₃) :
  s₁ ~[lts₁,lts₃] s₃ := by
  obtain ⟨r1, _, _⟩ := h1
  obtain ⟨r2, _, _⟩ := h2
  exists Relation.Comp r1 r2
  grind [IsBisimulation, Relation.Comp]

/-- Homogeneous bisimilarity is an equivalence relation. -/
theorem HomBisimilarity.eqv :
  Equivalence (HomBisimilarity lts) := {
    refl := HomBisimilarity.refl
    symm := Bisimilarity.symm
    trans := Bisimilarity.trans
  }

instance : IsEquiv State (HomBisimilarity lts) where
  refl := HomBisimilarity.refl
  symm _ _ := Bisimilarity.symm
  trans _ _ _ := Bisimilarity.trans

/-- Bisimulation implies simulation equivalence. -/
theorem IsBisimulation.simulationEquiv (h : IsBisimulation lts₁ lts₂ r) (hrel : r s₁ s₂) :
    s₁ ≤≥[lts₁,lts₂] s₂ := ⟨⟨r, hrel, h.isSimulation⟩, flip r, hrel, h.inv.isSimulation⟩

/-- The union of two bisimulations is a bisimulation. -/
@[scoped grind .]
theorem IsBisimulation.sup (hrb : IsBisimulation lts₁ lts₂ r) (hsb : IsBisimulation lts₁ lts₂ s) :
    IsBisimulation lts₁ lts₂ (r ⊔ s) := by
  rw [IsBisimulation.isSimulation_iff] at hrb hsb ⊢
  rw [show flip (r ⊔ s) = flip r ⊔ flip s by ext; rfl]
  exact ⟨hrb.1.sup hsb.1, hrb.2.sup hsb.2⟩

/-- Bisimilarity is a bisimulation. -/
@[scoped grind .]
theorem Bisimilarity.isBisimulation (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label) :
  IsBisimulation lts₁ lts₂ (Bisimilarity lts₁ lts₂) := by grind [IsBisimulation]

/-- Bisimilarity is the largest bisimulation. -/
@[scoped grind →]
theorem IsBisimulation.le_bisimilarity (h : IsBisimulation lts₁ lts₂ r) :
    r ≤ (Bisimilarity lts₁ lts₂) := by
  intro s₁ s₂ hr
  exists r

/-- The union of bisimilarity with any bisimulation is bisimilarity. -/
@[scoped grind =, simp]
theorem Bisimilarity.gfp (r : State₁ → State₂ → Prop) (h : IsBisimulation lts₁ lts₂ r) :
    (Bisimilarity lts₁ lts₂) ⊔ r = Bisimilarity lts₁ lts₂ := sup_eq_left.mpr h.le_bisimilarity

/-- `calc` support for bisimilarity. -/
instance : Trans (Bisimilarity lts₁ lts₂) (Bisimilarity lts₂ lts₃) (Bisimilarity lts₁ lts₃) where
  trans := Bisimilarity.trans

section Order

/-! ## Order properties -/

instance : Max {r // IsBisimulation lts₁ lts₂ r} where
  max r s := ⟨r.1 ⊔ s.1, IsBisimulation.sup r.2 s.2⟩

@[simp] lemma coe_sup (r s : {r // IsBisimulation lts₁ lts₂ r}) :
    (↑(r ⊔ s) : State₁ → State₂ → Prop) = (r : State₁ → State₂ → Prop) ⊔ s := rfl

/-- Bisimulations equipped with union form a join-semilattice. -/
instance : SemilatticeSup {r // IsBisimulation lts₁ lts₂ r} where
  sup r s := r ⊔ s
  le_sup_left r s := by simp [←Subtype.coe_le_coe]
  le_sup_right r s := by simp [←Subtype.coe_le_coe]
  sup_le r s t := by simp [←Subtype.coe_le_coe]; tauto

/-- The empty (heterogeneous) relation is a bisimulation. -/
@[scoped grind .]
theorem IsBisimulation.bot : IsBisimulation lts₁ lts₂ Relation.emptyHRelation := by
  intro s₁ s₂ hr
  cases hr

instance : Bot {r // IsBisimulation lts₁ lts₂ r} :=
  ⟨Relation.emptyHRelation, IsBisimulation.bot⟩

instance : Top {r // IsBisimulation lts₁ lts₂ r} :=
  ⟨Bisimilarity lts₁ lts₂, Bisimilarity.isBisimulation ..⟩

/-- In the inclusion order on bisimulations:

- The empty relation is the bottom element.
- Bisimilarity is the top element.
-/
instance : BoundedOrder {r // IsBisimulation lts₁ lts₂ r} where
  top := ⊤
  bot := ⊥
  le_top r := r.property.le_bisimilarity
  bot_le r := by simp [Bot.bot, LE.le]

end Order

/-! ## Bisimulation up-to -/

/-- Lifts a relation `r` to homogeneous bisimilarities on its types. -/
def UpToHomBisimilarity (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label)
    (r : State₁ → State₂ → Prop) : State₁ → State₂ → Prop :=
  Relation.Comp (HomBisimilarity lts₁) (Relation.Comp r (HomBisimilarity lts₂))

/-- A relation `r` is a bisimulation up to homogeneous bisimilarity if, whenever it relates two
states in an lts, the transitions originating from these states mimic each other and the reached
derivatives are themselves related by `r` up to bisimilarity. -/
def IsBisimulationUpTo (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label)
    (r : State₁ → State₂ → Prop) : Prop :=
  ∀ ⦃s₁ s₂⦄, r s₁ s₂ → ∀ μ, (
    (∀ s₁', lts₁.Tr s₁ μ s₁' → ∃ s₂', lts₂.Tr s₂ μ s₂' ∧
      (UpToHomBisimilarity lts₁ lts₂ r) s₁' s₂')
    ∧
    (∀ s₂', lts₂.Tr s₂ μ s₂' → ∃ s₁', lts₁.Tr s₁ μ s₁' ∧
      (UpToHomBisimilarity lts₁ lts₂ r) s₁' s₂')
  )

/-- Any bisimulation up to bisimilarity is a bisimulation. -/
@[scoped grind →]
theorem IsBisimulationUpTo.isBisimulation (h : IsBisimulationUpTo lts₁ lts₂ r) :
    IsBisimulation lts₁ lts₂ (UpToHomBisimilarity lts₁ lts₂ r) := by
  intro s₁ s₂ hr μ
  rcases hr with ⟨s₁b, hr1b, s₂b, hrb, hr2b⟩
  constructor
  case left =>
    intro s₁' htr1
    obtain ⟨s₁b', hs₁b'tr, hs₁b'r⟩ := hr1b.follow_fst htr1
    obtain ⟨s₂b', hs₂b'tr, hs₂b'r⟩ := (h hrb μ).1 s₁b' hs₁b'tr
    obtain ⟨s₂', hs₂btr, hs₂br⟩ := hr2b.follow_fst hs₂b'tr
    use s₂', hs₂btr
    obtain ⟨smid1, hsmidb, smid2, hsmidr, hsmidrb⟩ := hs₂b'r
    use smid1, hs₁b'r.trans hsmidb, smid2, hsmidr
    exact hsmidrb.trans hs₂br
  case right =>
    intro s₂' htr2
    obtain ⟨s₂b', hs₂b'tr, hs₂b'r⟩ := hr2b.follow_snd htr2
    obtain ⟨s₁b', hs₁b'tr, hs₁b'r⟩ := (h hrb μ).2 s₂b' hs₂b'tr
    obtain ⟨s₁', hs₁btr, hs₁br⟩ := hr1b.follow_snd hs₁b'tr
    use s₁', hs₁btr
    obtain ⟨smid1, hsmidb, smid2, hsmidr, hsmidrb⟩ := hs₁b'r
    use smid1, hs₁br.trans hsmidb, smid2, hsmidr
    exact hsmidrb.trans hs₂b'r

/-- If two states are related by a bisimulation, they can mimic each other's multi-step
transitions. -/
theorem IsBisimulation.bisim_trace (hb : IsBisimulation lts₁ lts₂ r) (hr : r s₁ s₂) :
    ∀ μs s₁', lts₁.MTr s₁ μs s₁' → ∃ s₂', lts₂.MTr s₂ μs s₂' ∧ r s₁' s₂' :=
  hb.isSimulation.sim_trace hr

/-! ## Relation to trace equivalence -/

/-- Any bisimulation implies trace equivalence. -/
@[scoped grind =>]
theorem IsBisimulation.traceEq (hb : IsBisimulation lts₁ lts₂ r) (hr : r s₁ s₂) :
    s₁ ~tr[lts₁,lts₂] s₂ := (hb.simulationEquiv hr).traceEq

/-- Bisimilarity is included in trace equivalence. -/
@[scoped grind .]
theorem Bisimilarity.le_traceEq : Bisimilarity lts₁ lts₂ ≤ TraceEq lts₁ lts₂ := by
  intro s₁ s₂ h
  obtain ⟨r, hr, hb⟩ := h
  apply hb.traceEq hr

/- One of the standard motivating examples for bisimulation: `1` and `5` are trace equivalent, but
not bisimilar. -/
private inductive BisimMotTr : ℕ → Char → ℕ → Prop where
-- First process, `1`
| one2two : BisimMotTr 1 'a' 2
| two2three : BisimMotTr 2 'b' 3
| two2four : BisimMotTr 2 'c' 4
-- Second process, `5`
| five2six : BisimMotTr 5 'a' 6
| six2seven : BisimMotTr 6 'b' 7
| five2eight : BisimMotTr 5 'a' 8
| eight2nine : BisimMotTr 8 'c' 9

/-- In general, trace equivalence is not a bisimulation (extra conditions are needed, see for
example `Bisimulation.deterministic_trace_eq_is_bisim`). -/
theorem IsBisimulation.traceEq_not_bisim :
    ∃ (State : Type) (Label : Type) (lts : LTS State Label),
      ¬(IsHomBisimulation lts (HomTraceEq lts)) := by
  let lts := LTS.mk BisimMotTr
  exists ℕ, Char, lts
  intro h
  have htreq : (1 ~tr[lts] 5) := by
    have htraces₁ : lts.traces 1 = {[], ['a'], ['a', 'b'], ['a', 'c']} := by
      ext μs
      constructor
      case mp =>
        rintro ⟨_, (_ | ⟨⟨_⟩, (_ | ⟨(_ | _), (_ | ⟨⟨_⟩, _⟩)⟩)⟩)⟩
        all_goals simp
      case mpr =>
        rintro (rfl | rfl | rfl | rfl)
        · exact ⟨1, .refl⟩
        · exact ⟨2, MTr.single lts .one2two⟩
        · exact ⟨3, MTr.stepL .one2two <| MTr.single lts .two2three⟩
        · exact ⟨4, MTr.stepL .one2two <| MTr.single lts .two2four⟩
    have htraces₅ : lts.traces 5 = {[], ['a'], ['a', 'b'], ['a', 'c']} := by
      ext μs
      constructor
      case mp =>
        rintro ⟨_, (_ | ⟨(_ | _), (_ | ⟨⟨_⟩, (_ | ⟨⟨_⟩, _⟩)⟩)⟩)⟩
        all_goals simp
      case mpr =>
        rintro (rfl | rfl | rfl | rfl)
        · exact ⟨5, .refl⟩
        · exact ⟨6, MTr.single lts .five2six⟩
        · exact ⟨7, MTr.stepL .five2six <| MTr.single lts .six2seven⟩
        · exact ⟨9, MTr.stepL .five2eight <| MTr.single lts .eight2nine⟩
    exact htraces₁.trans htraces₅.symm
  obtain ⟨h1, h2⟩ := h htreq 'a'
  obtain ⟨s₂', htr5, cih⟩ := h1 2 (by constructor)
  have htraces₂ : {['b'], ['c']} ⊆ lts.traces 2 := by
    intro μs h
    rcases h with (rfl | rfl)
    · refine ⟨3, MTr.single lts .two2three⟩
    · refine ⟨4, MTr.single lts .two2four⟩
  cases htr5
  case five2six =>
    suffices ['c'] ∉ lts.traces 6 by grind [TraceEq]
    rintro ⟨_, (_ | h)⟩
    cases h
  case five2eight =>
    suffices ['b'] ∉ lts.traces 8 by grind [TraceEq]
    rintro ⟨_, (_ | h)⟩
    cases h

/-- In general, bisimilarity and trace equivalence are distinct. -/
theorem Bisimilarity.bisimilarity_neq_traceEq :
    ∃ (State : Type) (Label : Type) (lts : LTS State Label),
      HomBisimilarity lts ≠ HomTraceEq lts := by
  obtain ⟨State, Label, lts, h⟩ := IsBisimulation.traceEq_not_bisim
  use State, Label, lts
  grind [Bisimilarity.isBisimulation lts lts]

/-- In any deterministic LTS, trace equivalence is a bisimulation. -/
theorem IsBisimulation.deterministic_traceEq_isBisimulation
    {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label}
    [lts₁.Deterministic] [lts₂.Deterministic] :
    (IsBisimulation lts₁ lts₂ (TraceEq lts₁ lts₂)) := by
  rw [IsBisimulation.isSimulation_iff, TraceEq.flip_eq]
  exact ⟨TraceEq.deterministic_isSimulation, TraceEq.deterministic_isSimulation⟩

/-- In deterministic LTSs, trace equivalence implies bisimilarity. -/
theorem Bisimilarity.deterministic_traceEq_bisim {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label}
    [lts₁.Deterministic] [lts₂.Deterministic] (h : s₁ ~tr[lts₁,lts₂] s₂) :
    (s₁ ~[lts₁,lts₂] s₂) := by
  use TraceEq lts₁ lts₂, h, IsBisimulation.deterministic_traceEq_isBisimulation

theorem deterministic_bisim_tfae {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label}
    [lts₁.Deterministic] [lts₂.Deterministic] (s₁ : State₁) (s₂ : State₂) :
    [s₁ ~[lts₁,lts₂] s₂, s₁ ~tr[lts₁,lts₂] s₂, s₁ ≤≥[lts₁,lts₂] s₂].TFAE := by
  tfae_have 2 ↔ 3 := traceEq_iff_simulationEquiv_of_deterministic s₁ s₂
  tfae_have 1 → 2 := Bisimilarity.le_traceEq s₁ s₂
  tfae_have 2 → 1 := Bisimilarity.deterministic_traceEq_bisim
  tfae_finish

/-- In deterministic LTSs, bisimilarity and trace equivalence coincide. -/
theorem Bisimilarity.deterministic_bisim_eq_traceEq
    {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label}
    [lts₁.Deterministic] [lts₂.Deterministic] : Bisimilarity lts₁ lts₂ = TraceEq lts₁ lts₂ := by
  ext s₁ s₂
  exact (deterministic_bisim_tfae s₁ s₂).out 0 1

/-- Homogeneous bisimilarity can also be characterized through symmetric simulations. -/
theorem HomBisimilarity.symm_simulation :
  HomBisimilarity lts =
    fun s₁ s₂ => ∃ r, r s₁ s₂ ∧ Std.Symm r ∧ IsHomSimulation lts r := by
  ext s₁ s₂
  constructor
  · intro h
    use lts.HomBisimilarity, h
    exact ⟨⟨fun _ _ => Bisimilarity.symm⟩, (Bisimilarity.isBisimulation lts lts).isSimulation⟩
  · intro ⟨r, hrel, ⟨hsymm⟩, hsim⟩
    use r, hrel
    have : r = flip r := by ext; rw [flip]; grind
    simpa [IsBisimulation.isSimulation_iff, ←this]

end Bisimulation

section WeakBisimulation

/-! ## Weak bisimulation and weak bisimilarity -/

/-- A weak bisimulation is similar to a `Bisimulation`, but allows for the related processes to do
internal work. Technically, this is defined as a `Bisimulation` on the saturation of the LTSs. -/
def IsWeakBisimulation [HasTau Label] (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label)
    (r : State₁ → State₂ → Prop) :=
  IsBisimulation (lts₁.saturate) (lts₂.saturate) r

/-- A homogeneous bisimulation is a bisimulation where the underlying LTSs are the same. -/
abbrev IsHomWeakBisimulation [HasTau Label] (lts : LTS State Label) := IsWeakBisimulation lts lts

/-- Two states are weakly bisimilar if they are related by some weak bisimulation. -/
def WeakBisimilarity [HasTau Label] (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label) :
    State₁ → State₂ → Prop :=
  fun s₁ s₂ =>
    ∃ r : State₁ → State₂ → Prop, r s₁ s₂ ∧ IsWeakBisimulation lts₁ lts₂ r

/-- Notation for weak bisimilarity. -/
scoped notation s:max " ≈[" lts₁ "," lts₂ "] " s':max => WeakBisimilarity lts₁ lts₂ s s'

/-- Homogeneous bisimilarity is bisimilarity where the underlying LTSs are the same. -/
abbrev HomWeakBisimilarity [HasTau Label] (lts : LTS State Label) := WeakBisimilarity lts lts

/-- Notation for homogeneous bisimilarity. -/
scoped notation s:max " ≈[" lts "] " s':max => HomWeakBisimilarity lts s s'

/-- An `SWBisimulation` is a more convenient definition of weak bisimulation, because the challenge
is a single transition. We prove later that this technique is sound, following a strategy inspired
by [Sangiorgi2011]. -/
def IsSWBisimulation [HasTau Label] (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label)
    (r : State₁ → State₂ → Prop) : Prop :=
  ∀ ⦃s₁ s₂⦄, r s₁ s₂ → ∀ μ, (
    (∀ s₁', lts₁.Tr s₁ μ s₁' → ∃ s₂', lts₂.STr s₂ μ s₂' ∧ r s₁' s₂')
    ∧
    (∀ s₂', lts₂.Tr s₂ μ s₂' → ∃ s₁', lts₁.STr s₁ μ s₁' ∧ r s₁' s₂')
  )

lemma IsSWBisimulation.isSimulation [HasTau Label] (h : IsSWBisimulation lts₁ lts₂ r) :
    IsSimulation lts₁ lts₂.saturate r := by
  intro s₁ s₂ hr μ
  exact (h hr μ).1

lemma IsSWBisimulation.isSimulation_flip [HasTau Label] (h : IsSWBisimulation lts₁ lts₂ r) :
    IsSimulation lts₂ lts₁.saturate (flip r) := by
  intro s₂ s₁ hr μ
  exact (h hr μ).2

lemma IsSWBisimulation.iff_isSimulation [HasTau Label] :
    IsSWBisimulation lts₁ lts₂ r ↔
      IsSimulation lts₁ lts₂.saturate r ∧ IsSimulation lts₂ lts₁.saturate (flip r) := by
  refine ⟨fun h => ⟨h.isSimulation, h.isSimulation_flip⟩, ?_⟩
  intro ⟨h, hflip⟩ s₁ s₂ hr μ
  exact ⟨h s₁ s₂ hr μ, hflip s₂ s₁ hr μ⟩

/-- We can now prove that any relation is a `WeakBisimulation` iff it is an `SWBisimulation`.
This formalises lemma 4.2.10 in [Sangiorgi2011]. -/
theorem isWeakBisimulation_iff_isSWBisimulation
    [HasTau Label] {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label} :
    IsWeakBisimulation lts₁ lts₂ r ↔ IsSWBisimulation lts₁ lts₂ r := by
  apply Iff.intro
  case mp =>
    intro h
    rw [IsSWBisimulation.iff_isSimulation]
    exact ⟨h.isSimulation.mono lts₁.tr_le_tr_saturate le_rfl,
      h.inv.isSimulation.mono lts₂.tr_le_tr_saturate le_rfl⟩
  case mpr =>
    intro h
    rw [IsWeakBisimulation, IsBisimulation.isSimulation_iff]
    exact ⟨h.isSimulation.isSimulation_saturate_left,
      h.isSimulation_flip.isSimulation_saturate_left⟩

theorem IsWeakBisimulation.isSwBisimulation
    [HasTau Label] {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label} {r : State₁ → State₂ → Prop}
    (h : IsWeakBisimulation lts₁ lts₂ r) :
  IsSWBisimulation lts₁ lts₂ r := isWeakBisimulation_iff_isSWBisimulation.1 h

theorem IsSWBisimulation.isWeakBisimulation
    [HasTau Label] {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label} {r : State₁ → State₂ → Prop}
    (h : IsSWBisimulation lts₁ lts₂ r) :
  IsWeakBisimulation lts₁ lts₂ r := isWeakBisimulation_iff_isSWBisimulation.2 h

/-- Weak bisimilarity can also be characterized through sw-bisimulations. -/
@[scoped grind =]
theorem WeakBisimilarity.weakBisim_eq_swBisim [HasTau Label]
    (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label) :
    WeakBisimilarity lts₁ lts₂ =
      fun s₁ s₂ => ∃ r : State₁ → State₂ → Prop, r s₁ s₂ ∧ IsSWBisimulation lts₁ lts₂ r := by
  grind [WeakBisimilarity, isWeakBisimulation_iff_isSWBisimulation.1,
    isWeakBisimulation_iff_isSWBisimulation.2]

/-- Homogeneous weak bisimilarity is reflexive. -/
theorem HomWeakBisimilarity.refl [HasTau Label] {lts : LTS State Label} (s : State) :
    s ≈[lts] s := by
  simp only [HomWeakBisimilarity]
  rw [WeakBisimilarity.weakBisim_eq_swBisim lts lts]
  exists Eq
  grind [IsSWBisimulation, STr.single]

/-- The inverse of a weak bisimulation is a weak bisimulation. -/
theorem IsWeakBisimulation.inv [HasTau Label]
    {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label}
    (r : State₁ → State₂ → Prop) (h : IsWeakBisimulation lts₁ lts₂ r) :
    IsWeakBisimulation lts₂ lts₁ (flip r) := by
  grind [IsWeakBisimulation.isSwBisimulation, IsSWBisimulation,
    flip, IsSWBisimulation.isWeakBisimulation]

/-- Weak bisimilarity is symmetric. -/
theorem WeakBisimilarity.symm [HasTau Label] {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label}
    (h : s₁ ≈[lts₁,lts₂] s₂) : s₂ ≈[lts₂,lts₁] s₁ := by
  obtain ⟨r, hr, hrh⟩ := h
  exists (flip r)
  grind [IsWeakBisimulation.inv, flip]

/-- The composition of two weak bisimulations is a weak bisimulation. -/
theorem IsWeakBisimulation.comp
    [HasTau Label] {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label} {lts₃ : LTS State₃ Label}
    (h1 : IsWeakBisimulation lts₁ lts₂ r1) (h2 : IsWeakBisimulation lts₂ lts₃ r2) :
    IsWeakBisimulation lts₁ lts₃ (Relation.Comp r1 r2) := by
  simp_all only [IsWeakBisimulation]
  exact h1.comp h2

/-- The composition of two sw-bisimulations is an sw-bisimulation. -/
theorem IsSWBisimulation.comp
    [HasTau Label] {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label} {lts₃ : LTS State₃ Label}
    (h1 : IsSWBisimulation lts₁ lts₂ r1) (h2 : IsSWBisimulation lts₂ lts₃ r2) :
    IsSWBisimulation lts₁ lts₃ (Relation.Comp r1 r2) := by
  simp_all only [isWeakBisimulation_iff_isSWBisimulation.symm]
  apply IsWeakBisimulation.comp h1 h2

/-- Weak bisimilarity is transitive. -/
theorem WeakBisimilarity.trans [HasTau Label]
    {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label} {lts₃ : LTS State₃ Label}
    (h1 : s₁ ≈[lts₁,lts₂] s₂) (h2 : s₂ ≈[lts₂,lts₃] s₃) : s₁ ≈[lts₁,lts₃] s₃ := by
  obtain ⟨r1, hr1, hr1b⟩ := h1
  obtain ⟨r2, hr2, hr2b⟩ := h2
  exists Relation.Comp r1 r2
  constructor
  case left =>
    exists s₂
  case right =>
    apply IsWeakBisimulation.comp hr1b hr2b

/-- Homogeneous weak bisimilarity is an equivalence relation. -/
theorem HomWeakBisimilarity.eqv [HasTau Label] {lts : LTS State Label} :
    Equivalence (HomWeakBisimilarity lts) where
  refl := HomWeakBisimilarity.refl
  symm := WeakBisimilarity.symm
  trans := WeakBisimilarity.trans

end WeakBisimulation

end Cslib.LTS

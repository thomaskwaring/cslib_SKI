/-
Copyright (c) 2026 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
module

public import Cslib.Logics.Propositional.NaturalDeduction.Lemmas
public import Mathlib.Order.Heyting.Regular
public import Mathlib.Data.Finset.Lattice.Fold
public import Cslib.ForMathlib.Order.Heyting.Hom

@[expose] public section

namespace Cslib.Logic.PL

variable {Atom : Type u} [DecidableEq Atom] {T : Theory Atom}

open Theory Derivation InferenceSystem Proposition

abbrev Valuation (Atom : Type*) (H : Type*) := Atom → H

/-- Extend a valuation to propositions using the Heyting algebra operations. -/
def Valuation.pInterpret {H : Type _} [GeneralizedHeytingAlgebra H] (v : Valuation Atom H) :
    Proposition Atom → H
  | atom x => v x
  | Proposition.and A B => (v.pInterpret A) ⊓ (v.pInterpret B)
  | Proposition.or A B => (v.pInterpret A) ⊔ (v.pInterpret B)
  | impl A B => (v.pInterpret A) ⇨ (v.pInterpret B)

variable {H : Type _} [iH : GeneralizedHeytingAlgebra H] (v : Valuation Atom H)

instance {H : Type _} [GeneralizedHeytingAlgebra H] :
    CoeFun (Valuation Atom H) (fun _ => Proposition Atom → H) where
  coe := Valuation.pInterpret

/-- Extend a valuation to contexts using conjunction. -/
def Valuation.ctxInterpret {H : Type _} [GeneralizedHeytingAlgebra H] (v : Valuation Atom H)
    (Γ : Ctx Atom) : H := Γ.inf (v.pInterpret)

@[inherit_doc]
scoped notation v "⟦" A "⟧" => Valuation.pInterpret v A

@[inherit_doc]
scoped notation v "⟦" Γ "⟧" => Valuation.ctxInterpret v Γ

omit [DecidableEq Atom] in
@[simp] lemma Valuation.pInterpret_atom (v : Valuation Atom H) (x : Atom) :
  v⟦atom x⟧ = v x := rfl

omit [DecidableEq Atom] in
@[simp] lemma Valuation.pInterpret_and (v : Valuation Atom H) (A B : Proposition Atom) :
  v⟦A ∧ B⟧ = v⟦A⟧ ⊓ v⟦B⟧ := rfl

omit [DecidableEq Atom] in
@[simp] lemma Valuation.pInterpret_or (v : Valuation Atom H) (A B : Proposition Atom) :
  v⟦A ∨ B⟧ = v⟦A⟧ ⊔ v⟦B⟧ := rfl

omit [DecidableEq Atom] in
@[simp] lemma Valuation.pInterpret_impl (v : Valuation Atom H) (A B : Proposition Atom) :
  v⟦A → B⟧ = v⟦A⟧ ⇨ v⟦B⟧ := rfl

open Valuation

variable {H : Type _} [iH : GeneralizedHeytingAlgebra H] (v : Valuation Atom H)

/-- A valuation models a proposition if its interpretation is the top element. -/
@[reducible]
def Valuation.PValid (A : Proposition Atom) : Prop := v⟦A⟧ = ⊤

/-- A valuation models a sequent if the interpretation of the context is ≤ the interpretation of
the conclusion. -/
@[reducible]
def Valuation.SValid (S : Sequent (Atom := Atom)) : Prop := v⟦S.1⟧ ≤ v⟦S.2⟧

/-- A valuation models a theory if it models every axiom. -/
@[reducible]
def Valuation.TValid (T : Theory Atom) : Prop := ∀ A ∈ T, v.PValid A

@[inherit_doc]
scoped notation v' " ⊨ " A => Valuation.PValid v' A

@[inherit_doc]
scoped notation v' " ⊨ " S => Valuation.SValid v' S

@[inherit_doc]
scoped notation v' " ⊨ " T => Valuation.TValid v' T

omit [DecidableEq Atom] in
theorem Valuation.MPL_valid : v ⊨ MPL := by grind

omit [DecidableEq Atom] in
theorem Valuation.IPL_valid_of_heytingAlgebra [Bot Atom] {H' : Type _} [HeytingAlgebra H']
    {v : Valuation Atom H'} : v ⊥ = ⊥ → v ⊨ IPL := by
  intro hv A hA
  rw [Set.mem_range] at hA
  replace ⟨A', hA⟩ := hA
  simp_rw [←hA, PValid, pInterpret, hv]
  exact bot_himp _

omit [DecidableEq Atom] in
theorem Valuation.CPL_valid_of_booleanAlgebra [Bot Atom] {H' : Type _} [BooleanAlgebra H']
    {v : Valuation Atom H'} :
    v ⊥ = ⊥ → v ⊨ CPL := by
  rintro hv A ⟨A', rfl⟩
  simp [PValid, pInterpret, hv]

variable {v : Valuation Atom H}

section Soundness

theorem Theory.Derivation.sound' {Γ : Ctx Atom} {B : Proposition Atom}
    (hT : v ⊨ T) (D : T.Derivation Γ B) : v⟦Γ⟧ ≤ v⟦B⟧ := by
  induction D with
  | ax hB => rw [hT _ hB]; exact le_top
  | ass hB => exact Finset.inf_le hB
  | conjI _ _ aih bih => exact le_inf aih bih
  | conjE₁ _ ih => exact ih.trans (inf_le_left ..)
  | conjE₂ _ ih => exact ih.trans (inf_le_right ..)
  | disjI₁ _ ih => exact ih.trans (le_sup_left ..)
  | disjI₂ _ ih => exact ih.trans (le_sup_right ..)
  | disjE _ _ _ ih aih bih =>
    refine le_trans ?_ (sup_le aih bih)
    simpa [Valuation.ctxInterpret, Finset.inf_insert, ←inf_sup_right]
  | implI Γ _ ih =>
    rw [Valuation.pInterpret, le_himp_iff, inf_comm]
    rwa [Valuation.ctxInterpret, Finset.inf_insert] at ih
  | implE  _ _ ih ih' => exact (le_inf ih ih').trans himp_inf_le

theorem Theory.Derivation.sound (hT : v ⊨ T) {S : Sequent (Atom := Atom)}
    (D : T⇓S) : v ⊨ S := D.sound' hT

theorem DerivableIn.sound (hT : v ⊨ T) {S : Sequent (Atom := Atom)} (h : DerivableIn T S) :
    v ⊨ S := h.some.sound hT

theorem DerivableIn.sound' (hT : v ⊨ T) {A : Proposition Atom} (h : DerivableIn T A) :
    v⟦A⟧ = ⊤ := by
  simpa [Valuation.ctxInterpret] using (DerivableIn.iff_derivableIn_empty.mp h).some.sound hT

theorem consistent_of_interpret_ne_top (h : ∃ A : Proposition Atom, v⟦A⟧ ≠ ⊤) (hT : v ⊨ T) :
    Consistent T := by
  replace ⟨A, h⟩ := h
  contrapose! h
  exact DerivableIn.sound' hT <| h A

theorem MPL_consistent [Inhabited Atom] : Consistent <| MPL (Atom := Atom) :=
  consistent_of_interpret_ne_top (v := fun _ => False) ⟨default, by simp⟩ (Valuation.MPL_valid _)

theorem IPL_consistent [Bot Atom] : Consistent <| IPL (Atom := Atom) :=
  consistent_of_interpret_ne_top (v := fun _ => False) ⟨default, by simp⟩
    (Valuation.IPL_valid_of_heytingAlgebra rfl)

theorem CPL_consistent [Bot Atom] : Consistent <| CPL (Atom := Atom) :=
  consistent_of_interpret_ne_top (v := fun _ => False) ⟨default, by simp⟩
    (Valuation.CPL_valid_of_booleanAlgebra rfl)

end Soundness

section Completeness

lemma nontrivial_of_consistent [Inhabited Atom] (h : Consistent T) :
    Nontrivial (Quotient T.propositionSetoid) where
  exists_pair_ne := by
    obtain ⟨A, hA⟩ : ∃ A : Proposition Atom, ¬ DerivableIn T A := by simpa [Consistent] using h
    use ⟦A⟧, ⟦⊤⟧
    intro hc
    rw [Quotient.eq, Theory.propositionSetoid] at hc
    simp_rw [←derivableIn_iff_equiv_top] at hc
    exact hA hc

instance propPO : PartialOrder (Quotient T.propositionSetoid) where
  le := Quotient.lift₂ (f := fun A B => DerivableIn T ({A} ⊢ B)) (by
    simp_rw [eq_iff_iff]
    intro A B A' B' hA hB
    trans DerivableIn T ({A'} ⊢ B)
    · exact equiv_iff_equiv_derivableIn_hypothesis.mp hA ∅ B
    · exact equiv_iff_equiv_derivableIn.mp hB {A'}
  )
  le_refl := Quotient.ind fun A => by
    simp_rw [Quotient.lift_mk]
    exact Theory.Equiv.refl A |>.mp
  le_trans := Quotient.ind₂ fun A B => Quotient.ind fun C => by
    simp_rw [Quotient.lift_mk]
    intro h h'
    exact DerivableIn.cut (Δ := ∅) h h'
  le_antisymm := Quotient.ind₂ fun A B => by
    simp_rw [Quotient.lift_mk, Quotient.eq]
    intro h h'
    exact equiv_iff.mpr ⟨h, h'⟩

@[simp]
lemma Theory.mk_le_mk (A B : Proposition Atom) :
    (⟦A⟧ : Quotient T.propositionSetoid) ≤ ⟦B⟧ ↔ DerivableIn T ({A} ⊢ B) := by simp [LE.le]

instance propLattice : Lattice (Quotient T.propositionSetoid) where
  sup := Quotient.lift₂ (f := fun (A : Proposition Atom) B => ⟦A ∨ B⟧) <| by
    simp only [Quotient.eq, Theory.propositionSetoid]
    exact fun _ _ _ _ => Theory.Equiv.or_or
  inf := Quotient.lift₂ (f := fun (A : Proposition Atom) B => ⟦A ∧ B⟧) <| by
    simp only [Quotient.eq, Theory.propositionSetoid]
    exact fun _ _ _ _ => Theory.Equiv.and_and
  le_sup_left := Quotient.ind₂ fun A B => by
    simp only [Quotient.lift_mk, T.mk_le_mk]
    exact ⟨disjI₁ (B := B) <| ass <| Finset.mem_singleton_self A⟩
  le_sup_right := Quotient.ind₂ fun A B => by
    simp only [Quotient.lift_mk, T.mk_le_mk]
    exact ⟨disjI₂ (A := A) <| ass <| Finset.mem_singleton_self B⟩
  sup_le := Quotient.ind₂ fun A B => Quotient.ind fun C => by
    simp only [Quotient.lift_mk, T.mk_le_mk]
    intro ⟨DA⟩ ⟨DB⟩
    refine ⟨(ass <| Finset.mem_singleton_self (A ∨ B)).disjE ?_ ?_⟩
    · exact DA.weak_ctx (by grind)
    · exact DB.weak_ctx (by grind)
  inf_le_left := Quotient.ind₂ fun A B => by
    simp only [Quotient.lift_mk, T.mk_le_mk]
    exact ⟨(ass <| Finset.mem_singleton_self (A ∧ B)).conjE₁⟩
  inf_le_right := Quotient.ind₂ fun A B => by
    simp only [Quotient.lift_mk, T.mk_le_mk]
    exact ⟨(ass <| Finset.mem_singleton_self (A ∧ B)).conjE₂⟩
  le_inf := Quotient.ind₂ fun A B => Quotient.ind fun C => by
    simp only [Quotient.lift_mk, T.mk_le_mk]
    intro ⟨DB⟩ ⟨DC⟩
    exact ⟨DB.conjI DC⟩

@[simp]
lemma Theory.mk_sup_mk (A B : Proposition Atom) :
    (⟦A⟧ : Quotient T.propositionSetoid) ⊔ ⟦B⟧ = ⟦A ∨ B⟧ := by simp [max, SemilatticeSup.sup]

@[simp]
lemma Theory.mk_inf_mk (A B : Proposition Atom) :
    (⟦A⟧ : Quotient T.propositionSetoid) ⊓ ⟦B⟧ = ⟦A ∧ B⟧ := by
  simp [min, SemilatticeInf.inf, Lattice.inf]

instance propGeneralizedHeyting [Inhabited Atom] :
    GeneralizedHeytingAlgebra (Quotient T.propositionSetoid) where
  top := ⟦⊤⟧
  le_top := Quotient.ind fun A => by
    simp only [T.mk_le_mk]
    exact ⟨derivationTop.weak_ctx <| Finset.empty_subset _⟩
  himp := Quotient.lift₂ (f := fun (A : Proposition Atom) B => ⟦A → B⟧) <| by
    simp only [Quotient.eq, Theory.propositionSetoid]
    exact fun _ _ _ _ => Theory.Equiv.impl_impl
  le_himp_iff := Quotient.ind₂ fun A B => Quotient.ind fun C => by
    simp only [Quotient.lift₂_mk, T.mk_le_mk, T.mk_inf_mk]
    constructor <;> intro ⟨D⟩
    · refine ⟨implE (A := B) ?_ ?_⟩
      · apply Theory.Derivation.cut (Γ := {A ∧ B}) (Δ := ∅) ?_ D
        exact (ass <| Finset.mem_singleton_self (A ∧ B)).conjE₁
      · exact (ass <| Finset.mem_singleton_self (A ∧ B)).conjE₂
    · refine ⟨implI _ ?_⟩
      refine Theory.Derivation.cut (Γ := {B, A}) (Δ := ∅) ?_ D |>.weak_ctx (by grind)
      apply conjI <;> exact ass (by grind)

lemma Theory.top [Inhabited Atom] :
  (⊤ : Quotient T.propositionSetoid) = ⟦⊤⟧ := rfl

@[simp]
lemma Theory.mk_himp_mk [Inhabited Atom] (A B : Proposition Atom) :
    (⟦A⟧ : Quotient T.propositionSetoid) ⇨ ⟦B⟧ = ⟦A → B⟧ := by simp [himp]

instance propBot [Bot Atom] : Bot (Quotient T.propositionSetoid) where
  bot := ⟦⊥⟧

lemma Theory.bot [Bot Atom] : (⊥ : Quotient T.propositionSetoid) = ⟦⊥⟧ := rfl

instance [Bot Atom] : Compl (Quotient T.propositionSetoid) where
  compl := Quotient.lift (f := fun (A : Proposition Atom) => ⟦¬ A⟧) <| by
    simp only [Theory.propositionSetoid, Quotient.eq]
    exact fun _ _ => Theory.Equiv.not

@[simp]
lemma Theory.compl_mk [Bot Atom] (A : Proposition Atom) :
  (⟦A⟧ : Quotient T.propositionSetoid)ᶜ = ⟦¬ A⟧ := by simp [compl]

@[reducible]
def propHeytingOfLE [Bot Atom] (h : IPL ≤ T) :
    HeytingAlgebra (Quotient T.propositionSetoid) where
  bot_le := Quotient.ind fun A => by
    simp only [T.bot, T.mk_le_mk]
    refine ⟨efqOfIPLHyp ?_ (Finset.mem_singleton_self ⊥) A⟩
    exact (nonempty_embedding_iff_le.mpr h).some
  himp_bot := Quotient.ind fun A => rfl

instance propHeyting [Bot Atom] [IsIntuitionistic T] :
    HeytingAlgebra (Quotient T.propositionSetoid) := propHeytingOfLE <| by
  apply le_of_subset
  grind

@[reducible]
def propBooleanOfLE [Bot Atom] (h : CPL ≤ T) : BooleanAlgebra (Quotient T.propositionSetoid) := by
  let iH : HeytingAlgebra (Quotient T.propositionSetoid) := propHeytingOfLE (ipl_le_cpl.trans h)
  refine BooleanAlgebra.ofRegular <| Quotient.ind fun A => ?_
  simp_rw [Heyting.IsRegular, T.compl_mk, T.mk_sup_mk, T.compl_mk, Quotient.eq]
  refine ⟨?_, ?_⟩
  · refine implE ?_ (ass <| Finset.mem_singleton_self _)
    refine Embedding.dneOfCPL ?_ _ |>.weak_ctx (by grind)
    exact (nonempty_embedding_iff_le.mpr h).some
  · refine implI _ <| implE (ass <| Finset.mem_insert_self _ _) ?_
    exact ass (by grind)

instance propBoolean [Bot Atom] [IsClassical T] : BooleanAlgebra (Quotient T.propositionSetoid) :=
  propBooleanOfLE <| by
    apply le_of_subset
    grind

def Theory.canonicalV (T : Theory Atom) : (Valuation Atom <| Quotient T.propositionSetoid) :=
  fun x => ⟦atom x⟧

theorem Theory.canonicalV_spec [Inhabited Atom] (A : Proposition Atom) :
    T.canonicalV.pInterpret A = ⟦A⟧ := by
  induction A with
  | atom _ => simp! [Theory.canonicalV]
  | and _ _ ihA ihB => simp! [min, SemilatticeInf.inf, Lattice.inf, ihA, ihB]
  | or _ _ ihA ihB => simp! [max, SemilatticeSup.sup, ihA, ihB]
  | impl _ _ ihA ihB => simp! [himp, ihA, ihB]

theorem Theory.lindenbaum_complete [Inhabited Atom] {A : Proposition Atom} :
    (T.canonicalV ⊨ A) ↔ DerivableIn T A := by
  simp_rw [Valuation.PValid, T.canonicalV_spec, T.top, Quotient.eq]
  exact derivableIn_iff_equiv_top A |>.symm

theorem Theory.tValid_canonicalV [Inhabited Atom] : T.canonicalV ⊨ T :=
  fun _ hA => T.lindenbaum_complete.mpr ⟨ax hA⟩

theorem Theory.complete [Inhabited Atom] {A : Proposition Atom} :
    DerivableIn T A ↔
    ∀ {H : Type u} [GeneralizedHeytingAlgebra H] {v : Valuation Atom H}, (v ⊨ T) → v ⊨ A := by
  constructor
  · intro hA H _ v hv
    exact DerivableIn.sound' hv hA
  · intro h
    exact T.lindenbaum_complete.mp <| h T.tValid_canonicalV

theorem MPL.complete [Inhabited Atom] {A : Proposition Atom} :
    DerivableIn (MPL (Atom := Atom)) A ↔
    ∀ {H : Type u} [GeneralizedHeytingAlgebra H] {v : Valuation Atom H}, v ⊨ A := by
  constructor
  · intro hA H _ v
    exact DerivableIn.sound' (Valuation.MPL_valid _) hA
  · intro h
    exact MPL.lindenbaum_complete.mp h

theorem IPL.complete [Bot Atom] {A : Proposition Atom} :
    DerivableIn (IPL (Atom := Atom)) A ↔
    ∀ {H : Type u} [HeytingAlgebra H] {v : Valuation Atom H}, v ⊥ = ⊥ → v ⊨ A := by
  constructor
  · intro hA H _ v hv
    exact DerivableIn.sound' (Valuation.IPL_valid_of_heytingAlgebra hv) hA
  · intro h
    refine IPL.lindenbaum_complete.mp <| h rfl

theorem CPL.complete [Bot Atom] {A : Proposition Atom} :
    DerivableIn (CPL (Atom := Atom)) A ↔
  ∀ {B : Type u} [BooleanAlgebra B] {v : Valuation Atom B}, v ⊥ = ⊥ → v ⊨ A := by
  constructor
  · intro hA H _ v hv
    exact DerivableIn.sound' (Valuation.CPL_valid_of_booleanAlgebra hv) hA
  · intro h
    refine CPL.lindenbaum_complete.mp <| h rfl

end Completeness

section Hom

variable {Atom Atom' : Type u} {T : Theory Atom} {T' : Theory Atom'} {H H' : Type*}
  [GeneralizedHeytingAlgebra H] [GeneralizedHeytingAlgebra H']

theorem GeneralizedHeytingHom.map_interpret (f : GeneralizedHeytingHom H H')
    (A : Proposition Atom) (v : Valuation Atom H) : f (v⟦A⟧) = (f ∘ v)⟦A⟧ := by
  induction A
  case atom _ => rfl
  all_goals simp_all [Valuation.pInterpret]

def Theory.Extension.toGeneralizedHeytingHom [DecidableEq Atom] [DecidableEq Atom']
    [Inhabited Atom] [Inhabited Atom'] (e : T.Extension T') :
    GeneralizedHeytingHom (Quotient T.propositionSetoid) (Quotient T'.propositionSetoid) where
  toFun := Quotient.map (· >>= e.f) <| fun A B => e.equiv_subst
  map_sup' := Quotient.ind₂ <| by simp
  map_inf' := Quotient.ind₂ <| by simp
  map_himp' := Quotient.ind₂ <| by simp

end Hom

end Cslib.Logic.PL

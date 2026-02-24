/-
Copyright (c) 2026 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Cslib.Foundations.Data.Tree.Maps
public import Mathlib.Tactic.TFAE

public section

namespace Cslib.PTree

open Relation

variable {S X : Type _} {s t u : PTree S X} {E : PTree S X → PTree S X → Prop} {p : List ℕ}
  {σ : X → PTree S X}

inductive RewritesAtWith (E : PTree S X → PTree S X → Prop) :
    List ℕ → (X → PTree S X) → PTree S X → PTree S X → Prop where
  | step_at_with {s t l r : PTree S X} (hlr : E l r) {p : List ℕ} (hp : s.IsPosi p)
      {σ : X → PTree S X} (hs : s[p] = (l >>= σ)) (ht : t = s[p := r >>= σ]) :
      RewritesAtWith E p σ s t

inductive RewritesAt (E : PTree S X → PTree S X → Prop) :
    List ℕ → PTree S X → PTree S X → Prop where
  | step_at {s t l r : PTree S X} (hlr : E l r) {p : List ℕ} (hp : s.IsPosi p) {σ : X → PTree S X}
    (hs : s[p] = (l >>= σ)) (ht : t = s[p := r >>= σ]) : RewritesAt E p s t

inductive Rewrites (E : PTree S X → PTree S X → Prop) :
    PTree S X → PTree S X → Prop where
  | step {s t l r : PTree S X} (hlr : E l r) {p : List ℕ} (hp : s.IsPosi p) {σ : X → PTree S X}
    (hs : s[p] = (l >>= σ)) (ht : t = s[p := r >>= σ]) : Rewrites E s t

attribute [scoped grind cases] RewritesAtWith RewritesAt Rewrites
attribute [scoped grind <=] RewritesAtWith.step_at_with RewritesAt.step_at Rewrites.step

@[grind =]
lemma RewritesAtWith.iff_exists : RewritesAtWith E p σ s t ↔ ∃ (l r : PTree S X), E l r ∧
    ∃ (_ : s.IsPosi p), s[p] = (l >>= σ) ∧ t = s[p := r >>= σ] := by grind

@[grind =]
lemma RewritesAt.iff_exists : RewritesAt E p s t ↔ ∃ (l r : PTree S X), E l r ∧
    ∃ (_ : s.IsPosi p) (σ : X → PTree S X), s[p] = (l >>= σ) ∧ t = s[p := r >>= σ] := by grind

@[grind =]
lemma Rewrites.iff_exists : Rewrites E s t ↔ ∃ (l r : PTree S X), E l r ∧ ∃ (p : List ℕ)
    (_ : s.IsPosi p) (σ : X → PTree S X), s[p] = (l >>= σ) ∧ t = s[p := r >>= σ] := by grind

@[grind =]
lemma rewritesAt_iff_exists_rewritesAtWith :
    RewritesAt E p s t ↔ ∃ σ, RewritesAtWith E p σ s t := by
  constructor
  · rw [RewritesAt.iff_exists]; intro ⟨_, _, _, _, σ, _⟩; use σ; grind
  · grind

lemma rewrites_iff_exists_rewritesAt :
    Rewrites E s t ↔ ∃ p, RewritesAt E p s t := by
  constructor
  · rw [Rewrites.iff_exists]; intro ⟨_, _, _, p, _⟩; use p; grind
  · grind

theorem Rewrites.tfae :
    [Rewrites E s t, ∃ p, RewritesAt E p s t, ∃ p σ, RewritesAtWith E p σ s t,
    ∃ (l r : PTree S X), E l r ∧ ∃ (p : List ℕ)
    (_ : s.IsPosi p) (σ : X → PTree S X), s[p] = (l >>= σ) ∧ t = s[p := r >>= σ]].TFAE := by
  tfae_have 1 ↔ 2 := rewrites_iff_exists_rewritesAt
  tfae_have 1 ↔ 4 := Rewrites.iff_exists
  tfae_have 2 → 3 := by
    intro ⟨p, h⟩; use p; exact rewritesAt_iff_exists_rewritesAtWith.mp h
  tfae_have 3 → 2 := by
    intro ⟨p, h⟩; use p; exact rewritesAt_iff_exists_rewritesAtWith.mpr h
  tfae_finish

def RewriteEquiv (E : PTree S X → PTree S X → Prop) := EqvGen (Rewrites E)

lemma RewriteEquiv.equivalence {E : PTree S X → PTree S X → Prop} :
  Equivalence (RewriteEquiv E) := by exact EqvGen.is_equivalence _

def MapVarClosed (E : PTree S X → PTree S X → Prop) : Prop :=
  ∀ (σ : X → PTree S X) (s t : PTree S X), E s t → E (s >>= σ) (t >>= σ)

def NodeClosed (E : PTree S X → PTree S X → Prop) : Prop :=
  ∀ (f : S) (tss : List (PTree S X × PTree S X)),
    (∀ ts ∈ tss, E ts.1 ts.2) → E (node f <| tss.map Prod.fst) (node f <| tss.map Prod.snd)

def NodeClosedSingle (E : PTree S X → PTree S X → Prop) : Prop :=
  ∀ (f : S) (ts : List (PTree S X)) (t' : PTree S X) (i : Fin ts.length),
    E ts[i] t' → E (node f ts) (node f <| ts.set i t')

def SubstClosed (E : PTree S X → PTree S X → Prop) : Prop :=
  ∀ (s s' t : PTree S X) (p : List ℕ) (_ : t.IsPosi p), E s s' → E (t[p:=s]) (t[p:=s'])

variable {E : PTree S X → PTree S X → Prop}

lemma Rewrites.self (l r : PTree S X) (hlr : E l r) (p : List ℕ) (hp : s.IsPosi p)
    (σ : X → PTree S X) (hs : s[p] = l >>= σ) : Rewrites E s (s[p := r >>= σ]) := by
  grind

lemma Rewrites.mapVarClosed : MapVarClosed (Rewrites E) := by
  intro σ s t h
  rw [Rewrites.iff_exists] at h ⊢
  obtain ⟨l, r, hlr, q, hq, ρ, hs, rfl⟩ := h
  use l, r, hlr, q, hq.bind, fun x => (ρ x) >>= σ
  constructor
  · simp [bind_getElem_comm hq, hs]
  · rw [bind_subst hq]
    congr 1
    simp

lemma Rewrites.substClosed : SubstClosed (Rewrites E) := by
  intro s s' t p hp h
  rw [Rewrites.iff_exists] at h
  obtain ⟨l, r, hlr, q, hq, σ, hs, rfl⟩ := h
  rw [← subst_append_subst (hp := by grind) hq]
  refine Rewrites.self l r hlr _ ?_ σ ?_
  all_goals grind

lemma Rewrites.minimal {E E' : PTree S X → PTree S X → Prop} (hrel : E ≤ E')
    (hmap : MapVarClosed E') (hsubst : SubstClosed E') : Rewrites E ≤ E' := by
  intro s t
  rw [Rewrites.iff_exists]
  rintro ⟨l, r, hlr, p, hp, σ, hs, rfl⟩
  suffices E' (s[p:=l >>= σ]) (s[p:=r >>= σ]) by
    rw (occs := [1]) [← subst_refl hp, hs]
    assumption
  apply hsubst
  · exact hp
  · apply hmap
    exact hrel _ _ hlr

lemma substClosed_iff_covariantClass :
    SubstClosed E ↔ CovariantClass (HasContext.Context (PTree S X)) (PTree S X) (·[·]) E := by
  constructor
  · intro hE
    constructor
    intro c s t h
    simpa using hE s t c.tree c.p c.isPosi_p h
  · intro ⟨hE⟩ s s' t p hp h
    have := hE ⟨t, p, hp⟩ h
    simpa

lemma nodeClosedSingle_iff_set_set : NodeClosedSingle E ↔
  ∀ (f : S) (ts : List (PTree S X)) (t t' : PTree S X) (i : Fin ts.length),
    E t t' → E (node f <| ts.set i t) (node f <| ts.set i t') := by
  constructor
  · intro hE f ts t t' i h
    have := hE f (ts.set i t) t' (i.cast List.length_set.symm)
    simp only [Fin.val_cast] at this
    apply List.set_set t ▸ this
    simpa
  · intro hE f ts t' i h
    simpa using hE f ts (ts[i]) t' i h

lemma NodeClosedSingle.set_set : NodeClosedSingle E →
  ∀ (f : S) (ts : List (PTree S X)) (t t' : PTree S X) (i : Fin ts.length),
    E t t' → E (node f <| ts.set i t) (node f <| ts.set i t') := nodeClosedSingle_iff_set_set.mp

theorem nodeClosedSingle_iff_substClosed : NodeClosedSingle E ↔ SubstClosed E := by
  constructor <;> intro hE
  · intro s s' t p hp h
    induction p generalizing t with
    | nil => simpa
    | cons i p ih =>
      cases t
      case leaf =>
        cases p <;> grind
      case node f ts =>
        simp only [hp.idx_lt_length, subst_node_cons_of_lt_length]
        have iprop := hp.idx_lt_length
        have := hE.set_set f ts (ts[i][p:=s]) (ts[i][p:=s']) ⟨i, iprop⟩
        exact this (ih _ hp.of_cons)
  · intro f ts t' i h
    simpa using hE ts[i] t' (node f ts) ([i]) (by simp) h

theorem nodeClosedSingle_of_nodeClosed_of_reflexive (hE_refl : Reflexive E) (hE : NodeClosed E) :
    NodeClosedSingle E := by
  intro f ts t' i h
  have := hE f (ts.zip (ts.set i t'))
  have hlen : (ts.set i t').length = ts.length := List.length_set
  simp only [List.length_set, Std.le_refl, List.map_fst_zip, List.map_snd_zip] at this
  apply this
  intro ss h
  obtain ⟨j, jprop, hj⟩ := List.mem_iff_getElem.mp h
  by_cases i = j
  all_goals grind [reflexive_iff_subrelation_eq.mp hE_refl]

private lemma List.forall_mem_pairs_of_forall_set_of_transitive {α : Type _}
    {r : List α → List α → Prop} {s : α → α → Prop} (hr : Transitive r) (hs : Reflexive s)
    (hr_nil : r [] ([]))
    (h : ∀ (xs : List α) (x' : α) (i : Fin xs.length), s xs[i] x' → r xs (xs.set i x')) :
    ∀ (xss : List (α × α)),
      (∀ xs ∈ xss, s xs.1 xs.2) → r (xss.map Prod.fst) (xss.map Prod.snd) := by
  intro xss hx
  induction xss generalizing r with
  | nil => simpa
  | cons xs xss ih =>
    refine hr (y := xs.snd :: (xss.map Prod.fst)) ?_ ?_
    · let i : Fin ((xs :: xss).map Prod.fst).length := ⟨0, by grind⟩
      have : xs.snd :: (xss.map Prod.fst) = (((xs :: xss).map Prod.fst).set i xs.snd) := by grind
      rw [this]
      apply h
      simpa [i] using hx xs
    · rw [List.map_cons]
      let r' : List α → List α → Prop := fun l l' => r (xs.snd :: l) (xs.snd :: l')
      change r' (xss.map Prod.fst) (xss.map Prod.snd)
      apply ih
      · intro l l' l''
        simp_rw [r']
        apply hr
      · simpa using h [xs.snd] xs.snd ⟨0, by grind⟩ (hs _)
      · intro l x' ⟨i, iprop⟩ hi
        simp_rw [r']
        have := h (xs.snd :: l) x' ⟨i + 1, by grind⟩ hi
        simpa using this
      · grind

theorem nodeClosed_iff_nodeClosedSingle_of_equivalence (hE_equiv : Equivalence E) :
    NodeClosed E ↔ NodeClosedSingle E := by
  refine ⟨nodeClosedSingle_of_nodeClosed_of_reflexive hE_equiv.refl, ?_⟩
  intro hE f tss ht
  apply List.forall_mem_pairs_of_forall_set_of_transitive
    (r := fun l l' => E (node f l) (node f l'))
    (s := E) (hs := hE_equiv.refl) (hr_nil := hE_equiv.refl (node f ([])))
  · intro xs ys zs
    exact hE_equiv.trans
  · grind [NodeClosedSingle]
  · assumption

theorem closures_tfae_of_equivalence (hE : Equivalence E) :
    [SubstClosed E, NodeClosed E, NodeClosedSingle E].TFAE := by
  tfae_have 3 ↔ 1 := nodeClosedSingle_iff_substClosed
  tfae_have 2 ↔ 3 := nodeClosed_iff_nodeClosedSingle_of_equivalence hE
  tfae_finish

theorem congruence_tfae :
    [Congruence (PTree S X) E, SubstClosed E ∧ Equivalence E, NodeClosed E ∧ Equivalence E,
      NodeClosedSingle E ∧ Equivalence E].TFAE := by
  rw [Congruence.iff_covariantClass_and_equivalence, ←substClosed_iff_covariantClass,
    List.tfae_cons_self]
  tfae_have 2 ↔ 3 := by simpa using nodeClosed_iff_nodeClosedSingle_of_equivalence
  tfae_have 3 ↔ 1 := by rw [and_congr_left_iff]; exact fun _ => nodeClosedSingle_iff_substClosed
  tfae_finish

theorem MapVarClosed.eqvGen (h : MapVarClosed E) : MapVarClosed (EqvGen E) := by
  intro σ s t h
  induction h <;> grind [EqvGen, MapVarClosed]

theorem RewriteEquiv.mapVarClosed : MapVarClosed (RewriteEquiv E) :=
  MapVarClosed.eqvGen Rewrites.mapVarClosed

theorem SubstClosed.eqvGen (h : SubstClosed E) : SubstClosed (EqvGen E) := by
  intro s s' t p hp h
  induction h <;> grind [EqvGen, SubstClosed]

theorem RewriteEquiv.nodeClosed : NodeClosed (RewriteEquiv E) := by
  rw [nodeClosed_iff_nodeClosedSingle_of_equivalence RewriteEquiv.equivalence,
    nodeClosedSingle_iff_substClosed]
  exact SubstClosed.eqvGen Rewrites.substClosed

private lemma EqvGen.minimal {α : Type*} {r r' : α → α → Prop} (hle : r ≤ r')
    (heqv : Equivalence r') : EqvGen r ≤ r' := by
  intro x y h
  induction h with
  | rel _ _ h => exact hle _ _ h
  | refl => exact heqv.refl _
  | symm _ _ _ ih => exact heqv.symm ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact heqv.trans ih₁ ih₂

theorem RewriteEquiv.minimal {E' : PTree S X → PTree S X → Prop} (hE : E ≤ E')
    (hE'_map : MapVarClosed E') (hE'_node : NodeClosed E') (hE'_eqv : Equivalence E') :
    RewriteEquiv E ≤ E' := by
  refine EqvGen.minimal ?_ hE'_eqv
  rw [nodeClosed_iff_nodeClosedSingle_of_equivalence hE'_eqv,
    nodeClosedSingle_iff_substClosed] at hE'_node
  apply Rewrites.minimal hE hE'_map hE'_node

lemma RewriteEquiv.single (h : E s t) : (RewriteEquiv E) s t := by
  apply EqvGen.rel
  apply Rewrites.step h IsPosi.nil' (σ := pure) <;> simp

lemma RewriteEquiv.refl (s : PTree S X) : (RewriteEquiv E) s s := EqvGen.refl _

lemma RewriteEquiv.symm (h : (RewriteEquiv E) s t) : (RewriteEquiv E) t s := EqvGen.symm _ _ h

lemma RewriteEquiv.trans (h : (RewriteEquiv E) s t) (h' : (RewriteEquiv E) t u) :
    (RewriteEquiv E) s u := EqvGen.trans _ _ _ h h'

lemma RewriteEquiv.bind (σ : X → PTree S X) (h : (RewriteEquiv E) s t) :
  (RewriteEquiv E) (s >>= σ) (t >>= σ) := RewriteEquiv.mapVarClosed _ _ _ h

lemma RewriteEquiv.node (f : S) {tss : List (PTree S X × PTree S X)}
    (h : ∀ ts ∈ tss, (RewriteEquiv E) ts.1 ts.2) :
    (RewriteEquiv E) (node f <| tss.map Prod.fst) (node f <| tss.map Prod.snd) :=
  RewriteEquiv.nodeClosed _ _ h

end Cslib.PTree

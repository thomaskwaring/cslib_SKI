/-
Copyright (c) 2026 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Cslib.Foundations.Data.Tree.Basic
public import Mathlib.Data.Fintype.OfMap

public section

namespace Cslib.PTree

variable {S S' X X' : Type _} {s t u : PTree S X} {p q : List ℕ}

def positionList (t : PTree S X) : List (List ℕ) :=
  match t with
  | leaf _ => [[]]
  | node _ ts => [] :: (List.finRange ts.length).flatMap
      (fun i => (ts[i]).positionList.map (i :: ·))
  termination_by t.size
  decreasing_by exact size_getElem_lt_size i.isLt

lemma cons_mem_positionList_node {f : S} {ts : List (PTree S X)} (i : ℕ) :
    (i :: p) ∈ (node f ts).positionList ↔
      (∃ (a : Fin ts.length), p ∈ ts[↑a].positionList ∧ ↑a = i) := by
  simp [positionList]

def ShapeEq (s t : PTree S X) : Prop := ∀ p, s.IsPosi p ↔ t.IsPosi p

lemma ShapeEq.mp (h : ShapeEq s t) (p : List ℕ) : s.IsPosi p → t.IsPosi p := (h p).mp

lemma ShapeEq.mpr (h : ShapeEq s t) (p : List ℕ) : t.IsPosi p → s.IsPosi p := (h p).mpr

@[grind .]
lemma ShapeEq.refl (s : PTree S X) : s.ShapeEq s := fun _ => Iff.rfl

lemma ShapeEq.node_length_eq {f : S} {ss ts : List (PTree S X)}
    (h : (node f ss).ShapeEq (node f ts)) : ss.length = ts.length := by
  have := h [ss.length]
  have := h [ts.length]
  grind

-- def test : PTree Unit Unit := node () ([leaf (), node () ([leaf ()])])

-- #eval test.positionList

@[grind =]
lemma IsPosi.iff_mem_positionList : p ∈ t.positionList ↔ t.IsPosi p := by
  induction p generalizing t with
  | nil => cases t <;> simp [positionList, IsPosi.nil]
  | cons i p ih =>
    cases t
    case leaf => simpa [positionList] using IsPosi.not_leaf_cons
    case node f ts =>
      rw [cons_mem_positionList_node]
      constructor
      · grind
      · intro h
        cases h
        case cons hi h =>
          use ⟨i, hi⟩
          grind

instance instDecidablePredIsPosi : DecidablePred s.IsPosi :=
  fun _ => decidable_of_decidable_of_iff IsPosi.iff_mem_positionList

lemma shapeEq_iff_positionList_subset_subset :
    s.ShapeEq t ↔ (s.positionList ⊆ t.positionList ∧ t.positionList ⊆ s.positionList) := by
  refine ⟨fun h => ⟨?_, ?_⟩, ?_⟩
  · grind [ShapeEq]
  · grind [ShapeEq]
  · intro ⟨hst, hts⟩ p
    rw [←IsPosi.iff_mem_positionList]
    grind

instance instDecidableShapeEq : DecidableRel (ShapeEq (S := S) (X := X)) :=
  fun _ _ => decidable_of_decidable_of_iff shapeEq_iff_positionList_subset_subset.symm

instance instFintypeSubtypeIsPosi : Fintype {p : List ℕ // t.IsPosi p} :=
  Fintype.subtype t.positionList.toFinset <| by grind [List.mem_toFinset]

def getName : (t : PTree S X) → (p : List ℕ) → t.IsPosi p → (S ⊕ X)
  | leaf x, _, _ => .inr x
  | node f _, [], _ => .inl f
  | node _ ts, i :: p, h => (ts[i]'h.idx_lt_length).getName p h.of_cons

lemma getName_nil_eq_inr_iff : getName t ([]) IsPosi.nil' = .inr x ↔ t = leaf x := by
  cases t <;> simp [getName]

lemma getName_nil_eq_inl_iff : getName t ([]) IsPosi.nil' = .inl f ↔ ∃ ts, t = node f ts := by
  cases t <;> simp [getName]

theorem ext_getName_of_shapeEq (s t : PTree S X) (hshape : ShapeEq s t)
    (hname : ∀ p (hsp : s.IsPosi p), getName s p hsp = getName t p (hshape.mp p hsp)) :
    s = t := by
  cases t
  case leaf x =>
    apply (getName_nil_eq_inr_iff (x := x)).mp
    simpa [getName] using hname [] IsPosi.nil'
  case node f ts =>
    have := hname [] IsPosi.nil'
    rw [getName, getName_nil_eq_inl_iff] at this
    obtain ⟨ss, rfl⟩ := this
    congr
    apply List.ext_getElem hshape.node_length_eq
    intro i his hit
    have : ts[i].size < (node f ts).size := size_getElem_lt_size hit
    apply ext_getName_of_shapeEq
    · intro p hsp
      apply hname (i :: p)
      apply IsPosi.cons <;> simpa
    · intro p
      have := hshape (i :: p)
      grind [IsPosi.cons]
  termination_by t.size

theorem ext_getName_shapeEq_iff (s t : PTree S X) :
    (∃ (h : ShapeEq s t), ∀ p (hsp : s.IsPosi p), getName s p hsp = getName t p (h.mp p hsp)) ↔
      s = t := by
  constructor
  · intro ⟨hshape, hname⟩
    exact ext_getName_of_shapeEq s t hshape hname
  · grind

theorem ext_getName_shapeEq_iff_subtype (s t : PTree S X) :
    (∃ (h : ShapeEq s t),
    ∀ p : {p // s.IsPosi p}, getName s p p.prop = getName t p (h.mp p p.prop)) ↔
      s = t := by
  constructor
  · intro ⟨hshape, hname⟩
    exact ext_getName_of_shapeEq s t hshape (fun p hp => hname ⟨p, hp⟩)
  · grind

instance instDecidableEqPTree [DecidableEq S] [DecidableEq X] : DecidableEq (PTree S X) :=
  fun s t => decidable_of_decidable_of_iff (ext_getName_shapeEq_iff_subtype s t)

inductive IsLeafPosi : (t : PTree S X) → List ℕ → Prop where
  | leaf (x : X) : IsLeafPosi (leaf x) ([])
  | node (f : S) (ts : List (PTree S X)) (i : ℕ) (hi : i < ts.length) (p : List ℕ) :
    ts[i].IsLeafPosi p → IsLeafPosi (node f ts) (i :: p)

lemma IsLeafPosi.isPosi (h : t.IsLeafPosi p) : t.IsPosi p := by
  induction h with
  | leaf _ => exact IsPosi.nil'
  | node _ _ _ hi _ _ ih => exact ih.cons hi

lemma IsLeafPosi.getElem (h : t.IsLeafPosi p) : ∃ x : X, t[p]'h.isPosi = PTree.leaf x := by
  induction h with
  | leaf x => use x; exact getElem_nil
  | node _ _ _ hi _ hp ih =>
    obtain ⟨x, hx⟩ := ih
    use x
    rwa [getElem_cons hi hp.isPosi]

lemma isLeafPosi_iff_getElem?_eq : t.IsLeafPosi p ↔ ∃ x, t[p]? = some (leaf x) := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h.getElem
    grind
  · intro ⟨x, hx⟩
    replace ⟨h, hx⟩ := getElem_of_getElem? hx
    induction h with
    | nil => rw [getElem_nil] at hx; exact hx ▸ IsLeafPosi.leaf x
    | cons hi hp ih =>
      apply IsLeafPosi.node _ _ _ hi _
      apply ih
      rwa [getElem_cons hi hp] at hx

end Cslib.PTree

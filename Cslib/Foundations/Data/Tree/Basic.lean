/-
Copyright (c) 2026 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Cslib.Foundations.Syntax.HasSubstitution
public import Cslib.Foundations.Syntax.Congruence
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.Group.Nat

public section

namespace Cslib

inductive PTree (S X : Type _) where
  | leaf (x : X) : PTree S X
  | node (f : S) : List (PTree S X) → PTree S X

namespace PTree

variable {S X : Type _}

def size : PTree S X → ℕ
  | leaf _ => 1
  | node f ts => 1 + (ts.map size).sum

@[simp]
lemma size_node {f : S} {ts : List (PTree S X)} : (node f ts).size = 1 + (ts.map size).sum :=
  by simp [size]

@[grind .]
lemma size_getElem_lt_size {f : S} {ts : List (PTree S X)} {i : ℕ} (hi : i < ts.length) :
    ts[i].size < (node f ts).size := by
  have : ts[i].size ≤ (ts.map size).sum :=
    List.le_sum_of_mem <| List.mem_map_of_mem <| List.getElem_mem hi
  grind [size]

def isLeaf : (s : PTree S X) → Bool
  | leaf _ => true
  | node _ _ => false

lemma isLeaf_eq_true_iff_exists {s : PTree S X} : s.isLeaf ↔ ∃ x, s = leaf x := by
  cases s
  all_goals simp [isLeaf]

inductive IsSubtree : PTree S X → PTree S X → Prop
  | refl (t : PTree S X) : t.IsSubtree t
  | tail (f : S) (ts : List (PTree S X)) (t' : PTree S X) (ht' : t' ∈ ts) (s : PTree S X) :
    s.IsSubtree t' → s.IsSubtree (node f ts)

attribute [refl] IsSubtree.refl

lemma IsSubtree.size_le {s t : PTree S X} (h : s.IsSubtree t) : s.size ≤ t.size := by
  induction h
  case refl => rfl
  case tail f ts t' ht' s hst' ih =>
    apply le_trans ih
    have : t'.size ≤ (ts.map size).sum := (ts.map size).le_sum_of_mem <| List.mem_map_of_mem ht'
    grind [size]

lemma IsSubtree.eq_of_size_eq (s t : PTree S X) (h : s.IsSubtree t)
    (h' : s.size = t.size) : s = t := by
  cases h
  case refl => rfl
  case tail f ts t' ht' hst' =>
    suffices s.size < (node f ts).size by absurd h'; exact this.ne
    have : t'.size ≤ (ts.map size).sum := (ts.map size).le_sum_of_mem <| List.mem_map_of_mem ht'
    grind [size, size_le hst']

instance instPartialOrderPTree : PartialOrder (PTree S X) where
  le := IsSubtree
  le_refl := PTree.IsSubtree.refl
  le_trans s t u hst htu := by
    induction htu
    case refl => assumption
    case tail f us u' hu' t ht ih =>
      exact PTree.IsSubtree.tail f us u' hu' _ (ih hst)
  le_antisymm s t hst hts := by
    have hst_size := hst.size_le
    have hts_size := hts.size_le
    have : s.size = t.size := Nat.le_antisymm hst_size hts_size
    exact hst.eq_of_size_eq s t this

inductive IsPosi : (t : PTree S X) → List ℕ → Prop
  | emp (t : PTree S X) : IsPosi t ([])
  | tail (f : S) (ts : List (PTree S X)) (i : ℕ) (hi : i < ts.length) (p : List ℕ) :
      ts[i].IsPosi p → (node f ts).IsPosi (i :: p)

-- attribute [scoped grind .] IsPosi.tail IsPosi.emp
attribute [scoped grind cases] IsPosi

@[scoped grind .]
lemma IsPosi.nil {t : PTree S X} : t.IsPosi [] := IsPosi.emp t

-- scoped macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| apply IsPosi.nil)

@[scoped grind .]
lemma IsPosi.node {f : S} {ts : List (PTree S X)} {i : ℕ} (hi : i < ts.length) {p : List ℕ}
    (hp : ts[i].IsPosi p) : (node f ts).IsPosi (i :: p) := IsPosi.tail f ts i hi p hp

lemma IsPosi.not_leaf_cons {x : X} {i : ℕ} {p : List ℕ} (h : (leaf (S := S) x).IsPosi (i :: p)) :
  False := by cases h

@[scoped grind .]
lemma IsPosi.idx_lt_length {f : S} {ts : List (PTree S X)} {i : ℕ} {p : List ℕ}
  (h : (PTree.node f ts).IsPosi (i :: p)) : i < ts.length := by cases h; assumption

lemma IsPosi.isPosi_tail {f : S} {ts : List (PTree S X)} {i : ℕ} {p : List ℕ}
    (h : (PTree.node f ts).IsPosi (i :: p)) : (ts[i]'h.idx_lt_length).IsPosi p := by
  cases h
  assumption

@[simp, grind =]
lemma IsPosi.singleton {f : S} {ts : List (PTree S X)} {i : ℕ} :
    (PTree.node f ts).IsPosi [i] ↔ i < ts.length := by grind

@[scoped grind →]
theorem IsPosi.prefix {t : PTree S X} {p q : List ℕ} (hq : t.IsPosi q) (hpq : p <+: q) :
    t.IsPosi p := by
  obtain ⟨q, rfl⟩ := hpq
  induction p generalizing t with
  | nil => exact IsPosi.nil
  | cons i p ih =>
    cases hq
    case tail _ _ hi h => exact (ih h).node hi

@[scoped grind →]
theorem IsPosi.prefix' {t : PTree S X} {p q : List ℕ} (hq : t.IsPosi (p ++ q)) : t.IsPosi p :=
  hq.prefix <| List.prefix_append ..

theorem IsPosi.head_succ {f : S} {t : PTree S X} {ts : List (PTree S X)} {i : ℕ} {p : List ℕ} :
    (PTree.node f (t :: ts)).IsPosi ((i + 1) :: p) ↔ (PTree.node f ts).IsPosi (i :: p) := by
  constructor <;> intro h <;> cases h <;> apply node <;> grind

def isPosiBool : List ℕ → PTree S X → Bool
  | [], _ => true
  |  (_ :: _), leaf _ => false
  | (_ :: _), node _ ([]) => false
  | (0 :: p), node _ (t :: _) => isPosiBool p t
  | ((i + 1) :: p), node f (_ :: ts) => isPosiBool (i :: p) (node f ts)

lemma isPosiBool_iff_IsPosi : (p : List ℕ) → (t : PTree S X) → (isPosiBool p t ↔ t.IsPosi p)
  | [], _ => by simpa [isPosiBool] using IsPosi.nil
  | (_ :: _), leaf _ => by
    constructor <;> intro h
    · simp [isPosiBool] at h
    · cases h
  | (_ :: _), node f ([]) => by
    simp only [isPosiBool, Bool.false_eq_true, false_iff]
    intro hc; cases hc; grind
  | (0 :: p), PTree.node _ (t :: ts) => by
    constructor <;> intro h
    · rw [isPosiBool, isPosiBool_iff_IsPosi] at h
      apply IsPosi.tail <;> grind
    · cases h
      case tail hi hp =>
        rw [isPosiBool, isPosiBool_iff_IsPosi]
        simpa using hp
  | ((i + 1) :: p), PTree.node f (t :: ts) => by
    rw [isPosiBool, isPosiBool_iff_IsPosi, IsPosi.head_succ]

instance instDecidableIsPosi {t : PTree S X} {p : List ℕ} : Decidable (t.IsPosi p) :=
  decidable_of_bool (isPosiBool p t) (isPosiBool_iff_IsPosi p t)

def getElemPos : (t : PTree S X) → (p : List ℕ) → (t.IsPosi p) → PTree S X
  | t, [], _ => t
  | leaf _, (i :: p), h => by apply False.elim; cases h
  | node f ts, (i :: p), h =>
      getElemPos (ts[i]'(by cases h; assumption)) p (by cases h; assumption)

instance instGetElemPTreePos : GetElem (PTree S X) (List ℕ) (PTree S X) IsPosi where
  getElem := getElemPos

@[simp, grind =]
lemma getElem_nil {t : PTree S X} : t[[]]'IsPosi.nil = t := by simp [getElem, getElemPos]

@[simp, scoped grind =]
lemma getElem_cons {f : S} {ts : List (PTree S X)} {i : ℕ} (hi : i < ts.length) {p : List ℕ}
    (hp : ts[i].IsPosi p) : (node f ts)[i :: p]'(hp.node hi) = ts[i][p] := by
  simp_rw [getElem, getElemPos]
  rfl

theorem IsPosi.suffix {t : PTree S X} {p q : List ℕ} (h : t.IsPosi (p ++ q)) :
    (t[p]'(h.prefix <| List.prefix_append p q)).IsPosi q := by
  induction p generalizing t with
  | nil => simpa
  | cons i p ih =>
    cases h
    case tail f ts hi h => exact ih h

@[grind →]
lemma IsPosi_append {t : PTree S X} {p q : List ℕ} (hp : t.IsPosi p) (hq : t[p].IsPosi q) :
    t.IsPosi (p ++ q) := by
  induction p generalizing t with
  | nil => simpa
  | cons i p ih =>
    cases hp
    apply IsPosi.tail
    · apply ih
      · simp_all
      · assumption

@[grind =]
theorem getElem_append_eq {t : PTree S X} {p q : List ℕ} (h : t.IsPosi (p ++ q)) :
    t[p ++ q] = (t[p]'h.prefix')[q]'h.suffix := by
  induction p generalizing t with
  | nil => simp
  | cons i p ih => grind

@[grind .]
theorem isSubtree_getElem {t : PTree S X} {p : List ℕ} (hp : t.IsPosi p) : t[p] ≤ t := by
  induction p generalizing t with
  | nil => rfl
  | cons i p ih =>
    cases hp
    case tail f ts hi h =>
      have : ts[i].IsSubtree (node f ts) := IsSubtree.tail _ _ ts[i] (List.getElem_mem _) _ (by rfl)
      refine le_trans ?_ this
      apply ih

theorem IsSubtree.exists_getElem?_eq {s t : PTree S X} (h : s ≤ t) :
    ∃ p : List ℕ, t[p]? = some s := by
  induction h with
  | refl t => use []; simp [getElem?, IsPosi.nil]
  | tail f ts t' ht' s h ih =>
    classical
    obtain ⟨p, ih⟩ := ih
    obtain ⟨hp, ih⟩ := getElem_of_getElem? ih
    use ts.idxOf t' :: p
    have hi : ts.idxOf t' < ts.length := List.idxOf_lt_length_of_mem ht'
    have : (node f ts).IsPosi (ts.idxOf t' :: p) := by
      apply IsPosi.tail (hi := hi)
      simpa [hi]
    rw [getElem?_eq_some_iff]
    use this
    rw [getElem_cons (hi := hi) (hp := by grind)]
    simpa [hi]

theorem IsSubtree.exists_isPosi_getElem_eq {s t : PTree S X} (h : s.IsSubtree t) :
    ∃ (p : List ℕ) (h : t.IsPosi p), t[p] = s := by
  obtain ⟨p, hp⟩ := h.exists_getElem?_eq
  use p
  simpa [getElem?_eq_some_iff] using hp

def subst (t u : PTree S X) (p : List ℕ) : PTree S X :=
  match t, p with
  | _, [] => u
  | leaf x, (_ :: _) => leaf x
  | node f ts, (i :: p) =>
      if hi : i < ts.length then
      node f <| ts.set i <| ts[i].subst u p else
      (node f ts)
  termination_by t.size
  decreasing_by exact size_getElem_lt_size hi

instance instHasSubstitutionPTree : HasSubstitution (PTree S X) (List ℕ) (PTree S X) where
  subst t p u := t.subst u p

protected structure Context (S X : Type _) where
  tree : PTree S X
  p : List ℕ
  isPosi_p : tree.IsPosi p

instance instHasContextPTree : HasContext (PTree S X) where
  Context := PTree.Context S X
  fill c t := c.tree[c.p := t]

variable {s t u : PTree S X} {p q r : List ℕ} {c : PTree.Context S X}

lemma subst_def : s[p:=t] = s.subst t p := rfl

@[simp, scoped grind =]
lemma subst_nil : s[([] : List ℕ):=t] = t := by
  simp [subst_def, subst]

@[simp, scoped grind =]
lemma subst_leaf_cons {x : X} {i : ℕ} : (leaf (S := S) x)[(i :: p):=t] = leaf x := by
  simp [subst_def, subst]

@[simp, scoped grind =>]
lemma subst_node_cons_of_lt_length {f : S} {i : ℕ} {ss : List (PTree S X)} (hi : i < ss.length) :
    (node f ss)[(i :: p):=t] = node f (ss.set i <| ss[i][p:=t]) := by simp [subst_def, subst, hi]

@[simp, scoped grind =>]
lemma subst_node_cons_of_ge_length {f : S} {i : ℕ} {ss : List (PTree S X)} (hi : ss.length ≤ i) :
    (node f ss)[(i :: p):=t] = node f ss := by simp [subst_def, subst, hi]

lemma subst_eq_self_of_not_isPosi {s t : PTree S X} {p : List ℕ} (h : ¬ s.IsPosi p) :
    s[p:=t] = s := by
  induction p generalizing s with
  | nil => exact False.elim <| h <| IsPosi.nil
  | cons i p ih =>
    cases s
    case leaf => simp
    case node f ss =>
      by_cases hi : i < ss.length
      case pos =>
        rw [subst_node_cons_of_lt_length hi]
        congr
        suffices ss[i][p:=t] = ss[i] by rw [this]; exact List.set_getElem_self hi
        apply ih
        contrapose h
        exact IsPosi.tail _ _ _ hi _ h
      case neg => rw [subst_node_cons_of_ge_length]; grind

@[simp, scoped grind =]
lemma Context.fill_eq : c[t] = c.tree[c.p := t] := rfl

lemma IsPosi.subst (h : s.IsPosi p) : s[p:=t].IsPosi p := by
  induction h with
  | emp s => exact IsPosi.nil
  | tail _ ts i hi p h ih => grind

lemma Context.isPosi_fill : c[t].IsPosi c.p := c.isPosi_p.subst

@[scoped grind =]
lemma getElem_subst_self_of_IsPosi (h : s.IsPosi p) : s[p:=t][p]'h.subst = t := by
  induction h with
  | emp s => simp
  | tail f  ts i hi p h ih => grind

lemma Context.getElem_fill_self : c[t][c.p]'c.isPosi_fill = t :=
  getElem_subst_self_of_IsPosi c.isPosi_p

@[simp, scoped grind .]
lemma append_IsPosi_subst (hp : s.IsPosi p) (hq : t.IsPosi q) : (s[p := t]).IsPosi (p ++ q) := by
  apply IsPosi_append
  rw [getElem_subst_self_of_IsPosi]
  all_goals assumption

@[simp, scoped grind =]
lemma getElem_subst_append_of_IsPosi (hp : s.IsPosi p) (hq : t.IsPosi q) :
    s[p:=t][p ++ q]'(append_IsPosi_subst hp hq) = t[q] := by
  rw [getElem_append_eq]
  congr
  exact getElem_subst_self_of_IsPosi hp

lemma subst_append_subst (hp : s.IsPosi p) (_ : t.IsPosi q) :
    (s[p:=t])[(p ++ q):=u] = s[p:=(t[q:=u])] := by
  induction p generalizing s with
  | nil => simp
  | cons i p ih =>
    cases hp
    case tail f ts hi h =>
      simp only [hi, subst_node_cons_of_lt_length, List.cons_append, List.length_set,
        List.getElem_set_self, List.set_set, node.injEq, true_and]
      apply List.ext_get (by simp)
      intro j hj hj'
      simp only [List.get_eq_getElem, List.getElem_set]
      split
      · apply ih h
      · rfl

lemma getElem_prefix_subst_append (h : s.IsPosi (p ++ q)) :
    s[(p++q):=t][p]'h.subst.prefix' = (s[p]'h.prefix')[q:=t] := by
  induction p generalizing s with
  | nil => simp
  | cons i p ih =>
    cases h
    case tail f ts hi h =>
      simp only [List.cons_append, subst_def, subst, hi, ↓reduceDIte]
      rw [getElem_cons hi h.prefix', getElem_cons (by simpa)]
      · simp_rw [subst_def] at ih
        rw [← ih h]
        grind
      · simpa using IsPosi.subst (t := t) h |>.prefix'

lemma subst_subst_append (h : s.IsPosi (p ++ q)) :
    (s[(p ++ q) := t])[p:=u] = s[p:=u] := by
  induction p generalizing s with
  | nil => simp
  | cons i p ih =>
    cases h
    case tail f ts hi h =>
      simp only [List.cons_append, subst_def, subst, hi, ↓reduceDIte, List.length_set,
        List.set_set, List.getElem_set_self, node.injEq, true_and]
      congr 1
      exact ih h

lemma subst_refl (h : s.IsPosi p) : s[p := s[p]] = s := by
  induction h <;> simp_all

namespace List

variable {α : Type*} {x₁ x₂ : α} {l l₁ l₂ : List α}

abbrev Parallel (l₁ l₂ : List α) : Prop := ¬ l₁ <+: l₂ ∧ ¬ l₂ <+: l₁

scoped infix:70 "||" => Parallel

lemma Parallel.left_not_prefix (h : l₁ || l₂) : ¬ l₁ <+: l₂ := h.1

lemma Parallel.right_not_prefix (h : l₁ || l₂) : ¬ l₂ <+: l₁ := h.2

@[grind .]
lemma not_parallel_self : ¬ (l || l) := fun h => h.left_not_prefix <| List.prefix_refl _

@[grind .]
lemma nil_not_parallel : ¬ ([] || l) := fun h => h.left_not_prefix List.nil_prefix

@[grind .]
lemma not_parallel_nil : ¬ (l || []) := fun h => h.right_not_prefix List.nil_prefix

@[grind =]
lemma IsParallel.symm : (l₁ || l₂) ↔ (l₂ || l₁) := and_comm

@[grind .]
lemma eq_of_not_cons_parallel (h : ¬ (x₁ :: l₁) || (x₂ :: l₂)) : x₁ = x₂ := by grind

lemma parallel_cons_iff : (x₁ :: l₁) || (x₂ :: l₂) ↔ (x₁ ≠ x₂ ∨ l₁ || l₂) := by grind

lemma parallel_cons_iff' : (x₁ :: l₁) || (x₂ :: l₂) ↔ (x₁ ≠ x₂ ∨ x₁ = x₂ ∧ l₁ || l₂) := by grind

lemma not_prefix_cons_iff : ¬ (x₁ :: l₁) <+: (x₂ :: l₂) ↔ (x₁ ≠ x₂ ∨ x₁ = x₂ ∧ ¬ l₁ <+: l₂) := by
  grind

end List

open List

lemma IsPosi.subst_of_not_prefix (hp : s.IsPosi p) (h : ¬ q <+: p) : s[q:=t].IsPosi p := by
  induction q generalizing s p with
  | nil => grind
  | cons j q ih =>
    cases hp
    case emp => grind
    case tail f ss i hi p hp =>
      obtain (hij | ⟨rfl, hpq⟩) := not_prefix_cons_iff.mp h
      · simp_rw [subst_def, PTree.subst]
        grind
      · simp_rw [subst_def, PTree.subst]
        split
        case isTrue h =>
          apply IsPosi.tail
          · rw [List.getElem_set_self]
            · exact ih hp hpq
            · grind
        case isFalse h => grind

lemma getElem_subst_eq_getElem_of_parallel (hp : s.IsPosi p) (hq : s.IsPosi q) (h : p || q) :
    (s[p:=t])[q]'(hq.subst_of_not_prefix h.left_not_prefix) = s[q] := by
  induction p generalizing s q with
  | nil => grind
  | cons i p ih =>
    cases hp
    case tail f ss hi hp =>
    cases hq
    case emp => grind
    case tail j q hj hq =>
    simp_rw [getElem_cons hj hq, subst_def, subst, hi, reduceDIte]
    have hj_set : j < (ss.set i <| ss[i].subst t p).length := by simpa
    obtain (hij | ⟨rfl, hpq⟩) := parallel_cons_iff'.mp h
    · have : j < (ss.modify i fun x => ss[i].subst t p).length := by simpa
      rw [getElem_cons hj_set]
      · simp_rw [ss.getElem_set_of_ne hij]
      · simp_rw [ss.getElem_set_of_ne hij]
        exact hq
    · simp_rw [getElem_cons (by simpa) (by simpa using hq.subst_of_not_prefix hpq.left_not_prefix),
        List.getElem_set_self]
      exact ih hp hq hpq

lemma subst_subst_comm_of_parallel (hp : s.IsPosi p) (hq : s.IsPosi q) (h : p || q) :
    (s[p:=t])[q:=u] = (s[q:=u])[p:=t] := by
  induction p generalizing s q with
  | nil => grind
  | cons i p ih =>
    cases hp
    case tail f ss hi hp =>
    cases hq
    case emp => grind
    case tail j q hj hq =>
    simp_rw [subst_def, subst, hi, hj, reduceDIte, subst, List.length_set, hi, hj, reduceDIte]
    congr 1
    apply List.ext_get (by simp)
    simp only [List.length_set, List.get_eq_getElem, List.getElem_set]
    intro k _ _
    simp_rw [subst_def] at ih
    split_ifs
    all_goals grind

end Cslib.PTree

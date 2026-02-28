/-
Copyright (c) 2026 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Cslib.Foundations.Syntax.HasWellFormed
public import Cslib.Foundations.Data.Tree.Rewriting

public section

namespace Cslib

structure Signature where
  Sym : Type _
  arity : Sym → ℕ

namespace PTree

variable {S X : Type _} {arity : S → ℕ}

def WF (arity : S → ℕ) : PTree S X → Prop
  | leaf _ => True
  | node f ts => ts.length = arity f ∧ ∀ t ∈ ts, t.WF arity

lemma WF.leaf_wf {x : X} : (leaf x).WF arity := by simp [WF]

@[grind →]
lemma WF.length_eq {f : S} {ts : List (PTree S X)} (h : (node f ts).WF arity) :
    ts.length = arity f := by grind [WF]

@[grind! .]
lemma WF.wf_of_mem {f : S} {ts : List (PTree S X)} (h : (node f ts).WF arity) {t : PTree S X}
    (ht : t ∈ ts) : t.WF arity := by rw [WF] at h; exact h.2 t ht

@[grind →]
lemma WF.lt_length_of_lt_arity {f : S} {ts : List (PTree S X)} (h : (node f ts).WF arity) {i : ℕ}
    (hi : i < arity f) : i < ts.length := h.length_eq ▸ hi

def WF.getArg {f : S} {ts : List (PTree S X)} (h : (node f ts).WF arity) {i : ℕ}
    (hi : i < arity f) : PTree S X := ts[i]'(h.lt_length_of_lt_arity hi)

lemma WF.cases {t : PTree S X} (h : t.WF arity) :
    (∃ x : X, leaf x = t) ∨
    ∃ (f : S) (ts : List (PTree S X)),
      (node f ts) = t ∧ ts.length = arity f ∧ ∀ t ∈ ts, t.WF arity := by
  cases t <;> grind [WF]

lemma WF.getElem {t : PTree S X} (h : t.WF arity) {p : List ℕ} (hp : t.IsPosi p) :
    t[p].WF arity := by
  induction p generalizing t with
  | nil => simpa
  | cons i p ih =>
    obtain (⟨x, rfl⟩ | ⟨f, ts, rfl, hlen, hts⟩) := h.cases
    · cases hp
    · cases hp
      case cons hi hp => grind

lemma WF.subst {s t : PTree S X} (hs : s.WF arity) (ht : t.WF arity) (p : List ℕ) :
    s[p:=t].WF arity := by
  by_cases h : s.IsPosi p
  · induction h with
    | nil => simpa
    | @cons f ss i hi p hp ih =>
      simp only [subst_node_cons_of_lt_length hi, WF, List.length_set]
      constructor
      · exact hs.length_eq
      · intro s' hs'
        obtain (hs' | rfl) := ss.mem_or_eq_of_mem_set hs'
        · exact wf_of_mem hs hs'
        · apply ih
          exact wf_of_mem hs (ss.getElem_mem hi)
  · rwa [subst_eq_self_of_not_isPosi h]

lemma WF.of_isSubtree {s t : PTree S X} (h : s ≤ t) (ht : t.WF arity) : s.WF arity := by
  induction h with
  | refl => exact ht
  | child f ts t' ht' s h ih => exact ih (ht.wf_of_mem ht')

end PTree

structure Term (Sig : Signature) (X : Type _) where
  t : PTree Sig.Sym X
  wf : t.WF Sig.arity

namespace PTree

def WF.childTerms {Sig : Signature} {X : Type _} {f : Sig.Sym} {ts : List (PTree Sig.Sym X)}
    (h : (PTree.node f ts).WF Sig.arity) : List (Term Sig X) :=
  ts.attach.map (fun ⟨t, ht⟩ => ⟨t, h.wf_of_mem ht⟩)

@[simp]
lemma WF.childTerms_length {Sig : Signature} {X : Type _} {f : Sig.Sym}
    {ts : List (PTree Sig.Sym X)} (h : (PTree.node f ts).WF Sig.arity) :
    h.childTerms.length = Sig.arity f := by
  simpa [WF.childTerms] using h.length_eq

lemma WF.childTerms_get_coe {Sig : Signature} {X : Type _} {f : Sig.Sym}
    {ts : List (PTree Sig.Sym X)} (h : (PTree.node f ts).WF Sig.arity) (i : Fin (Sig.arity f)) :
    h.childTerms[i].t = ts[i]'(by simp [h.length_eq]) := by
  simp [WF.childTerms]

def WF.getChild {Sig : Signature} {X : Type _} {f : Sig.Sym} {ts : List (PTree Sig.Sym X)}
    (h : (PTree.node f ts).WF Sig.arity) (i : Fin (Sig.arity f)) : Term Sig X :=
  h.childTerms[i]

lemma WF.getChild_coe_eq {Sig : Signature} {X : Type _} {f : Sig.Sym} {ts : List (PTree Sig.Sym X)}
    (h : (PTree.node f ts).WF Sig.arity) (i : Fin (Sig.arity f)) :
  (h.getChild i).t = h.childTerms[i].t := by simp [getChild]

open PTree in
lemma WF.getChild_size_lt {Sig : Signature} {X : Type _} {f : Sig.Sym}
    {ts : List (PTree Sig.Sym X)} (h : (PTree.node f ts).WF Sig.arity)
    (i : Fin (Sig.arity f)) :
    (h.getChild i).t.size < (PTree.node f ts).size := by
  simp only [getChild_coe_eq, childTerms, Fin.getElem_fin, List.getElem_map, List.getElem_attach,
    size_node, Nat.lt_one_add_iff]
  apply List.le_sum_of_mem
  grind

end PTree

namespace Term

@[ext]
lemma ext {s t : Term S X} (h : s.t = t.t) : s = t := by cases s; cases t; simpa

open PTree

variable {Sig : Signature} {X : Type _} {s t u : Term Sig X}

instance instCoeTermPTree : Coe (Term Sig X) (PTree Sig.Sym X) where
  coe := Term.t

def consNode (f : Sig.Sym) (ts : List (Term Sig X)) (hts : ts.length = Sig.arity f) : Term Sig X :=
  ⟨node f (ts.map Term.t), by simpa [WF, hts] using fun a _ => a.wf⟩

lemma consNode_coe_eq {f : Sig.Sym} {ts : List (Term Sig X)} (hts : ts.length = Sig.arity f) :
  (consNode f ts hts).t = node f (ts.map Term.t) := by simp [consNode]

def consNodeOfFn (f : Sig.Sym) (ts : Fin (Sig.arity f) → Term Sig X) : Term Sig X :=
  ⟨node f (List.ofFn <| Term.t ∘ ts), by simpa [WF] using fun a => (ts a).wf⟩

lemma consNodeOfFn_eq {f : Sig.Sym} (ts : Fin (Sig.arity f) → Term Sig X) :
    consNodeOfFn f ts =
      ⟨node f (List.ofFn <| Term.t ∘ ts), by simpa [WF] using fun a => (ts a).wf⟩ := by
  simp [consNodeOfFn]

-- lemma consNodeOfFn_childTerms {f : Sig.Sym} (ts : Fin (Sig.arity f) → Term Sig X) :
--     (consNodeOfFn f ts).wf.childTerms = List.ofFn <| Term.t ∘ ts

/--
The following result can be used to deconstruct a `Term` by cases on its underlying tree, for
instance:
```
example (t : Term Sig X) : True := by
  obtain ⟨t, ht⟩ := t
  obtain (⟨x, rfl⟩ | ⟨f, ts, hts, rfl⟩) := (⟨t, ht⟩ : Term Sig X).wf_cases
   <;> sorry
```
-/
lemma wf_cases (t : Term Sig X) :
    (∃ x : X, (leaf (S := Sig.Sym) x = t)) ∨
    (∃ (f : Sig.Sym) (ts : List (Term Sig X)),
      ts.length = Sig.arity f ∧ (node f (ts.map Term.t) = t)) := by
  replace ⟨t, ht⟩ := t
  cases t
  case leaf x => left; use x
  case node f ts =>
    right; use f, ht.childTerms
    simpa [WF.childTerms] using ht.length_eq

instance instGetElemTerm : GetElem (Term Sig X) (List ℕ) (Term Sig X) (fun t => t.t.IsPosi) where
  getElem t p hp := ⟨t.t[p], t.wf.getElem hp⟩

instance instHasSubstitutionTerm : HasSubstitution (Term Sig X) (List ℕ) (Term Sig X) where
  subst s p t := ⟨s.t[p := t.t], s.wf.subst t.wf p⟩

end Cslib.Term

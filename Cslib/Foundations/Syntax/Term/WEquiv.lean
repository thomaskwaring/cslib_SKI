/-
Copyright (c) 2026 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Cslib.Foundations.Syntax.Term.Basic
public import Mathlib.Data.W.Basic

public section

namespace Cslib.Term

open PTree

variable {S X : Type*} {Sig : Signature}

inductive Wα (Sig : Signature) (X : Type _) : Type _ where
  | leaf : (x : X) → Wα Sig X
  | node : (f : Sig.sym) → Wα Sig X

@[expose]
def Wβ (Sig : Signature) (X : Type _) : Wα Sig X → Type _
  | Wα.leaf _ => PEmpty
  | Wα.node f => Fin (Sig.arity f)

instance (a : Wα Sig X) : Fintype (Wβ Sig X a) := by
  cases a <;> rw [Wβ] <;> infer_instance


@[expose]
protected def W (Sig : Signature) (X : Type _) := WType (Wβ Sig X)

def toW (t : Term Sig X) : Term.W Sig X :=
  match t with
  | ⟨leaf x, _⟩ => WType.mk (Wα.leaf x) PEmpty.elim
  | ⟨node f ts, ht⟩ => WType.mk (Wα.node f) (fun i => (ht.getChild i).toW)
  termination_by t.t.size
  decreasing_by
    exact ht.getChild_size_lt i

def ofW (w : Term.W Sig X) : Term Sig X :=
  match w with
  | ⟨(Wα.leaf x), _⟩ => ⟨PTree.leaf x, WF.leaf_wf⟩
  | ⟨Wα.node f, ts⟩ => consNode f (List.ofFn (fun i => ofW (ts i))) (by simp)

lemma left_inv_W (t : PTree Sig.sym X) (ht : t.WF Sig.arity) :
    ofW (⟨t, ht⟩ : Term Sig X).toW = ⟨t, ht⟩ := by
  cases t
  case leaf => simp [toW, ofW]
  case node f ts =>
    rw [Term.mk.injEq, toW, ofW, consNode_coe_eq]
    congr
    apply List.ext_get
    · simpa using ht.length_eq.symm
    · intro i hi₁ hi₂
      simp only [List.get_eq_getElem, List.map_ofFn, List.getElem_ofFn, Function.comp_apply]
      have : (ht.getChild ⟨i, by grind⟩ |>.t.size) < (node f ts).size := ht.getChild_size_lt _
      have hinv := left_inv_W <| ht.getChild ⟨i, by grind⟩
      have hget := ht.childTerms_get_coe ⟨i, by grind⟩
      simpa [hinv, ht.getChild_coe_eq] using hget
  termination_by t.size

lemma right_inv_W (w₀ : Term.W Sig X) : (ofW w₀).toW = w₀ := by
  match w₀ with
  | ⟨Wα.leaf _, _⟩ =>
    rw [ofW, toW]; congr; ext u
    exact PEmpty.elim u
  | ⟨Wα.node f, ws⟩ =>
    have hinv := fun i => right_inv_W (ws i)
    have hcoe := consNode_coe_eq (f := f) (ts := List.ofFn fun i => ofW (ws i)) (by simp)
    have : (consNode f (List.ofFn fun i => ofW (ws i)) (by simp)) =
      ⟨(consNode f (List.ofFn fun i => ofW (ws i)) (by simp)).t,
      (consNode f (List.ofFn fun i => ofW (ws i)) (by simp)).wf⟩ := rfl
    rw [ofW, this]
    simp_rw [hcoe, toW]
    congr
    ext i
    rw [← hinv]
    congr
    rw [Term.mk.injEq, WF.getChild_coe_eq, WF.childTerms_get_coe]
    simp
  termination_by w₀.depth
  decreasing_by
    exact WType.depth_lt_depth_mk (f := ws) ..

def equivW : Term Sig X ≃ Term.W Sig X where
  toFun := toW
  invFun := ofW
  left_inv := by
    intro ⟨t, ht⟩
    exact left_inv_W t ht
  right_inv := right_inv_W

end Cslib.Term

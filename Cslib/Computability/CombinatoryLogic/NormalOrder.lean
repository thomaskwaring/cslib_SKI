import Cslib.Computability.CombinatoryLogic.Evaluation
import Mathlib.Data.List.Induction

namespace SKI

inductive Prim where
  | S₀ | K₀ | I₀

@[coe]
def Prim.toSKI : Prim → SKI
  | S₀ => S
  | K₀ => K
  | I₀ => I

open Prim

instance PrimToSKI : Coe Prim SKI := ⟨Prim.toSKI⟩

protected structure Tree where
  head : Prim
  tail : List SKI.Tree

def Tree.toSKI : SKI.Tree → SKI
  | ⟨x, xs⟩ => (↑x : SKI).applyList <| List.map Tree.toSKI xs

protected def toTree : SKI → SKI.Tree
  | S => ⟨S₀, []⟩
  | K => ⟨K₀, []⟩
  | I => ⟨I₀, []⟩
  | a ⬝ b => let ⟨x,xs⟩ := a.toTree; ⟨x, xs ++ [b.toTree]⟩

def Tree.size : SKI.Tree → Nat
  | ⟨x, xs⟩ => 1 + (List.sum <| List.map Tree.size xs)

lemma coe_toTree (x : Prim) : (↑x : SKI).toTree = ⟨x, []⟩ := by cases x <;> rfl

theorem toTree_of_toSKI (t : SKI.Tree) : t.toSKI.toTree = t := by
  let ⟨x,xs⟩ := t
  refine List.reverseRecOn xs ?nil ?app
  case nil => simp [Tree.toSKI, applyList, coe_toTree]
  case app =>
    intro ys y ih
    -- have : Tree.size y < Tree.size ⟨x, xs⟩ := by sorry
    simp only [Tree.toSKI, List.map_append, List.map_cons, List.map_nil, applyList_concat]
    have : (↑x : SKI).applyList (List.map Tree.toSKI ys) = (⟨x, ys⟩ : SKI.Tree).toSKI := by
      simp [Tree.toSKI]
    simp! [this, ih, toTree_of_toSKI y]
  termination_by Tree.size t
  decreasing_by sorry



-- def treeEquiv : Equiv SKI SKI.Tree where
--   toFun := SKI.toTree
--   invFun := SKI.Tree.toSKI

--   left_inv := by
--     intro x

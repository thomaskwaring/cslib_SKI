import Cslib.Semantics.ReductionSystem.Basic

@[reduction_sys rs "ₙ", simp]
def PredReduction (a b : ℕ) : Prop := a = b + 1

lemma single_step : 5 ⭢ₙ 4 := by
  change PredReduction _ _
  simp

-- `Trans` instances allow us to switch between single and multistep reductions in a `calc` block
lemma multiple_step : 5 ↠ₙ 1 := by
  -- TODO: can/should this be a `simp` attribute somewhere?
  have h : rs.Red = PredReduction := by rfl
  calc
    5 ⭢ₙ 4 := by simp [h]
    _ ↠ₙ 2 := by
      calc
        4 ⭢ₙ 3 := by simp [h]
        _ ⭢ₙ 2 := by simp [h]
    _ ⭢ₙ 1 := by simp [h]

-- ensure that this still works when there are variables
inductive Term (Var : Type)
variable {Var : Type}

@[reduction_sys rs' "β", simp]
def term_rel : Term Var → Term Var → Prop := λ _ _ ↦ True

example (a b : Term Var) : a ⭢β b := by
  change (@term_rel Var) a b
  simp

-- check that a "cannonical" notation also works
attribute [reduction_sys cannonical_rs] PredReduction

example : 5 ⭢ 4 := by 
  change PredReduction _ _
  simp

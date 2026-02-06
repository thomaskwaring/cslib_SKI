/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
import Cslib.Logics.Propositional.NaturalDeduction.Lemmas
import Mathlib.Tactic.ITauto

/-! # Double-negative translations via monads

This treatment generalizes the double-negation translations of classical into intuitionistic and
minimal logic. The rough idea is that the larger logic add a princple of "`f`-elimination", for
some operator `f` on propositions. Using the properties of this operator (in the cases at hand),
we can cook up a new translation denoted `(·)ᵒ`, with the properties:
- `f Aᵒ ≡[T + f-elim] Aᵒ`, for every `A`, and
- `Γ ⊢[T + f-elim] Bᵒ` implies `Γᵒ ⊢[T] Bᵒ`, so long as `⊢[T] (f A ⟶ A)ᵒ` for each `A`.

The classical case is when `f A = ~~A`, and `Aᵒ` is the "Gödel-Gentzen translation" from classical
to minimal logic. The difference between IPL and MPL is captured by `f A = A ∪ ⊥`, so that
`f`-elimination becomes the disjunctive syllogism `A ∪ ⊥ ⟶ A`, which is equivalent to the principle
of explosion.

Finally, the terminology "monad" is no coincidence here in cslib — this ought to relate to monads
qua "notions of computation" (Moggi). At very least the two operators mentioned above mimic,
respectively, continuation-passing style and computations with failiure.

### References

- van den Berg, *A Kuroda-style* j-*translation*,
<https://link.springer.com/article/10.1007/s00153-018-0656-x>
- Aczel, *The Russell–Prawitz modality*, <https://doi.org/10.1017/S0960129501003309>
-/

namespace PL

open Proposition Theory Derivation

variable {Atom : Type _} [DecidableEq Atom] {T : Theory Atom}

/-! ### Monads -/

structure TMonad (T : Theory Atom) where
  f : Proposition Atom → Proposition Atom
  map : T.Derivation ⟨{A ⟶ B}, f A ⟶ f B⟩
  pure (A : Proposition Atom) : T.Derivation ⟨∅, A ⟶ f A⟩
  join (A : Proposition Atom) : T.Derivation ⟨∅ , f (f A) ⟶ f A⟩

open TMonad

def TMonad.mapDer (t : TMonad T) {A B : Proposition Atom} (D : T.Derivation ⟨{A}, B⟩) :
    T.Derivation ⟨{t.f A}, t.f B⟩ := by
  refine implE (A := t.f A) ?_ (ass <| by grind)
  refine cut (Γ := {t.f A}) (Δ := ∅) (A := A ⟶ B) ?_ ?_
  · apply implI
    exact D.weak_ctx (by grind)
  · exact t.map

def TMonad.pure' (t : TMonad T) (A : Proposition Atom) : T.Derivation ⟨{A}, t.f A⟩ := by
  apply implE (A := A)
  · exact t.pure A |>.weak_ctx (by grind)
  · exact ass <| by grind

def TMonad.preserveEquiv (t : TMonad T) {A B : Proposition Atom} (e : T.equiv A B) :
    T.equiv (t.f A) (t.f B) := ⟨t.mapDer e.1, t.mapDer e.2⟩

def TMonad.tBind (t : TMonad T) {A B : Proposition Atom} :
    T.Derivation ⟨{t.f A, A ⟶ t.f B}, t.f B⟩ := by
  apply implE (A := t.f (t.f B)) (t.join B |>.weak_ctx <| by grind)
  apply implE (A := t.f A)
  · exact t.map.weak_ctx <| by grind
  · exact ass <| by grind

def TMonad.tSeq (t : TMonad T) {A B : Proposition Atom} :
    T.Derivation ⟨{t.f A, t.f (A ⟶ B)}, t.f B⟩ := by
  refine Theory.Derivation.cut (Γ := {t.f A, t.f (A ⟶ B)}) (Δ := {t.f (A ⟶ B)})
    (A := (A ⟶ B) ⟶ t.f B) ?_ ?_ |>.weak_ctx (by grind)
  · apply implI
    apply implE (A := t.f A)
    · exact t.map (A := A) (B := B) |>.weak_ctx (by grind)
    · exact ass <| by grind
  · exact t.tBind (A := A ⟶ B) (B := B) |>.weak_ctx (by grind)

def TMonad.tSeq₂ (t : TMonad T) {A B C : Proposition Atom} :
    T.Derivation ⟨{t.f A, t.f B, t.f (A ⟶ (B ⟶ C))}, t.f C⟩ := by
  refine Theory.Derivation.cut
      (Γ := {t.f A, t.f B, t.f (A ⟶ (B ⟶ C))})
      (Δ := {t.f B})
      (A := t.f (B ⟶ C)) ?_ (t.tSeq (A := B) (B := C) |>.weak_ctx (by grind))
    |>.weak_ctx (by grind)
  · exact t.tSeq (A := A) (B := B ⟶ C) |>.weak_ctx (by grind)

theorem TMonad.map_sDerivable (t : TMonad T) {Γ : Ctx Atom} {B : Proposition Atom} (h : Γ ⊢[T] B) :
    (Γ.image t.f) ⊢[T] (t.f B) := by
  induction Γ using Finset.induction generalizing B with
  | empty =>
    let ⟨D⟩ := h
    constructor
    apply implE (A := B)
    · exact (t.pure B).weak_ctx <| by grind
    · exact D.weak_ctx <| by grind
  | insert A Γ  _ ih =>
    let ⟨D⟩ := h
    let ⟨E⟩ := ih ⟨D.implI⟩
    constructor
    · rw [Finset.image_insert]
      refine Theory.Derivation.cut (Γ := Γ.image t.f) (Δ := {t.f A}) (A := t.f (A ⟶ B)) E ?_
        |>.weak_ctx <| by grind
      exact t.tSeq (A := A) (B := B) |>.weak_ctx (by grind)

def TMonad.idem (t : TMonad T) (A : Proposition Atom) : T.equiv (t.f A) (t.f (t.f A)) := by
  constructor
  · exact implE (A := t.f A) (t.pure (t.f A) |>.weak_ctx <| by grind) (ass <| by grind)
  · exact implE (A := t.f (t.f A)) (t.join A |>.weak_ctx <| by grind) (ass <| by grind)

def TMonad.equivImplF (t : TMonad T) (A B : Proposition Atom) :
    T.equiv (A ⟶ t.f B) (t.f (A ⟶ t.f B)) := by
  constructor
  · apply implE (A := A ⟶ t.f B)
    · exact t.pure (A ⟶ t.f B) |>.weak_ctx <| by grind
    · exact ass <| by grind
  · apply implI
    apply implE (A := t.f (t.f B))
    · exact t.join B |>.weak_ctx <| by grind
    · refine Theory.Derivation.cut (Γ := {A}) (A := t.f A) (Δ := {t.f (A ⟶ t.f B)}) ?_ t.tSeq
        |>.weak_ctx (by grind)
      exact implE (t.pure A |>.weak_ctx (by grind)) (ass <| by grind)

def TMonad.conjShift (t : TMonad T) (A B : Proposition Atom) :
    T.equiv (t.f (A ⋏ B)) (t.f A ⋏ t.f B) := by
  constructor
  · apply conjI   -- this direction only uses functoriality
    · apply t.mapDer; exact conjE₁ (B := B) <| ass <| by grind
    · apply t.mapDer; exact conjE₂ (A := A) <| ass <| by grind
  · refine implE (A := t.f B) (implE (A := t.f A) ?_ ?_) ?_
    · apply implI; apply implI
      apply implE (A := t.f (A ⟶ (B ⟶ (A ⋏ B))))
      · apply implI
        exact t.tSeq₂ (A := A) (B := B) (C := A ⋏ B) |>.weak_ctx <| by grind
      · apply implE (A := A ⟶ (B ⟶ (A ⋏ B))) (t.pure (A ⟶ (B ⟶ (A ⋏ B))) |>.weak_ctx <| by grind)
        apply implI; apply implI
        apply conjI <;> exact ass <| by grind
    · exact conjE₁ (B := t.f B) <| ass <| by grind
    · exact conjE₂ (A := t.f A) <| ass <| by grind

def TMonad.disjShift (t : TMonad T) (A B : Proposition Atom) :
    T.equiv (t.f (A ⋎ B)) (t.f (t.f A ⋎ t.f B)) := by
  constructor
  · apply t.mapDer
    apply disjE (A := A) (B := B) (ass <| by grind)
    · apply disjI₁
      exact t.pure' A |>.weak_ctx (by grind)
    · apply disjI₂
      exact t.pure' B |>.weak_ctx (by grind)
  · refine Theory.Derivation.cut (Γ := ∅) (Δ := {t.f (t.f A ⋎ t.f B)})
        (A := t.f A ⋎ t.f B ⟶ t.f (A ⋎ B)) ?_ ?_
    · apply implI
      apply disjE (A := t.f A) (B := t.f B) (ass <| by grind)
      · let : T.Derivation ⟨{A}, A ⋎ B⟩ := disjI₁ <| ass (by grind)
        exact t.mapDer this |>.weak_ctx (by grind)
      · let : T.Derivation ⟨{B}, A ⋎ B⟩ := disjI₂ <| ass (by grind)
        exact t.mapDer this |>.weak_ctx (by grind)
    · exact t.tBind (A := t.f A ⋎ t.f B) (B := A ⋎ B) |>.weak_ctx (by grind)

/-! ### *j*-Translation -/

/-- Gödel-Gentzen style translation. -/
@[reducible]
def TMonad.gg (t : TMonad T) : Proposition Atom → Proposition Atom
  | atom x => t.f (atom x)
  | conj A B => conj (t.gg A) (t.gg B)
  | disj A B => t.f <| disj (t.gg A) (t.gg B)
  | impl A B => impl (t.gg A) (t.gg B)

def TMonad.ggActionEquiv (t : TMonad T) :
    (A : Proposition Atom) → T.equiv (t.f <| t.gg A) (t.gg A)
  | atom x => commEquiv <| t.idem <| atom x
  | conj A B => by
    refine transEquiv (B := t.f (t.gg A) ⋏ t.f (t.gg B)) ?_ ?_
    · exact t.conjShift (t.gg A) (t.gg B)
    · exact infWD _ _ _ _ (t.ggActionEquiv A) (t.ggActionEquiv B)
  | disj A B => commEquiv <| t.idem _
  | impl A B => by
    let eA := t.ggActionEquiv A
    let eB := t.ggActionEquiv B
    constructor
    · apply implI
      apply mapEquivHypothesis {t.f (t.gg A ⟶ t.gg B)} eA
      apply mapEquivConclusion _ eB
      exact t.tSeq
    · apply implE (A := t.gg A ⟶ t.gg B)
      · exact t.pure (t.gg A ⟶ t.gg B) |>.weak_ctx (Finset.empty_subset _)
      · exact ass <| by exact Finset.mem_singleton.mpr rfl

def TMonad.preserveDerivation (t : TMonad T) {T' : Theory Atom}
    (derT' : ∀ A ∈ T', T.Derivation ⟨∅, t.gg A⟩) {Γ : Ctx Atom} {B : Proposition Atom} :
      T'.Derivation ⟨Γ, B⟩ → T.Derivation ⟨Γ.image t.gg, t.gg B⟩
  | ax hB => (derT' B hB).weak_ctx <| Finset.empty_subset _
  | ass hB => ass (by grind)
  | conjI D E => conjI (t.preserveDerivation derT' D) (t.preserveDerivation derT' E)
  | conjE₁ D => conjE₁ (t.preserveDerivation derT' D)
  | conjE₂ D => conjE₂ (t.preserveDerivation derT' D)
  | @disjI₁ _ _ _ _ A B D => by
    apply implE (A := (t.gg A ⋎ t.gg B))
    · exact t.pure (t.gg A ⋎ t.gg B) |>.weak_ctx (by grind)
    · exact disjI₁ (t.preserveDerivation derT' D)
  | @disjI₂ _ _ _ _ A B D => by
    apply implE (A := (t.gg A ⋎ t.gg B))
    · exact t.pure (t.gg A ⋎ t.gg B) |>.weak_ctx (by grind)
    · exact disjI₂ (t.preserveDerivation derT' D)
  | @disjE _ _ _ _ A B C D E E' => by
    apply mapEquivConclusion _ (t.ggActionEquiv C)
    refine cut (Γ := Γ.image t.gg) (Δ := Γ.image t.gg) (A := t.f (t.gg A ⋎ t.gg B))
      (t.preserveDerivation derT' D) ?_ |>.weak_ctx (by grind)
    refine cut (Γ := Γ.image t.gg) (Δ := {t.f <| (t.gg A) ⋎ (t.gg B)})
        (A := (t.gg A) ⋎ (t.gg B) ⟶ t.f (t.gg C)) ?_ ?_ |>.weak_ctx (by grind)
    · apply implI
      apply mapEquivConclusion _ (commEquiv <| t.ggActionEquiv C)
      apply disjE (A := t.gg A) (B := t.gg B) (ass <| by grind)
      · exact (t.preserveDerivation derT' E).weak_ctx <| by grind
      · exact (t.preserveDerivation derT' E').weak_ctx <| by grind
    · exact t.tBind (A := t.gg A ⋎ t.gg B) (B := t.gg C) |>.weak_ctx (by grind)
  | implI _ D => implI (Γ.image t.gg) (Finset.image_insert t.gg _ Γ ▸ t.preserveDerivation derT' D)
  | implE D E => implE (t.preserveDerivation derT' D) (t.preserveDerivation derT' E)

theorem TMonad.preserve_derivability (t : TMonad T) {T' : Theory Atom}
    (derT' : ∀ A ∈ T', ⊢[T] t.gg A) {Γ : Ctx Atom} {B : Proposition Atom} :
    Γ ⊢[T'] B → (Γ.image t.gg) ⊢[T] t.gg B
  | ⟨D⟩ => ⟨t.preserveDerivation (fun A hA => Classical.choice <| derT' A hA) D⟩

@[reducible]
def TMonad.TElim (t : TMonad T) : Theory Atom := Set.range (fun A => t.f A ⟶ A)

/-! TODO: all of these results actually apply to `T'` such that `T ∪ t.TElim ≤ T'`. -/

def TMonad.actionTrivOfTElim (t : TMonad T) (A : Proposition Atom) :
    (T ∪ t.TElim).equiv A (t.f A) := by
  constructor
  · apply implE (A := A)
    · apply (t.pure A).weak <;> grind
    · exact ass <| by grind
  · exact implE (A := t.f A) (ax <| by grind) (ass <| by grind)

def TMonad.ggEquiv (t : TMonad T) : (A : Proposition Atom) → (T ∪ t.TElim).equiv A (t.gg A)
  | atom x => t.actionTrivOfTElim (atom x)
  | conj A B => infWD _ _ _ _ (t.ggEquiv A) (t.ggEquiv B)
  | disj A B => by
    refine transEquiv (B := t.gg A ⋎ t.gg B) ?_ ?_
    · apply supWD <;> exact t.ggEquiv _
    · exact t.actionTrivOfTElim _
  | impl A B => himpWD _ _ _ _ (t.ggEquiv A) (t.ggEquiv B)

theorem TMonad.derivable_tElim_iff (t : TMonad T) (hT : ∀ A ∈ T, ⊢[T] t.gg A)
    (h : ∀ A : Proposition Atom, ⊢[T] t.gg (t.f A ⟶ A)) :
    Γ ⊢[T ∪ t.TElim] B ↔ (Γ.image t.gg) ⊢[T] (t.gg B) := by
  constructor <;> intro h_der
  · refine t.preserve_derivability (T' := T ∪ t.TElim) ?_ h_der
    intro A hA
    rw [Set.mem_union, Set.mem_range] at hA
    cases hA
    case inl hA => exact hT A hA
    case inr hA =>
      replace ⟨A', hA⟩ := hA
      rw [← hA]
      exact h A'
  · induction Γ using Finset.induction generalizing B with
    | empty =>
      refine (((T ∪ t.TElim).equiv_iff_equiv_conclusion (A := t.gg B) (B := B)).mp ?_ <|
          (∅ : Ctx Atom)).mp ?_
      · exact ⟨commEquiv (t.ggEquiv B)⟩
      · exact h_der.weak_theory (by grind)
    | insert A Γ _ ih =>
      suffices (T ∪ t.TElim).SDerivable ⟨Γ, A ⟶ B⟩ by
        let ⟨D⟩ := this
        exact ⟨implE (A := A) (D.weak_ctx <| by grind) (ass <| by grind)⟩
      apply ih (B := A ⟶ B)
      let ⟨D⟩ := h_der
      exact ⟨implI _ <| (Finset.image_insert t.gg _ _) ▸ D⟩


/-! ### Examples -/

section PseudoNeg

variable [PseudoBot Atom]

def mapDN {A B : Proposition Atom} : T.Derivation ⟨{A ⟶ B}, ~ᵣ~ᵣA ⟶ ~ᵣ~ᵣB⟩ := by
  apply implI; apply implI
  apply implE (A := ~ᵣA) (ass <| by grind)
  apply implI
  apply implE (A := B) (ass <| by grind)
  apply implE (A := A) <;> exact ass (by grind)

def pureDN (A : Proposition Atom) : T.Derivation ⟨∅, A ⟶ ~ᵣ~ᵣA⟩ := by
  apply implI; apply implI
  apply implE (A := A) <;> exact ass <| by grind

def joinDN (A : Proposition Atom) : T.Derivation ⟨∅, ~ᵣ~ᵣ~ᵣ~ᵣA ⟶ ~ᵣ~ᵣA⟩ := implI _ tripleNeg.1

def DN : (TMonad T) where
  f := (~ᵣ~ᵣ ·)
  map := mapDN
  pure := pureDN
  join := joinDN

def mapOrB {A B : Proposition Atom} : T.Derivation ⟨{A ⟶ B}, (A ⋎ ⊥ᵣ) ⟶ (B ⋎ ⊥ᵣ)⟩ := by
  apply implI
  apply disjE (A := A) (B := ⊥ᵣ) (ass <| by grind)
  · apply disjI₁; apply implE (A := A) <;> exact ass <| by grind
  · apply disjI₂; exact ass (by grind)

def pureOrB (A : Proposition Atom) : T.Derivation ⟨∅, A ⟶ A ⋎ ⊥ᵣ⟩ :=
  implI _ <| disjI₁ <| ass <| by grind

def joinOrB (A : Proposition Atom) : T.Derivation ⟨∅, (A ⋎ ⊥ᵣ) ⋎ ⊥ᵣ ⟶ A ⋎ ⊥ᵣ⟩ := by
  apply implI
  apply disjE (A := A ⋎ ⊥ᵣ) (B := ⊥ᵣ) (ass <| by grind) (ass <| by grind)
  apply disjI₂; exact ass <| by grind

def OrB : (TMonad T) where
  f := (· ⋎ ⊥ᵣ)
  map := mapOrB
  pure := pureOrB
  join := joinOrB

def mapPierce {A B : Proposition Atom} :
    T.Derivation ⟨{A ⟶ B}, (~ᵣA ⟶ A) ⟶ (~ᵣB ⟶ B)⟩ := by
  apply implI; apply implI
  apply implE (A := A) (ass <| by grind)
  apply implE (A := ~ᵣA) (ass <| by grind)
  apply implI
  apply implE (A := B) (ass <| by grind)
  apply implE (A := A) <;> exact ass <| by grind

def purePierce (A : Proposition Atom) : T.Derivation ⟨∅, A ⟶ (~ᵣA ⟶ A)⟩ :=
  implI _ <| implI _ <| ass <| by grind

def joinPierce (A : Proposition Atom) :
    T.Derivation ⟨∅, (~ᵣ(~ᵣA ⟶ A) ⟶ (~ᵣA ⟶ A)) ⟶ (~ᵣA ⟶ A)⟩ := by
  apply implI; apply implI
  refine implE (A := ~ᵣA) ?_ (ass <| by grind)
  apply implE (A := ~ᵣ(~ᵣA ⟶ A)) (ass <| by grind)
  apply implI
  apply implE (A := A)
  · exact ass <| by grind
  · apply implE (A := ~ᵣA) <;> exact ass <| by grind

def Pierce : (TMonad T) where
  f A := ~ᵣA ⟶ A
  map := mapPierce
  pure := purePierce
  join := joinPierce

end PseudoNeg

end PL

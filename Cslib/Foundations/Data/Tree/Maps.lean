/-
Copyright (c) 2026 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Cslib.Foundations.Data.Tree.Basic

public section

namespace Cslib.PTree

variable {S S' X X' : Type _} {s t u : PTree S X}

def mapSym (σ : S → S') : PTree S X → PTree S' X
  | leaf x => leaf x
  | node f ts => node (σ f) (ts.map <| mapSym σ)

def mapVar (σ : X → PTree S X') : PTree S X → PTree S X'
  | leaf x => σ x
  | node f ts => node f (ts.map <| mapVar σ)

def flatten (s : PTree S (PTree S X)) : PTree S X := s.mapVar id

instance instMonadPTree : Monad (PTree S) where
  pure := leaf
  bind s σ := mapVar σ s

lemma mapVar_leaf : (s : PTree S X) → (mapVar leaf s) = s
  | leaf _ => by simp [mapVar]
  | node _ ss => by
    simp_rw [mapVar]
    congr
    rewrite (occs := .pos [2]) [(List.map_id ss).symm]
    exact List.map_congr_left <| fun s' _ => mapVar_leaf s'

lemma mapVar_mapVar {X X' X'' : Type _} (σ : X → PTree S X') (ρ : X' → PTree S X'') :
    (s : PTree S X) → mapVar (fun x => mapVar ρ (σ x)) s = mapVar ρ (mapVar σ s)
  | leaf _ => by simp [mapVar]
  | node _ ss => by
    simp only [mapVar, List.map_map, node.injEq, List.map_inj_left, Function.comp_apply, true_and]
    intro s' _
    apply mapVar_mapVar

instance instLawfulMonadPTree : LawfulMonad (PTree S) := by
  apply LawfulMonad.mk'
  · intro _ s
    simpa [Functor.map, mapVar] using mapVar_leaf s
  · simp [pure, bind, mapVar]
  · intro _ _ _ s σ ρ
    simpa [bind, mapVar] using (mapVar_mapVar σ ρ s).symm
  · simp [Functor.mapConst, Functor.map]
  · simp [SeqLeft.seqLeft, bind, pure]
  · simp [SeqRight.seqRight, bind]
  · intro _ _ _ _
    simp only [bind, pure, Functor.map]
    congr
  · simp [Functor.map, bind, Seq.seq]

variable {σ : X → PTree S X'} {p : List ℕ}

lemma mapVar_eq_bind : mapVar σ t = t >>= σ := rfl

@[simp]
lemma bind_leaf {x : X} : (leaf x) >>= σ = σ x := by rw [←mapVar_eq_bind, mapVar]

@[simp]
lemma bindLeft_node {f : S} {ts : List (PTree S X)} :
    node f ts >>= σ = node f (ts.map <| (· >>= σ)) := by
  simp_rw [←mapVar_eq_bind, mapVar]

lemma IsPosi.bind (hp : t.IsPosi p) : (t >>= σ).IsPosi p := by
  induction p generalizing t with
  | nil => exact IsPosi.nil'
  | cons i p ih =>
    cases hp
    case cons f ts hi hp =>
      rw [bindLeft_node]
      apply IsPosi.cons (hi := (List.length_map _).symm ▸ hi)
      simpa using ih hp

lemma bind_getElem_comm (hp : t.IsPosi p) : (t >>= σ)[p]'hp.bind = t[p] >>= σ := by
  induction p generalizing t with
  | nil => simp
  | cons i p ih =>
    cases hp
    case cons f ts hi hp =>
      have : ((ts.map (· >>= σ))[i]'((List.length_map _).symm ▸ hi)).IsPosi p :=
        by simpa using hp.bind (σ := σ)
      have := getElem_cons (f := f) ((List.length_map _).symm ▸ hi) this
      simpa [this, hi, hp] using ih hp

lemma bind_subst (hp : s.IsPosi p) : s[p:=t] >>= σ = (s >>= σ)[p := t >>= σ] := by
  induction p generalizing s with
  | nil => simp
  | cons i p ih =>
    cases hp
    case cons f ts hi hp =>
      simp only [hi, subst_node_cons_of_lt_length, bindLeft_node, List.map_set, List.length_map,
        List.getElem_map, node.injEq, true_and]
      congr
      apply ih hp

def IsInstance (s : PTree S X) (t : PTree S X') : Prop := ∃ σ, s >>= σ = t

scoped infix:50 " ≿ " => IsInstance

lemma IsInstance.refl (s : PTree S X) : s ≿ s := ⟨pure, bind_pure s⟩

lemma IsInstance.trans {s t u : PTree S X} (hst : s ≿ t) (htu : t ≿ u) : s ≿ u := by
  obtain ⟨σ, rfl⟩ := hst
  obtain ⟨ρ, rfl⟩ := htu
  rw [bind_assoc]
  exact ⟨fun x => σ x >>= ρ, rfl⟩

lemma bind_isInstance : s ≿ (s >>= σ) := ⟨σ, rfl⟩

end Cslib.PTree

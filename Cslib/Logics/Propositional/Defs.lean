/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
import Mathlib.Order.Notation
import Mathlib.Data.FunLike.Basic

/-! # Propositions

We define `Proposition`, the type of propositions over a given type of atom. This type has a `Bot`
instance whenever `Atom` does, and a `Top` whenever `Atom` is inhabited. We introduce notation for
the logical connectives: `⊥ ⊤ ⋏ ⋎ ⟶ ~` for, respectively, falsum, verum, conjunction, disjunction,
implication and negation.

NB: starting from a base type `Atom`, a canonical bottom element can be added using `WithBot Atom`,
from `Mathlib.Order.TypeTags` — this is defined as `Option Atom`, but conveniently adds all the
requisite coercions, instances, etc.
-/

universe u

variable {Atom : Type u} [DecidableEq Atom]

namespace PL

/-- Propositions. -/
inductive Proposition (Atom : Type u) : Type u where
  /-- Propositional atoms -/
  | atom (x : Atom)
  /-- Conjunction -/
  | conj (a b : Proposition Atom)
  /-- Disjunction -/
  | disj (a b : Proposition Atom)
  /-- Implication -/
  | impl (a b : Proposition Atom)
deriving DecidableEq, BEq

instance instBotProposition [Bot Atom] : Bot (Proposition Atom) := ⟨.atom ⊥⟩
instance instInhabitedOfBot [Bot Atom] : Inhabited Atom := ⟨⊥⟩

/-- We view negation as a defined connective ~A := A → ⊥ -/
abbrev Proposition.neg [Bot Atom] : Proposition Atom → Proposition Atom := (Proposition.impl · ⊥)

/-- A fixed choice of a derivable proposition (of course any two are equivalent). -/
def Proposition.top [Inhabited Atom] : Proposition Atom := impl (.atom default) (.atom default)

instance instTopProposition [Inhabited Atom] : Top (Proposition Atom) := ⟨.top⟩

example [Bot Atom] : (⊤ : Proposition Atom) = Proposition.impl ⊥ ⊥ := rfl

@[inherit_doc] scoped infix:35 " ⋏ " => Proposition.conj
@[inherit_doc] scoped infix:35 " ⋎ " => Proposition.disj
@[inherit_doc] scoped infix:30 " ⟶ " => Proposition.impl
@[inherit_doc] scoped prefix:40 " ~ " => Proposition.neg

def Proposition.map {Atom Atom' : Type u} (f : Atom → Atom') : Proposition Atom → Proposition Atom'
  | atom x => atom (f x)
  | conj A B => conj (A.map f) (B.map f)
  | disj A B => disj (A.map f) (B.map f)
  | impl A B => impl (A.map f) (B.map f)

instance {Atom Atom' : Type u} : FunLike (Atom → Atom') (Proposition Atom) (Proposition Atom') where
  coe := Proposition.map
  coe_injective' f f' h := by
    ext x
    have : (Proposition.atom x).map f = (Proposition.atom x).map f' :=
      congrFun h (Proposition.atom x)
    grind [Proposition.map]

end PL

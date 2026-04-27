/-
Copyright (c) 2026 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
module

public import Cslib.Init
public import Mathlib.Order.Heyting.Basic
public import Mathlib.Order.Hom.BoundedLattice

@[expose] public section

open Function

variable {F α β γ δ : Type*} [FunLike F α β]

structure HImpHom (α β : Type*) [HImp α] [HImp β] where
  toFun : α → β
  map_himp' (a b : α) : toFun (a ⇨ b) = toFun a ⇨ toFun b

class HImpHomClass (F α β : Type*) [HImp α] [HImp β] [FunLike F α β] : Prop where
  map_himp (f : F) (a b : α) : f (a ⇨ b) = f a ⇨ f b

export HImpHomClass (map_himp)

attribute [simp] HImpHomClass.map_himp

namespace HImpHom

variable [HImp α] [HImp β] [HImp γ] [HImp δ]

instance : FunLike (HImpHom α β) α β where
  coe := HImpHom.toFun
  coe_injective' f g h := by cases f; cases g; congr

instance : HImpHomClass (HImpHom α β) α β where
  map_himp := HImpHom.map_himp'

@[simp] lemma toFun_eq_coe (f : HImpHom α β) : f.toFun = f := rfl

@[simp, norm_cast]
lemma coe_mk (f : α → β) (hf) : ⇑(mk f hf) = f := rfl

@[ext]
theorem ext {f g : HImpHom α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

variable (α)

/-- `id` as a `HImpHom`. -/
protected def id : HImpHom α α :=
  { toFun := id
    map_himp' := fun _ _ => rfl }

@[simp, norm_cast]
theorem coe_id : ⇑(HImpHom.id α) = id :=
  rfl

variable {α}

@[simp]
theorem id_apply (a : α) : HImpHom.id α a = a :=
  rfl

instance : Inhabited (HImpHom α α) :=
  ⟨HImpHom.id _⟩

/-- Composition of `HImpHom`s as a `HImpHom`. -/
def comp (f : HImpHom β γ) (g : HImpHom α β) : HImpHom α γ :=
  { toFun := f ∘ g
    map_himp' := fun a b => by simp }

variable {f f₁ f₂ : HImpHom α β} {g g₁ g₂ : HImpHom β γ}

@[simp]
theorem coe_comp (f : HImpHom β γ) (g : HImpHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl

@[simp]
theorem comp_apply (f : HImpHom β γ) (g : HImpHom α β) (a : α) : f.comp g a = f (g a) :=
  rfl

@[simp]
theorem comp_assoc (f : HImpHom γ δ) (g : HImpHom β γ) (h : HImpHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
theorem comp_id (f : HImpHom α β) : f.comp (HImpHom.id α) = f :=
  ext fun _ => rfl

@[simp]
theorem id_comp (f : HImpHom α β) : (HImpHom.id β).comp f = f :=
  ext fun _ => rfl

@[simp]
theorem cancel_right (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, congr_arg (fun a ↦ comp a f)⟩

@[simp]
theorem cancel_left (hg : Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => HImpHom.ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩

end HImpHom

structure GeneralizedHeytingHom (α β : Type*) [GeneralizedHeytingAlgebra α]
    [GeneralizedHeytingAlgebra β] extends LatticeHom α β, HImpHom α β

class GeneralizedHeytingHomClass (F α β : Type*) [GeneralizedHeytingAlgebra α]
    [GeneralizedHeytingAlgebra β] [FunLike F α β] extends LatticeHomClass F α β, HImpHomClass F α β

namespace GeneralizedHeytingHom

variable [GeneralizedHeytingAlgebra α] [GeneralizedHeytingAlgebra β] [GeneralizedHeytingAlgebra γ]
  [GeneralizedHeytingAlgebra δ]

instance : FunLike (GeneralizedHeytingHom α β) α β where
  coe f := f.toFun
  coe_injective' f g h := by obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f; obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g; congr

instance : GeneralizedHeytingHomClass (GeneralizedHeytingHom α β) α β where
  map_sup f := f.map_sup'
  map_inf f := f.map_inf'
  map_himp f := f.map_himp'

@[simp] lemma toFun_eq_coe (f : GeneralizedHeytingHom α β) : f.toFun = f := rfl

@[simp] lemma coe_toLatticeHom (f : GeneralizedHeytingHom α β) : ⇑f.toLatticeHom = f := rfl

@[simp] lemma coe_mk (f : LatticeHom α β) (hf) : ⇑(mk f hf) = f := rfl

@[ext]
theorem ext {f g : GeneralizedHeytingHom α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

variable (α)

/-- `id` as a `GeneralizedHeytingHom`. -/
protected def id : GeneralizedHeytingHom α α :=
  { LatticeHom.id _ with
    map_himp' := fun _ _ => rfl }

@[simp, norm_cast]
theorem coe_id : ⇑(GeneralizedHeytingHom.id α) = id :=
  rfl

variable {α}

@[simp]
theorem id_apply (a : α) : GeneralizedHeytingHom.id α a = a :=
  rfl

instance : Inhabited (GeneralizedHeytingHom α α) :=
  ⟨GeneralizedHeytingHom.id _⟩

instance : PartialOrder (GeneralizedHeytingHom α β) :=
  PartialOrder.lift _ DFunLike.coe_injective

/-- Composition of `GeneralizedHeytingHom`s as a `GeneralizedHeytingHom`. -/
def comp (f : GeneralizedHeytingHom β γ) (g : GeneralizedHeytingHom α β) :
    GeneralizedHeytingHom α γ :=
  { f.toLatticeHom.comp g.toLatticeHom with
    toFun := f ∘ g
    map_himp' := fun a b => by simp }

variable {f f₁ f₂ : GeneralizedHeytingHom α β} {g g₁ g₂ : GeneralizedHeytingHom β γ}

@[simp]
theorem coe_comp (f : GeneralizedHeytingHom β γ) (g : GeneralizedHeytingHom α β) :
  ⇑(f.comp g) = f ∘ g := rfl

@[simp]
theorem comp_apply (f : GeneralizedHeytingHom β γ) (g : GeneralizedHeytingHom α β) (a : α) :
  f.comp g a = f (g a) := rfl

@[simp]
theorem comp_assoc (f : GeneralizedHeytingHom γ δ) (g : GeneralizedHeytingHom β γ)
  (h : GeneralizedHeytingHom α β) : (f.comp g).comp h = f.comp (g.comp h) := rfl

@[simp]
theorem comp_id (f : GeneralizedHeytingHom α β) : f.comp (GeneralizedHeytingHom.id α) = f :=
  ext fun _ => rfl

@[simp]
theorem id_comp (f : GeneralizedHeytingHom α β) : (GeneralizedHeytingHom.id β).comp f = f :=
  ext fun _ => rfl

@[simp]
theorem cancel_right (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, congr_arg (fun a ↦ comp a f)⟩

@[simp]
theorem cancel_left (hg : Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => GeneralizedHeytingHom.ext fun a => hg <| by rw [← comp_apply, h, comp_apply],
    congr_arg _⟩

end GeneralizedHeytingHom

@[simp]
protected lemma GeneralizedHeytingHomClass.map_top [GeneralizedHeytingAlgebra α]
    [GeneralizedHeytingAlgebra β] [GeneralizedHeytingHomClass F α β] (f : F) : f ⊤ = ⊤ := by
  rw [← @himp_self α _ ⊤, map_himp, himp_self]

structure HeytingHom (α β : Type*) [HeytingAlgebra α]
    [HeytingAlgebra β] extends GeneralizedHeytingHom α β where
  protected map_bot' : toFun ⊥ = ⊥

class HeytingHomClass (F α β : Type*) [HeytingAlgebra α]
    [HeytingAlgebra β] [FunLike F α β] extends GeneralizedHeytingHomClass F α β where
  map_bot (f : F) : f ⊥ = ⊥

variable [HeytingAlgebra α] [HeytingAlgebra β] [HeytingAlgebra γ] [HeytingAlgebra δ]
  [HeytingHomClass F α β] (f : F)

instance (priority := 100) HeytingHomClass.toBoundedLatticeHomClass [FunLike F α β]
    [HeytingAlgebra α] {_ : HeytingAlgebra β} [HeytingHomClass F α β] :
    BoundedLatticeHomClass F α β :=
  { ‹HeytingHomClass F α β› with
    map_top := GeneralizedHeytingHomClass.map_top }

namespace HeytingHom

instance : FunLike (HeytingHom α β) α β where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩ := f; obtain ⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩ := g; congr

instance : HeytingHomClass (HeytingHom α β) α β where
  map_sup f := f.map_sup'
  map_inf f := f.map_inf'
  map_himp f := f.map_himp'
  map_bot f := f.map_bot'

@[simp] lemma toFun_eq_coe (f : HeytingHom α β) : f.toFun = f := rfl

@[simp] lemma coe_toGeneralizedHeytingHom (f : HeytingHom α β) :
  ⇑f.toGeneralizedHeytingHom = f := rfl

@[simp] lemma coe_mk (f : GeneralizedHeytingHom α β) (hf) : ⇑(mk f hf) = f := rfl

@[ext]
theorem ext {f g : HeytingHom α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

variable (α)

/-- `id` as a `HeytingHom`. -/
protected def id : HeytingHom α α :=
  { BotHom.id _ with
    toLatticeHom := LatticeHom.id _
    map_himp' := fun _ _ => rfl }

@[simp, norm_cast]
theorem coe_id : ⇑(HeytingHom.id α) = id :=
  rfl

variable {α}

@[simp]
theorem id_apply (a : α) : HeytingHom.id α a = a :=
  rfl

instance : Inhabited (HeytingHom α α) :=
  ⟨HeytingHom.id _⟩

instance : PartialOrder (HeytingHom α β) :=
  PartialOrder.lift _ DFunLike.coe_injective

/-- Composition of `HeytingHom`s as a `HeytingHom`. -/
def comp (f : HeytingHom β γ) (g : HeytingHom α β) : HeytingHom α γ :=
  { f.toLatticeHom.comp g.toLatticeHom with
    toFun := f ∘ g
    map_bot' := by simp
    map_himp' := fun a b => by simp }

variable {f f₁ f₂ : HeytingHom α β} {g g₁ g₂ : HeytingHom β γ}

@[simp]
theorem coe_comp (f : HeytingHom β γ) (g : HeytingHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl

@[simp]
theorem comp_apply (f : HeytingHom β γ) (g : HeytingHom α β) (a : α) : f.comp g a = f (g a) :=
  rfl

@[simp]
theorem comp_assoc (f : HeytingHom γ δ) (g : HeytingHom β γ) (h : HeytingHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
theorem comp_id (f : HeytingHom α β) : f.comp (HeytingHom.id α) = f :=
  ext fun _ => rfl

@[simp]
theorem id_comp (f : HeytingHom α β) : (HeytingHom.id β).comp f = f :=
  ext fun _ => rfl

@[simp]
theorem cancel_right (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, congr_arg (fun a ↦ comp a f)⟩

@[simp]
theorem cancel_left (hg : Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => HeytingHom.ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩

end HeytingHom

@[simp] lemma map_compl (a : α) : f aᶜ = (f a)ᶜ := by rw [←himp_bot, map_himp, map_bot, himp_bot]

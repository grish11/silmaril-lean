module

public import Silmaril.Logic.BrookesSC.Concrete.Thms

/-! # Singleton observations of the concrete SC institution -/

@[expose] public section

namespace Silmaril.Logic.BrookesSC.Concrete.Observation

open CategoryTheory Silmaril.Semantics.Brookes

universe u

variable {W : World.{u}} [DecidableEq W.Cell] [DecidableEq W.Mutex] [DecidableEq W.Thread]
variable {A : Type u} {S : Signature W}

/-- Successful runs on one store, with a typed result. -/
abbrev StateRelation (W : World.{u}) (A : Type u) := Store W → Store W → A → Prop

/-- Keep only the singleton transition observations. -/
def observe (behavior : Behavior (Store W) A) : StateRelation W A :=
  behavior.completes

/-- The store semantics of the same signature, using relational sequencing
with a matching middle store. -/
abbrev stateTarget (W : World.{u}) [DecidableEq W.Cell] [DecidableEq W.Mutex] [DecidableEq W.Thread] :
    Target.{u,u} W where
  Carrier := StateRelation W
  order _ :=
    { le := fun x y => ∀ s t a, x s t a → y s t a
      le_refl _ := fun _ _ _ h => h
      le_trans _ _ _ h₁ h₂ := fun s t a h => h₂ s t a (h₁ s t a h) }
  pure a s t r := s = t ∧ r = a
  bind x k s t r := ∃ m a, x s m a ∧ k a m t r
  primitive p s t r := Store.step p s = some (r, t)
  bind_mono h hk s t r := by
    rintro ⟨m, a, hl, hr⟩
    exact ⟨m, a, h s m a hl, hk a m t r hr⟩

/-- Observe the interpretation of each external label at one transition. -/
def observeModel (M : TraceModel S) : Model (stateTarget W) S :=
  ⟨fun op => observe (M.external op)⟩

/-- Singleton observation is monotone on models of a fixed signature. -/
def observeModelFunctor (S : Signature W) : TraceModel S ⥤ Model (stateTarget W) S where
  obj := observeModel
  map h := ⟨fun op _ _ _ mem => h.down op mem⟩
  map_id _ := rfl
  map_comp _ _ := rfl

end Silmaril.Logic.BrookesSC.Concrete.Observation

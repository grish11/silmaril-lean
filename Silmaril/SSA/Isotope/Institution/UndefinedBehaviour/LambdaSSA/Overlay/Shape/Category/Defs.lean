module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Defs

/-! # Interfaces and arrows of shaped stateful observations -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category

universe v w x

/-- An exact label interface for a fixed value and state carrier and atom typing. -/
structure Interface (α : Type w) (σ : Type x) {κ : Type v} (atomType : α → κ → Prop) where
  labels : List (Ty κ)

variable {α : Type w} {σ : Type x} {κ : Type v} {atomType : α → κ → Prop}

/-- The payload supplied to a particular input label. -/
abbrev Interface.Payload (X : Interface α σ atomType) (i : Fin X.labels.length) :=
  {a : Value α // ValueTyped atomType a (X.labels.get i)}

/-- Observational arrows take a typed input and a machine state. Every
ordinary successful exit carries a typed result. Fault, divergence and
fresh top are also permitted. -/
structure Arrow (X Y : Interface α σ atomType) where
  run (i : Fin X.labels.length) (a : X.Payload i) (s : σ) : Behaviour Y.labels.length α σ
  returnsTyped (i : Fin X.labels.length) (a : X.Payload i) (s : σ) :
    ReturnsTyped atomType (L := Y.labels) (run i a s)

variable {X Y : Interface α σ atomType}

/-- Extend a typed arrow to the raw inputs accepted by `Behaviour.bind`.
An ill-typed input has empty ordinary behaviour. Composition calls the
second arrow only on typed ordinary exits of the first. -/
noncomputable def Arrow.total (f : Arrow X Y) (i : Fin X.labels.length) (a : Value α) (s : σ) :
    Behaviour Y.labels.length α σ := by
  classical
  exact if h : ValueTyped atomType a (X.labels.get i) then f.run i ⟨a, h⟩ s else ↑(∅ : Set (Outcome Y.labels.length α σ))

@[simp] theorem Arrow.total_typed (f : Arrow X Y) (i : Fin X.labels.length) (a : X.Payload i) (s : σ) :
    f.total i a.val s = f.run i a s := by
  exact dite_eq_left a.property

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category

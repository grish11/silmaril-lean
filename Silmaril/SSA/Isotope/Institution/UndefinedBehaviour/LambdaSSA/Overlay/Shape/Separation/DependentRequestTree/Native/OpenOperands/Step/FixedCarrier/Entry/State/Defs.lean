module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Entry.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.State.Defs

/-! # Transporting a concrete shared-entry witness -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Category.FiniteIteration

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {A : Syntax.Ty} {n m : Nat}

/-- Keep the shared caller and extend the typed script to the new carrier
by mapping its states. Unlisted queries still use ordinary divergence. -/
def EntryCounterexample.mapState (w : EntryCounterexample Φ A n) (e : Fin n ↪ Fin m) :
    EntryCounterexample Φ A m :=
  ⟨w.input, e w.initial, w.script.map (InterpreterScript.Row.mapState e)⟩

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

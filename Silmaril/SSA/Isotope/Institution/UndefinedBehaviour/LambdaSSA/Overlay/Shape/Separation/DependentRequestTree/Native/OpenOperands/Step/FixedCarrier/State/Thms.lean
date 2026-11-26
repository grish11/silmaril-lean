module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Thms
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.State.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.State.Transport

/-! # Preserving decorated observations across state embeddings -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay

universe u v w

/-- Injective store renaming reflects as well as preserves the lifted
observation order, including the distinction between ordinary sets and top. -/
theorem Behaviour.mapState_le_iff {labels : Nat} {α : Type u} {σ : Type v} {τ : Type w}
    (e : σ ↪ τ) (p q : Behaviour labels α σ) : p.mapState e ≤ q.mapState e ↔ p ≤ q :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FixedCarrier.State.mapState_le_iff
    e p q

namespace Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Category.FiniteIteration
open CFG.Dependent.Native (withExitUB)
open ScheduleSearch (StateInventory)
open TwoRequest (Exits)

variable {Φ : Type u} [HasTy Φ Syntax.Ty] [DecidableEq Φ] {S : RequestSignature Φ} {R : List Syntax.Ty}
  {n m : Nat}

/-- Mapped script lookup on the image returns the mapped original answer.
First-match lookup and the default ordinary divergence are preserved. -/
theorem InterpreterScript.interpret_mapState (e : Fin n ↪ Fin m) (script : List (InterpreterScript.Row Φ n))
    (f : Φ) (a : Syntax.Payload (instrSrc f)) (s : Fin n) :
    InterpreterScript.interpret (script.map (InterpreterScript.Row.mapState e)) f a (e s) =
      (InterpreterScript.interpret script f a s).mapState e :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FixedCarrier.State.interpret_mapState
    e script f a s

/-- Exact readback transports the whole observation on the original
decorated CFG. Only the old invocation inventory is needed for the proof. -/
theorem Table.observe_entry_mapState (e : Fin n ↪ Fin m) (g : Table S R)
    (raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits) (checked : g.checkNative raw = true)
    (caller : Syntax.Payload (R.get g.entry)) (prim : Syntax.Primitives Φ n) (other : Syntax.Primitives Φ m)
    (agree : ∀ f a s, other f a (e s) = (prim f a s).mapState e)
    (configs : ConfigurationEnumeration R) (stores : StateInventory n) (s : Fin n) :
    Shape.denote (withExitUB raw g.selected) (Syntax.model other (g.bindings caller)) (e s) =
      (Shape.denote (withExitUB raw g.selected) (Syntax.model prim (g.bindings caller)) s).mapState e := by
  rw [g.observe_entry raw checked caller other, g.observe_entry raw checked caller prim,
    g.observe_runFinite_mapState e caller prim other agree configs stores, g.observe_runFinite caller prim configs stores]
  exact Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FixedCarrier.State.resultBehaviour_mapState _ _

end Shape.DependentRequestTree.NativeExtraction.OpenOperands
end Silmaril.Isotope.LambdaSSA.UB.Overlay

module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.Defs
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Syntax.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Feedback.Thms

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open CFG.Dependent (internal_type)
open CFG.Dependent.Native (Typed jump diverge)
open Syntax (StatePrimitives Bindings Payload model)

universe u v

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {Γ L : List Syntax.Ty} {σ : Type v}

theorem observe_diverge (prim : StatePrimitives Φ σ) (env : Bindings Γ) (s : σ) :
    Shape.denote (.native (diverge (Φ := Φ) (Γ := Γ) (L := L))) (model prim env) s =
      WithTop.some {Outcome.diverge} := by
  let R : List Syntax.Ty := [.unit]
  let j := Feedback.internal R L 0
  let entry : Typed Φ Γ (R ++ L) := jump j (internal_type 0) .unit
  let blocks (i : Fin R.length) : Typed Φ (R.get i :: Γ) (R ++ L) := jump j (internal_type 0) .unit
  let M := (model prim env).raw
  let f := feedbackRun (.native entry) (fun i => .native (blocks i)) M
  change denote (.native ⟨nativeFeedback entry blocks, nativeFeedback_hasType entry blocks⟩) M s = _
  rw [← denote_native_feedback]
  change Feedback.close f (.entry s) = _
  have start : f (.entry s) = WithTop.some {Outcome.ret j .unit s} :=
    CFG.observe_jump prim env j (internal_type 0) .unit s
  have loopStep : f (.block 0 .unit s) = WithTop.some {Outcome.ret j .unit s} := by
    let packet : Payload (.unit : Syntax.Ty) := ⟨.unit, .unit⟩
    change denote (.native (blocks 0)) (extendModel (model prim env).raw packet.val) s = _
    exact (Syntax.denote_push prim env packet (.native (blocks 0)) s).trans
      (CFG.observe_jump prim (env.push packet) j (internal_type 0) .unit s)
  rw [close_branch (i := 0) start]
  exact close_infinite_of_singleton (f := f) (fun _ => .block 0 .unit s)
    (fun _ => ⟨0, .unit, s, rfl, loopStep⟩)

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native

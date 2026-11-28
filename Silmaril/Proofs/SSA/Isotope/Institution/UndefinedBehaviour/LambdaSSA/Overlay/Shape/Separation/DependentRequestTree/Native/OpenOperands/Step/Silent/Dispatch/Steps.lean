module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Silent.Dispatch.Defs
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Syntax.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Thms

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category (splitPayload)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration hiding Table Row
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands (Head StateTransition blockPoint)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent (evalHead)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch
open CFG.Dependent (Packet internal_type)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest (Exits)
open Syntax (Expr Payload Bindings StatePrimitives model)

universe u v

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ}
  {R Γ : List Syntax.Ty} {A B : Syntax.Ty} {σ : Type v}

private theorem dispatch_step (prim : StatePrimitives Φ σ) (env : Bindings Γ) (s : σ)
    (arg : Expr Γ (.coprod A B)) (left right : Fin R.length)
    (onLeft : Expr (A :: Γ) (R.get left)) (onRight : Expr (B :: Γ) (R.get right)) :
    denote (.native ((Row.dispatch arg left right onLeft onRight : Row S R Γ).native)) (model prim env).raw s =
      match splitPayload (arg.eval env) with
      | .inl a => (StateTransition.repeat (⟨left, onLeft.eval (env.push a)⟩ : Packet R) s).routed
      | .inr b => (StateTransition.repeat (⟨right, onRight.eval (env.push b)⟩ : Packet R) s).routed := by
  rw [Row.native, ← denote_native_lsubst]
  change (denote (.native (Syntax.Program.caseRegion arg)) (model prim env).raw s).bind _ = _
  rw [Syntax.observe_case]
  cases splitPayload (arg.eval env) with
  | inl a =>
    rw [Syntax.singleton_return_bind, Syntax.denote_push]
    exact CFG.observe_jump prim (env.push a) (Feedback.internal R Exits left) (internal_type left) onLeft s
  | inr b =>
    rw [Syntax.singleton_return_bind, Syntax.denote_push]
    exact CFG.observe_jump prim (env.push b) (Feedback.internal R Exits right) (internal_type right) onRight s

theorem feedback_step (g : Table S R) (caller : Payload (R.get g.entry))
    (prim : StatePrimitives Φ σ) (p : Packet R) (s : σ) :
    g.feedback caller prim (blockPoint p s) =
      match g.step caller p with
      | .inl q => (StateTransition.repeat q s).routed
      | .inr head => (head.execute prim s).routed := by
  obtain ⟨i, a⟩ := p
  let env := (g.visible.bindings caller).push a
  change denote (.native (g.blocks i))
    (extendModel (model prim (g.visible.bindings caller)).raw a.val) s = _
  rw [Syntax.denote_push, Table.blocks, Table.step]
  cases row : g.row i with
  | jump j arg =>
    exact CFG.observe_jump prim env (Feedback.internal R Exits j) (internal_type j) arg s
  | dispatch arg left right onLeft onRight =>
    rw [dispatch_step (S := S)]
    simp only [Row.step]
    generalize splitPayload (arg.eval ((g.visible.bindings caller).push a)) = picked
    cases picked <;> rfl
  | guarded code =>
    have visible : g.visible.row i = code := by simp [Table.visible, row]
    have old := g.visible.feedback_step caller prim ⟨i, a⟩ s
    change denote (.native (g.visible.blocks i))
      (extendModel (model prim (g.visible.bindings caller)).raw a.val) s = _ at old
    rw [Syntax.denote_push, Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Table.blocks,
      Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Table.head, visible] at old
    cases code <;> exact old

theorem native_close (g : Table S R) (caller : Payload (R.get g.entry))
    (prim : StatePrimitives Φ σ) (s : σ) :
    denote (.native g.native) (model prim (g.visible.bindings caller)).raw s =
      Feedback.close (g.feedback caller prim) (blockPoint ⟨g.entry, caller⟩ s) := by
  unfold Table.native
  rw [← denote_native_feedback]
  have start : g.feedback caller prim (.entry s) =
      WithTop.some {Outcome.ret (Feedback.internal R Exits g.entry) caller.val s} :=
    CFG.observe_jump prim (g.visible.bindings caller) (Feedback.internal R Exits g.entry)
      (internal_type g.entry) (.var 0) s
  exact close_branch start

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch

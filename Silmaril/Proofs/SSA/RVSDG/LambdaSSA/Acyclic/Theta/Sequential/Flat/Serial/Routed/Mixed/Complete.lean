module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Mixed.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize.Structured.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Wires.Reverse.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse.Recursive.Thms

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Mixed.Proofs

open Numbered.Recognize (budget loop parse_thetaBody)
open Wires.Reverse (readBody readBody_lift)
open StructuredCFG.WithNestedFeedback.Reverse.Recursive (Normal)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ] [DecidableEq τ]
variable {A E M D : τ} {rows : List (Ports (OrderedRuntime.Structured.Ty τ))}

private theorem read_consumer (n : Normal Φ M E D M E D rows) (h : n.Supported) :
    readConsumer n.toSyntax.code.1 = some ⟨rows, n⟩ := by
  unfold readConsumer
  rw [dite_eq_left rfl, dite_eq_left rfl]
  change (do
    let q ← StructuredCFG.WithNestedFeedback.Reverse.Recursive.candidate n.toSyntax.graph
    pure (⟨rows, q⟩ : Consumer Φ M E D)) = _
  rw [StructuredCFG.WithNestedFeedback.Reverse.Recursive.candidate_generated n h]
  rfl

theorem candidate_generated (s : Components Φ A E M D) (h : s.Supported) :
    candidate s.graph = some s := by
  unfold candidate Components.graph
  rw [NestedTheta.Term.toTerm_toGraph]
  let body := (Wires.liftChecked (ExplicitRuntime.Wiring.thetaBody s.producer).2.2).1
  change (do
    let (fuel, labels) ← (do
      let labels ← readBody body
      pure (budget body, [ExplicitRuntime.Reverse.Vertex.theta labels]))
    let ⟨b, k, p⟩ ← loop fuel A E M labels
    let ⟨rows, q⟩ ← readConsumer s.consumer.toSyntax.code.1
    pure (⟨b, k, p, rows, q⟩ : Components Φ A E M D)) = _
  dsimp only [body]
  rw [readBody_lift]
  have producer := parse_thetaBody s.producer h.1
  change (do
    let ⟨b, k, p⟩ ← loop (budget body) A E M
      [.theta (ExplicitRuntime.Reverse.read (ExplicitRuntime.Wiring.thetaBody s.producer).2.1)]
    let ⟨rows, q⟩ ← readConsumer s.consumer.toSyntax.code.1
    pure (⟨b, k, p, rows, q⟩ : Components Φ A E M D)) = _
  rw [producer]
  change (do
    let ⟨rows, q⟩ ← readConsumer s.consumer.toSyntax.code.1
    pure (⟨s.B, s.K, s.producer, rows, q⟩ : Components Φ A E M D)) = _
  rw [read_consumer s.consumer h.2]
  cases s
  rfl

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Mixed.Proofs

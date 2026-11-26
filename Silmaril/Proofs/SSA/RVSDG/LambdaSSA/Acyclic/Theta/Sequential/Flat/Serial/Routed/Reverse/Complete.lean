module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Reverse.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize.Structured.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Wires.Reverse.Thms

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Reverse.Proofs

open Numbered.Recognize (RightAssociated parse_thetaBody loop_associated budget)
open Wires.Reverse (readBody_lift)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A B K M C J E D : τ}
variable {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}
variable {g : Graph Φ A E M M E D sigs}

private def labels (s : Loop Φ A B K E D) : LoopLabels τ Φ :=
  let code := ExplicitRuntime.Wiring.thetaBody s
  (budget (Wires.liftChecked code.2.2).1, [.theta (ExplicitRuntime.Reverse.read code.2.1)])

private theorem scan_graph (s : Source Φ A B K M C J E D) :
    scan s.graph.toTerm = some (labels s.producer, labels s.consumer) := by
  rw [Source.graph, NestedTheta.Term.toTerm_toGraph]
  let p := (Wires.liftChecked (ExplicitRuntime.Wiring.thetaBody s.producer).2.2).1
  let q := (Wires.liftChecked (ExplicitRuntime.Wiring.thetaBody s.consumer).2.2).1
  change ((do
    let pl ← (do return (budget p, [ExplicitRuntime.Reverse.Vertex.theta (← Wires.Reverse.readBody p)]))
    let ql ← (do return (budget q, [ExplicitRuntime.Reverse.Vertex.theta (← Wires.Reverse.readBody q)]))
    pure (pl, ql)) : Option (LoopLabels τ Φ × LoopLabels τ Φ)) = _
  dsimp only [p, q]
  rw [readBody_lift, readBody_lift]
  rfl

variable [DecidableEq τ] [DecidableEq Φ]

omit [DecidableEq Φ] in
theorem candidate_graph (s : Source Φ A B K M C J E D)
    (hp : RightAssociated s.producer.body) (hq : RightAssociated s.consumer.body) :
    candidate s.graph = some ⟨B, K, C, J, s⟩ := by
  have left := parse_thetaBody s.producer hp
  have right := parse_thetaBody s.consumer hq
  rw [candidate, scan_graph]
  change (do
    let ⟨b, k, p⟩ ← Numbered.Recognize.loop (labels s.producer).1 A E M (labels s.producer).2
    let ⟨c, j, q⟩ ← Numbered.Recognize.loop (labels s.consumer).1 M E D (labels s.consumer).2
    pure (⟨b, k, c, j, ⟨p, q⟩⟩ : Components Φ A E M D)) = _
  dsimp only [labels]
  rw [left]
  change (do
    let ⟨c, j, q⟩ ← Numbered.Recognize.loop _ M E D _
    pure (⟨B, K, c, j, ⟨s.producer, q⟩⟩ : Components Φ A E M D)) = _
  rw [right]
  cases s
  rfl

theorem recover_generated (s : Source Φ A B K M C J E D)
    (hp : RightAssociated s.producer.body) (hq : RightAssociated s.consumer.body)
    (iso : NestedTheta.Graph.Isomorphic (Wires.Op Φ) g s.graph) :
    recover ⟨s.graph, iso⟩ = some ⟨s.source.region, .routed s iso⟩ := by
  rw [recover, show (⟨s.graph, iso⟩ : View g).representative = s.graph from rfl,
    candidate_graph s hp hq, Option.bind_some]
  simp [certify]

private def liftLoop (x : TwoBlock.ExplicitRuntime.Skeleton.Closed (TwoBlock.TwoExit.Pure τ)
    (ExplicitRuntime.Effect Φ) (payloadData A E D) (payloadData A E D) [WirePorts A E D]) :
    Code Φ A E D A E D [WirePorts A E D] :=
  Wires.liftChecked x.2

omit [DecidableEq τ] [DecidableEq Φ] in
private theorem same_graph {s t : Source Φ A B K M C J E D}
    (hp : ExplicitRuntime.Wiring.loop s.producer = ExplicitRuntime.Wiring.loop t.producer)
    (hq : ExplicitRuntime.Wiring.loop s.consumer = ExplicitRuntime.Wiring.loop t.consumer) :
    s.graph = t.graph := by
  have left : (Spine.loop s.producer).code = (Spine.loop t.producer).code :=
    congrArg liftLoop hp
  have right : (Spine.loop s.consumer).code = (Spine.loop t.consumer).code :=
    congrArg liftLoop hq
  simp only [Source.graph, Source.code, left, right]

theorem complete_generated (s : Source Φ A B K M C J E D)
    (iso : NestedTheta.Graph.Isomorphic (Wires.Op Φ) g s.graph) :
    (recover ⟨s.graph, iso⟩).isSome = true := by
  obtain ⟨p, hp, wp⟩ := loop_associated s.producer
  obtain ⟨q, hq, wq⟩ := loop_associated s.consumer
  let t : Source Φ A B K M C J E D := ⟨p, q⟩
  have same : t.graph = s.graph := same_graph (s := t) (t := s) wp wq
  let accept (rep : CanonicalGraph Φ A E M D)
      (map : NestedTheta.Graph.Isomorphic (Wires.Op Φ) g rep) := (recover ⟨rep, map⟩).isSome = true
  have ht : accept t.graph (same.symm ▸ iso) := by
    simp only [accept, recover_generated t hp hq, Option.isSome_some]
  exact Eq.mp (congrArg (fun rep => ∀ map, accept rep map) same)
    (fun _ => ht) iso

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Reverse.Proofs

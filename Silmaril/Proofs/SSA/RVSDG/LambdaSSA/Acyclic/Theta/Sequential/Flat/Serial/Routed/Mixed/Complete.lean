module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Mixed.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse.Recursive.Thms

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Mixed.Proofs

open StructuredCFG.WithNestedFeedback.Reverse.Recursive
  (Entry Layout scan scan_append scan_parse_generated scan_route_free weight weight_append)
open NestedTheta (Node)
open OrderedRuntime.Structured (gammaNode primitiveNode)
open Numbered.Recognize (opcodeKey instructionKey effectKey)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A X Z L E M D H : τ}
variable {ps qs : List (Ports (OrderedRuntime.Structured.Ty τ))}

private theorem scan_select (q : Code Φ M E D M E D qs) (arm : Layout τ Φ)
    (hq : scan q.1 = some arm) :
    scan (select (H := H) q).1 = some [.route H E M D, .fork [] arm] := by
  simp only [select, scan, Node.ofBase, primitiveNode, gammaNode,
    StructuredCFG.WithNestedFeedback.Reverse.Recursive.readEntry,
    StructuredCFG.WithNestedFeedback.Reverse.readOpcode, opcodeKey, instructionKey, effectKey,
    Fin.cases_zero]
  change (do
    let marker ← some (Entry.route H E M D)
    let tail ← (do
      let branch ← (do
        let left ← some []
        let right ← scan q.1
        pure (Entry.fork left right))
      let suffix ← some []
      pure (branch :: suffix))
    pure (marker :: tail)) = _
  rw [hq]
  rfl

private theorem split_mixed (labels : Layout τ Φ)
    (free : ∀ h e m d, Entry.route h e m d ∉ labels) :
    splitLayout labels = none := by
  unfold splitLayout
  split
  next consumer h e m d producer eq =>
    have member : Entry.route h e m d ∈ labels.reverse := by rw [eq]; simp
    exact (free h e m d (List.mem_reverse.mp member)).elim
  next => rfl

private theorem split_link (producer consumer : Layout τ Φ) :
    splitLayout (producer ++ [.route H E M D, .fork [] consumer]) =
      some ⟨H, E, M, D, producer, consumer⟩ := by
  simp [splitLayout, List.reverse_append]

private theorem scans [DecidableEq τ] (s : Component Φ A X Z L E D ps) (h : s.Supported) :
    ∃ labels, scan s.code.1 = some labels ∧
      ∀ fuel, weight labels < fuel → parse fuel A X Z labels = some (pack s) := by
  induction s with
  | mixed n =>
    obtain ⟨labels, scanned, parsed⟩ := scan_parse_generated n h
    refine ⟨labels, scanned, ?_⟩
    intro fuel enough
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp [parse, split_mixed labels (scan_route_free n scanned), parsed, pack,
        StructuredCFG.WithNestedFeedback.Reverse.Recursive.pack]
  | @link a x z carry e m d ps qs p q left right =>
    obtain ⟨producer, scannedProducer, parsedProducer⟩ := left h.1
    obtain ⟨consumer, scannedConsumer, parsedConsumer⟩ := right h.2
    refine ⟨producer ++ [.route carry e m d, .fork [] consumer], ?_, ?_⟩
    · simp only [Component.code, splice, scan_append, scannedProducer, scan_select _ _ scannedConsumer]
      rfl
    intro fuel enough
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [weight_append, weight] at enough
      have hp := parsedProducer fuel (by omega)
      have hq := parsedConsumer fuel (by omega)
      simp [parse, split_link, hp, hq, pack, expect]

theorem candidate_generated [DecidableEq τ] (s : Component Φ A X Z L E D ps) (h : s.Supported) :
    candidate s.graph = some s := by
  obtain ⟨labels, scanned, parsed⟩ := scans s h
  simp [candidate, Component.graph, NestedTheta.Term.toTerm_toGraph,
    scanned, decodeLayout, parsed _ (Nat.lt_succ_self _), pack]

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Mixed.Proofs

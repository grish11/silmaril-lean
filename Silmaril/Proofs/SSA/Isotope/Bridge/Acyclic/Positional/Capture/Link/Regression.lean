module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Link.Thms

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Link.Tests

open Region (packedExitType)
open LambdaSSA.Semantics (Env extend)
open LetCase.Structural.Finite (Shape StructuralContext Types)
open LetCase.Structural.Reply (Γ₀)
open LetCase.LocallyNameless (Equiv)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

set_option backward.isDefEq.respectTransparency false

private inductive Op | request | record

private abbrev bitShape : Shape := .sum .unit .unit
private abbrev Bit : Types := bitShape.ty
private abbrev captures : BoundCtx Types 1 := .snoc .nil Bit
private abbrev exits : List Types := [.unit, .unit]
private abbrev Packet := packedExitType exits

local instance : LetCase.Structural.Finite.Signature Op where
  source
    | .request => bitShape
    | .record => .pair bitShape bitShape
  target _ := bitShape

private def producer : Table Op captures exits 0 where
  types _ := .unit
  block _ := .case ⟨.op .request (.bv 1), .op .bv⟩ (.exit (i := 0) rfl) (.exit (i := 1) rfl)

private def consumer : Table Op captures exits 0 where
  types _ := Packet
  block _ := .case
    ⟨.op .record (.pair (.bv 1) (.case (.bv 0) (.inl .unit) (.inr .unit))),
      .op (.pair .bv (.case .bv (.inl .unit) (.inr .unit)))⟩
    (.exit (i := 0) rfl) (.exit (i := 1) rfl)

private def start : Operand Op captures .unit := ⟨.unit, .unit⟩
private def receive : Operand Op (captures.snoc Packet) Packet := ⟨.bv 0, .bv⟩
private def graph : Table Op captures exits 3 := table producer consumer 0 receive
private def graphEntry : Operand Op captures (graph.types 0) := entry producer consumer 0 receive 0 start
private theorem graphCheck : graph.check = true := check producer consumer rfl rfl 0 receive
private theorem input : StructuralContext captures := .snoc .nil bitShape

/-- The two ordered handoffs share a consumer row. Both label ranges and
the handoffs are visible in the written linked CFG. -/
example : (List.finRange 4).map graph.localTargets = [[1, 2], [3], [3], []] := rfl

example : Equiv false Γ₀ captures (graph.toLetCase graphCheck 0 graphEntry).1
    (bind (producer.toLetCase rfl 0 start) (continuation consumer 0 receive rfl)).1 Packet :=
  serial_equiv producer consumer rfl rfl 0 0 start receive input

example :
    let rebuilt := Reverse.CheckedTable.ofFiniteLetCase input
      (bind (producer.toLetCase rfl 0 start) (continuation consumer 0 receive rfl))
    ReplayEqv false captures.toList (graph.packedSSA 0 graphEntry)
      (rebuilt.table.packedSSA 0 rebuilt.entry) [Packet] :=
  serial_packed_replay producer consumer rfl rfl 0 0 start receive input

private abbrev low : Value Empty := .inl .unit
private abbrev high : Value Empty := .inr .unit
private def env : Env Empty := extend (fun _ => .unit) low

/-- The record request must read the older capture and the producer's
actual tag. It returns that tag, so both ordered exits stay observable. -/
private def step (f : Op) (x : Value Empty) (s : List Op) (y : Value Empty) (s' : List Op) : Prop :=
  (match f with
    | .request => x = low ∧ (y = low ∨ y = high)
    | .record => (x = .pair low low ∧ y = low) ∨ (x = .pair low high ∧ y = high)) ∧ s' = s ++ [f]

private abbrev eval := LambdaSSA.Semantics.Region.Eval step

/-- The actual packed evaluator runs one request and one record in that
order and returns the first packed tag. -/
example : eval env (graph.packedSSA 0 graphEntry) [] 0 low [.request, .record] := by
  refine .cfg (.let₁ .unit (.br .var)) (.step (next := 1) (middle := .unit) (s₁ := [.request]) (by decide) ?_
    (.step (next := 3) (middle := low) (s₁ := [.request]) (by decide) ?_
      (.step (next := 4) (by decide) ?_ (.exit (by decide)))))
  · exact .case_inl (.op .var ⟨⟨rfl, .inl rfl⟩, rfl⟩) (.let₁ .var (.br .var))
  · exact .let₁ (.let₁ (.inl .var) .var) (.br .var)
  · exact .case_inl (.op (.pair .var (.case_inl .var (.inl .unit))) ⟨.inl ⟨rfl, rfl⟩, rfl⟩)
      (.let₁ .var (.br (.inl .var)))

/-- The other reply executes the same requests once, reaches the same shared
consumer, and returns the second packed tag with the same unit payload. -/
example : eval env (graph.packedSSA 0 graphEntry) [] 0 (.inr low) [.request, .record] := by
  refine .cfg (.let₁ .unit (.br .var)) (.step (next := 2) (middle := .unit) (s₁ := [.request]) (by decide) ?_
    (.step (next := 3) (middle := .inr low) (s₁ := [.request]) (by decide) ?_
      (.step (next := 4) (by decide) ?_ (.exit (by decide)))))
  · exact .case_inr (.op .var ⟨⟨rfl, .inr rfl⟩, rfl⟩) (.let₁ .var (.br .var))
  · exact .let₁ (.let₁ (.inr (.inl .var)) .var) (.br .var)
  · exact .case_inr (.op (.pair .var (.case_inr .var (.inr .unit))) ⟨.inr ⟨rfl, rfl⟩, rfl⟩)
      (.let₁ .var (.br (.inr (.inl .var))))

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Link.Tests

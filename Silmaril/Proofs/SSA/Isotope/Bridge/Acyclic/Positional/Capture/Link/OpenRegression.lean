module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Link.Thms

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Link.Open.Tests

open Region (packedExitType)
open LambdaSSA.Semantics (Env extend)
open LetCase.Structural.Finite (Shape StructuralContext Types)
open LetCase.Structural.Reply (Γ₀)
open LetCase.LocallyNameless (Equiv)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

set_option backward.isDefEq.respectTransparency false

private inductive Op | request | advance | record

private abbrev bitShape : Shape := .sum .unit .unit
private abbrev nextShape : Shape := .pair bitShape .unit
private abbrev Bit : Types := bitShape.ty
private abbrev captures : BoundCtx Types 1 := .snoc .nil Bit
private abbrev exits : List Types := [.unit, .unit]
private abbrev Packet := packedExitType exits

local instance : LetCase.Structural.Finite.Signature Op where
  source
    | .request | .advance => bitShape
    | .record => .pair bitShape (.pair bitShape nextShape)
  target
    | .request | .record => bitShape
    | .advance => .sum nextShape .unit

private def producer : Table Op captures exits 0 where
  types _ := .unit
  block _ := .case ⟨.op .request (.bv 1), .op .bv⟩ (.exit (i := 0) rfl) (.exit (i := 1) rfl)

private def consumerWithCycle (cycle : Bool) : Table Op (captures.snoc Packet) exits 2 where
  types := ![Bit, nextShape.ty, Ty.unit]
  block := fun i => Fin.cases
    (motive := fun j => Block Op (captures.snoc Packet) ![Bit, nextShape.ty, Ty.unit] exits
      (![Bit, nextShape.ty, Ty.unit] j))
    (.case ⟨.op .advance (.bv 2), .op .bv⟩ (.local 1) (.exit (i := 1) rfl))
    (Fin.cases
      (motive := fun j : Fin 2 => Block Op (captures.snoc Packet) ![Bit, nextShape.ty, Ty.unit] exits
        (![Bit, nextShape.ty, Ty.unit] j.succ))
      (.case
        ⟨.op .record (.pair (.bv 2) (.pair (.case (.bv 1) (.inl .unit) (.inr .unit)) (.bv 0))),
          .op (.pair .bv (.pair (.case .bv (.inl .unit) (.inr .unit)) .bv))⟩
        (.exit (i := 0) rfl) (.exit (i := 1) rfl))
      (fun _ => if cycle then .jump ⟨.unit, .unit⟩ (.local 2)
        else .jump ⟨.pair (.inl .unit) .unit, .pair (.inl .unit) .unit⟩ (.local 1))) i

private abbrev consumer := consumerWithCycle false

private def producerEntry : Operand Op captures .unit := ⟨.unit, .unit⟩
private def consumerEntry : Operand Op (captures.snoc Packet) Bit := ⟨.inl .unit, .inl .unit⟩
private def linked : Table Op captures exits 5 := table producer consumer 0 consumerEntry
private def linkedEntry : Operand Op captures (linked.types 0) :=
  start producer consumer 0 consumerEntry 0 producerEntry

private theorem checkedTable : linked.check = true :=
  check producer consumer rfl rfl 0 consumerEntry

private theorem input : StructuralContext captures := .snoc .nil bitShape

/-- Both handoffs enter row three. Row four receives a pair where row three
received a bit. The unentered row five also appears in the global graph. -/
example : (List.finRange 6).map linked.localTargets = [[1, 2], [3], [3], [4], [], [4]] := rfl

/-- Changing only the unentered row to a self-loop is rejected, including
after conversion and reindexing into the linked table. -/
example : (consumerWithCycle true).check = false := rfl
example : (table producer (consumerWithCycle true) 0 consumerEntry).check = false := rfl

example : Equiv false Γ₀ captures (linked.toLetCase checkedTable 0 linkedEntry).1
    (bind (producer.toLetCase rfl 0 producerEntry) (consumer.toLetCase rfl 0 consumerEntry)).1 Packet :=
  serial_equiv producer consumer rfl rfl 0 0 producerEntry consumerEntry input

example :
    let rebuilt := Reverse.CheckedTable.ofFiniteLetCase input
      (bind (producer.toLetCase rfl 0 producerEntry) (consumer.toLetCase rfl 0 consumerEntry))
    ReplayEqv false captures.toList (linked.packedSSA 0 linkedEntry)
      (rebuilt.table.packedSSA 0 rebuilt.entry) [Packet] :=
  serial_packed_replay producer consumer rfl rfl 0 0 producerEntry consumerEntry input

private abbrev low : Value Empty := .inl .unit
private abbrev high : Value Empty := .inr .unit
private abbrev taggedRight : Value Empty := .inr low
private abbrev changed : Value Empty := .pair high .unit
private def env : Env Empty := extend (fun _ => .unit) low

/-- The successor must observe the old ambient bit, the original handoff
tag, and the new pair from advance. The selected exit depends on that tag. -/
private def step (f : Op) (x : Value Empty) (s : List Op) (y : Value Empty) (s' : List Op) : Prop :=
  (match f with
    | .request => x = low ∧ (y = low ∨ y = high)
    | .advance => x = low ∧ y = .inl changed
    | .record => (x = .pair low (.pair low changed) ∧ y = low) ∨
                 (x = .pair low (.pair high changed) ∧ y = high)) ∧ s' = s ++ [f]

private abbrev eval := LambdaSSA.Semantics.Region.Eval step

example : eval env (linked.packedSSA 0 linkedEntry) [] 0 low [.request, .advance, .record] := by
  refine .cfg (.let₁ .unit (.br .var)) (.step (next := 1) (middle := .unit) (s₁ := [.request]) (by decide) ?_
    (.step (next := 3) (middle := .pair low low) (s₁ := [.request]) (by decide) ?_
      (.step (next := 4) (middle := .pair low changed) (s₁ := [.request, .advance]) (by decide) ?_
        (.step (next := 6) (by decide) ?_ (.exit (by decide))))))
  · exact .case_inl (.op .var ⟨⟨rfl, .inl rfl⟩, rfl⟩) (.let₁ .var (.br .var))
  · exact .let₁ (.let₁ (.inl .var) (.pair .var (.inl .unit))) (.br .var)
  · exact .case_inl (.let₂ .var (.case_inl (.op .var ⟨⟨rfl, rfl⟩, rfl⟩) (.inl (.pair .var .var))))
      (.let₁ .var (.br .var))
  · exact .case_inl (.let₂ .var (.case_inl (.op (.pair .var (.pair (.case_inl .var (.inl .unit)) .var))
      ⟨.inl ⟨rfl, rfl⟩, rfl⟩) (.inl .var))) (.let₁ .var (.br (.inl .var)))

example : eval env (linked.packedSSA 0 linkedEntry) [] 0 taggedRight [.request, .advance, .record] := by
  refine .cfg (.let₁ .unit (.br .var)) (.step (next := 2) (middle := .unit) (s₁ := [.request]) (by decide) ?_
    (.step (next := 3) (middle := .pair taggedRight low) (s₁ := [.request]) (by decide) ?_
      (.step (next := 4) (middle := .pair taggedRight changed) (s₁ := [.request, .advance]) (by decide) ?_
        (.step (next := 6) (by decide) ?_ (.exit (by decide))))))
  · exact .case_inr (.op .var ⟨⟨rfl, .inr rfl⟩, rfl⟩) (.let₁ .var (.br .var))
  · exact .let₁ (.let₁ (.inr (.inl .var)) (.pair .var (.inl .unit))) (.br .var)
  · exact .case_inl (.let₂ .var (.case_inl (.op .var ⟨⟨rfl, rfl⟩, rfl⟩) (.inl (.pair .var .var))))
      (.let₁ .var (.br .var))
  · exact .case_inr (.let₂ .var (.case_inr (.op (.pair .var (.pair (.case_inr .var (.inr .unit)) .var))
      ⟨.inr ⟨rfl, rfl⟩, rfl⟩) (.inr .var))) (.let₁ .var (.br (.inr (.inl .var))))

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Link.Open.Tests

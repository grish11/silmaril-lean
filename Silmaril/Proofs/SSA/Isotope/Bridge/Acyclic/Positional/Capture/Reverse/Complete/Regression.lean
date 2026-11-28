module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse.Complete.Thms

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Reverse.CompleteTests

open LetCase.LocallyNameless (Derivation Equiv)
open LetCase.Structural.Finite (Shape StructuralContext Types)
open LetCase.Structural.Reply (Γ₀)
open LambdaSSA.Semantics (Env extend)
open Region (packedExitType)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

set_option backward.isDefEq.respectTransparency false

private inductive Op | enter | finish

private abbrev bitShape : Shape := .sum .unit .unit
private abbrev Bit : Types := bitShape.ty
private abbrev ambient : BoundCtx Types 1 := .snoc .nil Bit
private abbrev exits : List Types := [.unit, .unit]
private abbrev Result := packedExitType exits
private abbrev Term := LetCase.LocallyNameless.Tm Empty Op

local instance : LetCase.Structural.Finite.Signature Op where
  source
    | .enter => bitShape
    | .finish => .pair bitShape bitShape
  target _ := bitShape

private def term : Term 1 :=
  .let₁ (.op .enter (.bv 0))
    (.let₁ (.op .finish (.pair (.bv 1) (.bv 0)))
      (.case (.bv 0) (.inl (.bv 0)) (.inr (.inl (.bv 0)))))

private def typed : Derivation Op Γ₀ ambient term Result :=
  .let₁ (.op .bv) (.let₁ (.op (.pair .bv .bv)) (.case .bv (.inl .bv) (.inr (.inl .bv))))

private theorem inhabitedInput : StructuralContext ambient := .snoc .nil bitShape

private def graph : CheckedTable Op ambient exits :=
  .ofFiniteLetCase inhabitedInput ⟨term, typed⟩

/-- The first row computes the continuation. Two cases decode its packet,
with an explicit final empty tail. -/
example : (List.finRange 4).map graph.table.localTargets = [[1], [2], [3], []] := rfl

example : Region.HasType ambient.toList graph.toSSA exits :=
  graph.toSSA_hasType

/-- Re-emission preserves native LetCase equality at the actual source term. -/
example : Equiv false Γ₀ ambient graph.toLetCase.1 term Result :=
  CheckedTable.ofLetCase_emit false (by decide) typed

example : ReplayEqv false ambient.toList (graph.table.packedSSA 0 graph.entry)
    ((Code.ofLetCase typed).guardedSSA 0) [Result] :=
  CheckedTable.ofLetCase_packed_replay (by decide) typed

example :
    let q := reconstruct graph.table graph.checked 0 graph.entry
    ReplayEqv false ambient.toList (graph.table.packedSSA 0 graph.entry) (q.table.packedSSA 0 q.entry) [Result] :=
  reconstruct_packed_replay graph.table graph.checked 0 graph.entry

private def captured : Env Empty := extend (fun _ => .unit) (.inl .unit)

/-- The continuation must see both the older capture and the new reply.
Its two possible replies exercise the two distinct unit-payload exits. -/
private def step (f : Op) (x : Value Empty) (s : List Op) (y : Value Empty) (s' : List Op) : Prop :=
  (match f with
    | .enter => x = .inl .unit ∧ y = .inr .unit
    | .finish => x = .pair (.inl .unit) (.inr .unit) ∧ (y = .inl .unit ∨ y = .inr .unit)) ∧
  s' = s ++ [f]

private theorem enter :
    LambdaSSA.Semantics.Region.Eval step captured (graph.table.entry 0 graph.entry) [] 0 (.inr .unit) [.enter] :=
  .br (.op .var ⟨⟨rfl, rfl⟩, rfl⟩)

private theorem leftRow :
    LambdaSSA.Semantics.Region.Eval step (extend captured (.inr .unit)) (graph.table.block 0).toSSA
      [.enter] 1 (.inl .unit) [.enter, .finish] :=
  .br (.let₁ (.op (.pair .var .var) ⟨⟨rfl, Or.inl rfl⟩, rfl⟩) (.case_inl .var (.inl .var)))

private theorem rightRow :
    LambdaSSA.Semantics.Region.Eval step (extend captured (.inr .unit)) (graph.table.block 0).toSSA
      [.enter] 1 (.inr (.inl .unit)) [.enter, .finish] :=
  .br (.let₁ (.op (.pair .var .var) ⟨⟨rfl, Or.inr rfl⟩, rfl⟩) (.case_inr .var (.inr (.inl .var))))

/-- The written CFG reaches exit zero after the entry and continuation
requests, with no request in the decoder. -/
example : LambdaSSA.Semantics.Region.Eval step captured graph.toSSA [] 0 .unit [.enter, .finish] := by
  have dispatch : LambdaSSA.Semantics.Region.Eval step (extend captured (.inl .unit))
      (graph.table.block 1).toSSA [.enter, .finish] 4 .unit [.enter, .finish] :=
    .case_inl .var (.br .var)
  exact .cfg enter (.step (by decide) leftRow (.step (by decide) dispatch (.exit (by decide))))

/-- The same request order reaches exit one on the other typed reply. -/
example : LambdaSSA.Semantics.Region.Eval step captured graph.toSSA [] 1 .unit [.enter, .finish] := by
  have next : LambdaSSA.Semantics.Region.Eval step (extend captured (.inr (.inl .unit)))
      (graph.table.block 1).toSSA [.enter, .finish] 2 (.inl .unit) [.enter, .finish] :=
    .case_inr .var (.br .var)
  have dispatch : LambdaSSA.Semantics.Region.Eval step (extend captured (.inl .unit))
      (graph.table.block 2).toSSA [.enter, .finish] 5 .unit [.enter, .finish] :=
    .case_inl .var (.br .var)
  exact .cfg enter (.step (by decide) rightRow
    (.step (by decide) next (.step (by decide) dispatch (.exit (by decide)))))

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Reverse.CompleteTests

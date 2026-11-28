module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse.Categorical.Thms

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Reverse.Tests

open Isotope.Semantics (BoundEnv InstructionModel)
open LambdaSSA.Semantics (Env extend)

private inductive Op | seed | mix

private abbrev N : Ty Unit := .base ()
private abbrev PairOfExits : Ty Unit := .coprod N N
private abbrev Packet : Ty Unit := .coprod N PairOfExits
private abbrev ambient : BoundCtx (Ty Unit) 1 := .snoc .nil N
private abbrev D := Ty.denote (fun _ : Unit => Nat)

local instance : HasTy Op (Ty Unit) where
  src
    | .seed => N
    | .mix => .product N N
  trg
    | .seed => Packet
    | .mix => N

/-- The captured block computes with the shared bias before selecting exit 2.
The other branch dispatches its incoming packet to positions 0 and 1. -/
private def program : Program Op ambient [N, N, N] :=
  ⟨Packet, ⟨.op .seed (.bv 0), .op .bv⟩,
    .case ⟨.bv 0, .bv⟩
      (.local (.jump ⟨.op .mix (.pair (.bv 1) (.bv 0)), .op (.pair .bv .bv)⟩ (.exit (i := 2) rfl)))
      (.local (.case ⟨.bv 0, .bv⟩ (.exit (i := 0) rfl) (.exit (i := 1) rfl)))⟩

/-- Write the exact term directly, without starting from a source positional
table. The result tags distinguish three exits even at the same payload type. -/
private def term : Operand Op ambient (Region.packedExitType [N, N, N]) :=
  ⟨.let₁ (.op .seed (.bv 0))
      (.case (.bv 0)
        (.let₁ (.op .mix (.pair (.bv 2) (.bv 0))) (.inr (.inr (.inl (.bv 0)))))
        (.case (.bv 0) (.inl (.bv 0)) (.inr (.inl (.bv 0))))),
    .let₁ (.op .bv) (.case .bv
      (.let₁ (.op (.pair .bv .bv)) (.inr (.inr (.inl .bv))))
      (.case .bv (.inl .bv) (.inr (.inl .bv))))⟩

private def witnessed : ResultGrammar term := ⟨program, rfl⟩

example : witnessed.toTable.size + 1 = 3 := rfl

example :
    (List.finRange 3).map witnessed.toTable.table.localTargets = [[2, 1], [], []] := rfl

example : witnessed.toTable.table.check = true := witnessed.toTable.checked

private def model : InstructionModel D Op (StateM (List Op)) where
  eval
    | .seed => fun x s => (if Nat.blt x 5 then .inl (3 : Nat) else .inr (.inr (5 : Nat)), s ++ [.seed])
    | .mix => fun p s => (Nat.add (Nat.mul 10 p.1) p.2, s ++ [.mix])

private def input (bias : Nat) : BoundEnv D ambient :=
  BoundEnv.snoc (D := D) (A := N) (fun i => i.elim0) bias

example : witnessed.toTable.toLetCase.2.denote D model (fun x => nomatch x) (input 4) [] =
    (.inr (.inr (.inl (43 : Nat))), [.seed, .mix]) := by
  rw [witnessed.toTable_toLetCase]
  rfl

example : witnessed.toTable.toLetCase.2.denote D model (fun x => nomatch x) (input 7) [] =
    (.inr (.inl (5 : Nat)), [.seed]) := by
  rw [witnessed.toTable_toLetCase]
  rfl

private def result : Op → Value Nat → Option (Value Nat)
  | .seed, .atom bias =>
    some (if Nat.blt bias 5 then .inl (.atom 3) else .inr (.inr (.atom 5)))
  | .mix, .pair (.atom bias) (.atom packet) => some (.atom (10 * bias + packet))
  | _, _ => none

private def step (op : Op) (arg : Value Nat) (before : List Op) (out : Value Nat)
    (after : List Op) : Prop :=
  result op arg = some out ∧ after = before ++ [op]

private def nativeInput : Env Nat := extend (fun _ => .unit) (.atom 4)

/-- Native execution of the reified table enters at block 0, takes local
label 2, and returns at outward position 2 with the same ordered effects. -/
example : LambdaSSA.Semantics.Region.Eval step nativeInput witnessed.toTable.toSSA []
    2 (.atom 43) [.seed, .mix] := by
  let p := witnessed.toTable.table
  have entered : LambdaSSA.Semantics.Region.Eval step nativeInput
      (p.entry 0 witnessed.toTable.entry) [] 0 (.inl (.atom 3)) [.seed] :=
    .br (.op .var ⟨rfl, rfl⟩)
  have selected : LambdaSSA.Semantics.Region.Eval step (extend nativeInput (.inl (.atom 3)))
      (p.block 0).toSSA [.seed] 2 (.atom 3) [.seed] :=
    .case_inl .var (.br .var)
  have mixed : LambdaSSA.Semantics.Region.Eval step (extend nativeInput (.atom 3))
      (p.block 2).toSSA [.seed] 5 (.atom 43) [.seed, .mix] :=
    .br (.op (.pair .var .var) ⟨rfl, rfl⟩)
  exact .cfg entered (.step (by decide) selected (.step (by decide) mixed (.exit (by decide))))

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Reverse.Tests

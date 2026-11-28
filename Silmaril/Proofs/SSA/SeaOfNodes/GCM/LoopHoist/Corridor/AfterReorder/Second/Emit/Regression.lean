module

import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.Example.Defs

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.Regression

open Silmaril.MLIR.Arith (Env Var Width)
open Silmaril.MLIR.CF (Block Terminator)
open Silmaril.MLIR.Pure (i1)
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.Example (observe packet)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Example (loop first)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Example (word input)
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (TargetOp evalOp lower)

private def emitted := replay? (loop false) first 2

#guard (emitted.map fun moved => moved.prepared.origins) == some [3, 0, 2, 4]
#guard (emitted.map fun moved =>
  let cfg := moved.prepared.intermediate.2
  ((shape cfg none).bindings, (shape cfg savedHeader).bindings)) == some (3, 4)
#guard observe false == some (2, (4, 3), [[3, 2, 3], [3, 2, 7], [3, 2, 11], [3]])

private def trueFeedsHeader {saved consumer : Width} : {Γ : List Width} →
    Block TargetOp (Label saved word word [consumer]) Γ [word] → Bool
  | _, .letOp _ _ rest => trueFeedsHeader rest
  | _, .terminator (.condBr _ ⟨.header, _⟩ ⟨.exit, _⟩) => true
  | _, .terminator _ => false

#guard (emitted.map fun moved => trueFeedsHeader (moved.cfg.block .header)) == some true

-- The native lowering uses true for feedback. Exercise the same typed
-- remapper on a terminator where the false occurrence targets the header.
private def falseFeedback (test : BitVec i1.val) : Option (List Nat) := do
  let term : Terminator (Label word word word) [word] [i1, word, word, word] :=
    .condBr .here ⟨.exit, .cons (.there (.there (.there .here))) .nil⟩
      ⟨.header, .cons (.there .here) (.cons (.there (.there .here)) .nil)⟩
  let env : Env [word, i1, word, word, word] := .cons 3 (.cons test (.cons 2 (.cons 7 (.cons 11 .nil))))
  let .inl frame := (liftTerm Var.there .here term).eval env | none
  pure (packet frame)

#guard falseFeedback 0 == some [3, 2, 7]
#guard falseFeedback 1 == some [11]

#guard (emitted.map fun moved =>
  let values := input 2 10 1
  [0, 1, 2, 3, 4, 5, 6].map fun fuel => (moved.cfg.run evalOp fuel values).map (fun env => (env.get .here).toNat)) ==
  some [none, none, none, none, none, some 3, some 3]
#guard (emitted.map fun moved =>
  let values := input 2 10 1
  [3, 4, 5].all fun fuel =>
    let observeResult := fun outcome => outcome.map (fun (env : Env [word]) => (env.get .here).toNat)
    let after := observeResult (moved.cfg.run evalOp fuel values)
    after == observeResult (moved.prepared.intermediate.2.run evalOp fuel values) &&
      after == observeResult ((lower (loop false)).run evalOp fuel values)) == some true
#guard (emitted.map fun moved =>
  ((moved.cfg.run evalOp 3 (input 8 8 3)).map fun env => (env.get .here).toNat)) == some (some 9)

-- Cut zero is still too early. Stale current index three names the latch update.
#guard (emitted.map fun moved =>
  let p := moved.prepared
  let _ := targetDecEq (saved := p.intermediate.1) (carried := word) (result := word)
  Dominance.Placement.checkCut p.intermediate.2 intermediateBlocks p.consumer.operands p.consumer.uses
    ⟨none, 0⟩) == some false
#guard (emitted.map fun moved =>
  (findCandidate? 3 0 savedOrigins (moved.prepared.intermediate.2.block .header)).isNone) == some true

#guard (observe true).isNone
#guard (replay? (loop false) ⟨first.header, 2⟩ 1).isNone
#guard (replay? (loop false) first 1).isNone

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.Regression

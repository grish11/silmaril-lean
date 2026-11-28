module

import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Institution.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Example.Defs
import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Thms
import Silmaril.SSA.SeaOfNodes.Loop.Thms

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout

open Silmaril.MLIR.Arith (Width)
open Corridor.Example (Inputs word input)
open AfterReorder.Second.Example (first)
open Replay.Example (producer consumer)
open Layout.Example (loop requests)
open Loop.MLIR.CF (TargetOp evalOp lower lower_denotePart model)
open Loop.MLIR.CF.Institution (Profile observe observeCfg)
open SeaOfNodes.MLIR (Word sourceInputs)

private abbrev boundary : Profile := ⟨Inputs, word, word⟩

private def runs {Labels : List Width → Type}
    (cfg : Silmaril.MLIR.CF.Cfg TargetOp Labels Inputs [word]) : List (List (Option Nat)) :=
  [1, 0].map fun stride => [0, 3, 4, 5, 9].map fun fuel =>
    (cfg.run evalOp fuel (input 2 10 stride)).map fun env => (env.get .here).toNat

private def generated : Option (Nat × Nat × Bool × List (List (Option Nat))) := do
  let ⟨_, _, seed⟩ ← Layout.Example.seed?
  let .ok ⟨_, out⟩ := run seed 2 requests | none
  let original := lower loop
  let observed := runs out.cfg
  pure ((shape original none).bindings, (shape out.cfg none).bindings, observed == runs original, observed)

-- Two seed hoists and three physical placements change the emitted preheader.
#guard generated == some (2, 7, true,
  [[none, none, none, some 9, some 9], [none, none, none, none, none]])

private theorem originalSpins : observe (B := boundary) (lower loop) (input 2 10 0) = Part.none := by
  change (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed (lower loop)).denotePart evalOp (input 2 10 0) = Part.none
  rw [lower_denotePart, Part.eq_none_iff']
  intro defined
  have ⟨value, member⟩ := Part.dom_iff_mem.mp (show (loop.denote model _).Dom from defined)
  have returns := (loop.returns_iff_mem_denote model (sourceInputs (input 2 10 0)) value).mpr member
  exact loop.not_returns_of_backedge_invariant model (sourceInputs (input 2 10 0)) value
    (· = .cons (3 : Word word) .nil) rfl
    (fun _ same => same.symm ▸ ⟨.cons (3 : Word word) .nil, rfl, rfl⟩) returns

-- Apply the partial-observation theorem to the specific plan executed above.
private theorem generatedSpins
    {record : First Inputs word word} {two : AfterReorder.Second.Emit.Emission Inputs word word}
    {state : State Inputs two.prepared.intermediate.1 word word [two.prepared.consumer.width]}
    {out : Output Inputs two.prepared.intermediate.1 word word}
    (seed : replay loop first.header [producer, consumer] = .ok (.two record consumer two))
    (initialized : initial? (Step.fromTwo record consumer two) = some state)
    (accepted : run state 2 requests = .ok out) :
    observeCfg out.2.cfg (input 2 10 0) = Part.none :=
  (run_fromTwo_observe (B := boundary) seed initialized accepted _).trans originalSpins

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout

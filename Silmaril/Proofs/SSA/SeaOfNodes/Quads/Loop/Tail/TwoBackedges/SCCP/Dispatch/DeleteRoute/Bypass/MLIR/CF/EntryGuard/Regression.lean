module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.EntryGuard.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.EntryGuard.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.EntryGuard

open Bypass.MLIR.CF.Example (facts looping program regs width)
open Bypass.Backends.Example (stoppingFacts)
open SeaOfNodes.Loop.MLIR.CF (evalOp model)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Silmaril.MLIR.CF (Terminator)
open Blocks (Bank)

private def input (side : Bool) := Bypass.MLIR.CF.Example.entry true side
private def assumptions := facts (.constant ⟨true⟩)

private def choseSpecialized (cfg : Target regs width) (bank : Bank (regs := regs) model) :
    Option Bool :=
  match cfg.entry.eval evalOp (fun term env => Terminator.eval env term) (encodeValues bank) with
  | .inl ⟨.entry side, .nil⟩ => some side
  | _ => none

#guard
  match compile program assumptions with
  | .error _ => false
  | .ok cfg =>
    let run bank fuel := (cfg.run evalOp fuel (encodeValues bank)).map (fun env => env.get .here)
    choseSpecialized cfg (input true) == some true &&
      choseSpecialized cfg (input false) == some false &&
      run (input true) 6 == some (99 : Word width) &&
      run (input false) 7 == some (7 : Word width) &&
      (run (input true) 5).isNone && (run (input false) 6).isNone

-- The selector agrees, but the last typed word disagrees.
#guard
  match compile program assumptions with
  | .error _ => false
  | .ok cfg =>
    choseSpecialized cfg (.cons ⟨true⟩ (.cons ⟨true⟩ (.cons (8 : Word width) .nil))) == some false

#guard
  match compile looping assumptions with
  | .error _ => false
  | .ok cfg =>
    choseSpecialized cfg (input true) == some true &&
      choseSpecialized cfg (input false) == some false &&
      (cfg.run evalOp 20 (encodeValues (input true))).isNone &&
      (cfg.run evalOp 20 (encodeValues (input false))).isNone

#guard (match compile program (facts .overdefined) with | .error .bothMarked => true | _ => false)
#guard (match compile program stoppingFacts with | .error .neitherMarked => true | _ => false)

example {target : Target regs width} (success : compile program assumptions = .ok target) :
    (∃ fuel, target.run evalOp fuel (encodeValues (input false)) = some (.cons 7 .nil)) :=
  (compile_returns_iff success (input false) 7).mpr ⟨5, rfl⟩

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.EntryGuard

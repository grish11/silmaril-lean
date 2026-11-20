module

public import Silmaril.Wasm.Resource.Replay.Kernel.Defs
import Silmaril.Wasm.Verify.Kernel.Thms

@[expose] public section

namespace Silmaril.Proofs.Wasm.Resource.Replay.Kernel

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Verify
  Silmaril.Wasm.Game Silmaril.Wasm.Resource Silmaril.Wasm.Resource.Replay.Kernel
open Silmaril.Wasm.Verify.Kernel (splitK_eq runIK_eq)

private theorem decomposeK_eq (store : Store Nat) (depth : Nat) :
    decomposeK store depth = decompose? store := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
    funext code
    rw [decomposeK, decompose?, splitK_eq, ih]
    rcases splitVals code with ⟨values, _ | ⟨head, rest⟩⟩
    · rfl
    · cases head <;> first | rfl | kernel_rfl

private theorem runToK_eq (fuel : Nat) (config : Config Nat) :
    runToK fuel config = runTo? fuel config := by
  simp only [runToK, runTo?, runIK_eq, decomposeK_eq]

theorem replayFromK_eq (inst : ScalarInstance) (script : Script) (fuel : Nat) (count : Nat) :
    replayFromK inst script fuel count = replayFrom inst script fuel count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    funext index config
    simp only [replayFromK, replayFrom, runToK_eq, ih]
    rcases runTo? fuel config with _ | ⟨stopped, ctx, addr, host, args⟩ <;> rfl

end Silmaril.Proofs.Wasm.Resource.Replay.Kernel

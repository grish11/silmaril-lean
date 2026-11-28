module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.MLIR.MemRef.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.Correctness
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite

open RVSDG (Tuple)
open Quads.CFG (Predecessors)
open Silmaril.MLIR.MemRef (Buffer)
open SeaOfNodes.Memory.MLIR.MemRef (observe)

variable {args : List ValueSort} {cells sites : Nat} {preds : Predecessors sites}
variable {store : PrefixStore args} {arm : Occurrence preds → Memory.Graph args}
variable {candidate : Candidate args preds} {input : Tuple (Val cells) args} {edited : Bank args preds}

/-- Success replays exactly the checked original path at every position. -/
theorem check_eq_some_iff :
    check preds store arm candidate input = some edited ↔
      ∀ arrival, rewriteArm store (arm arrival) (candidate arrival) input = some edited[arrival.val] :=
  Proofs.check_eq_some_iff

/-- A single refused occurrence prevents the all-path edit. -/
theorem check_eq_none_iff :
    check preds store arm candidate input = none ↔
      ∃ arrival, rewriteArm store (arm arrival) (candidate arrival) input = none :=
  Proofs.check_eq_none_iff

/-- Relocating paths and certificates together relocates the checked outputs
in occurrence order. This also applies when predecessor labels repeat. -/
theorem check_reindex {target : Predecessors sites} (order : Occurrence target ≃ Occurrence preds)
    (success : check preds store arm candidate input = some edited) :
    check target store (fun arrival => arm (order arrival)) (fun arrival => candidate (order arrival)) input =
      some (Vector.ofFn fun arrival => edited[(order arrival).val]) := by
  apply check_eq_some_iff.mpr
  intro arrival
  simpa only [Vector.getElem_ofFn] using check_eq_some_iff.mp success (order arrival)

/-- At the selected operand the rewrite keeps the complete join packet
and every ordered Load readback at the checked scalar valuation. -/
theorem check_observations (success : check preds store arm candidate input = some edited)
    (arrival : Occurrence preds) (initial : Heap cells) :
    let entered := (store.table.denote input initial).2
    edited[arrival.val].denote input initial = (arm arrival).denote input entered ∧
      ∀ index, Memory.DeadStore.readAt edited[arrival.val] index input PUnit.unit initial =
        Memory.DeadStore.readAt (arm arrival) index input PUnit.unit entered :=
  rewriteArm_observations input (check_eq_some_iff.mp success arrival) initial

/-- A native continuation receives the same word and heap at its typed
entry, so explicit-edge return with that continuation is unchanged. -/
theorem check_continuation (success : check preds store arm candidate input = some edited)
    (arrival : Occurrence preds) (initial : Heap cells) (suffix : Memory.Graph (.word :: args))
    (word : Word) (final : Heap cells) :
    let before := (arm arrival).denote input (store.table.denote input initial).2
    let after := edited[arrival.val].denote input initial
    suffix.Returns (.cons after.1 input) after.2 word final ↔
      suffix.Returns (.cons before.1 input) before.2 word final := by
  simp only [(check_observations success arrival initial).1]

/-- The existing MemRef emitter for one path returns the exact selected
word and entire buffer on either side of the cut. -/
theorem check_memref_arm (success : check preds store arm candidate input = some edited)
    (arrival : Occurrence preds) (initial : Buffer cells) :
    observe edited[arrival.val] input initial = observe (store.prepend (arm arrival)) input initial :=
  Proofs.check_memref_arm success arrival initial

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite

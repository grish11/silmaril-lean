module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.MemRef.CF.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Thms
import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Proofs

open RVSDG (Tuple)
open Silmaril.MLIR.MemRef (Buffer)
open Discovery.MemRef.CF (lowerDiamond lowerDiamond_run run)
open Memory.DeadStore.Search.Selection.Readers.Repeat renaming rewrite_denote → repeatDenote

variable {args : List ValueSort} {cells : Nat}
variable {entry : Memory.Graph args}

theorem asPrefixStore_heap {store : PrefixStore args} (recognized : asPrefixStore entry = some store)
    (input : Tuple (Val cells) args) (initial : Heap cells) :
    (store.table.denote input initial).2 = (entry.denote input initial).2 := by
  unfold asPrefixStore at recognized
  split at recognized <;> try contradiction
  cases Option.some.inj recognized
  rfl

theorem rewriteResidual_denote {graph : Graph args} {result : Discovery.Result args}
    (input : Tuple (Val cells) args) (accepted : rewriteResidual graph entry input = some result)
    (guard : Bool) (initial : Heap cells) :
    result.graph.denote guard input initial = graph.denote guard input (entry.denote input initial).2 := by
  obtain ⟨store, recognized, checked⟩ := Option.bind_eq_some_iff.mp accepted
  exact (Discovery.rewrite_denote input checked guard initial).trans
    (congrArg (graph.denote guard input) (asPrefixStore_heap recognized input initial))

theorem lower_runs (graph : Graph args) (entry : Memory.Graph args) (input : Tuple (Val cells) args)
    (guard : Bool) (fuel : Nat) (initial : Buffer cells) :
    let programs := (lower graph entry input).programs
    let result := graph.denote guard input (entry.denote input initial.cell).2
    let expected := if fuel < 3 then none else some (result.1, Buffer.mk result.2)
    run programs.original programs.input guard fuel initial = expected ∧
      run programs.optimized programs.input guard fuel initial = expected := by
  cases checked : rewriteResidual graph (Entry.lowerRepeated graph entry input).entry input with
  | none => simpa only [lower, checked] using Entry.lowerRepeated_runs graph entry input guard fuel initial
  | some result =>
    simp only [lower, checked]
    refine ⟨(Entry.lowerRepeated_runs graph entry input guard fuel initial).1, ?_⟩
    have sameHeap := congrArg Prod.snd (repeatDenote entry input initial.cell)
    have same := (rewriteResidual_denote input checked guard initial.cell).trans
      (congrArg (graph.denote guard input) sameHeap)
    exact (lowerDiamond_run result.graph none input guard fuel initial).trans
      (congrArg (fun result : Word × Heap cells =>
        if fuel < 3 then none else some (result.1, Buffer.mk result.2)) same)

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Proofs

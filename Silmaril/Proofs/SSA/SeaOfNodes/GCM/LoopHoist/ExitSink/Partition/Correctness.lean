module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Suffix.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Thms
import Mathlib.Data.List.Induction

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Block Terminator)
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink (Source SavedBank)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier
  (Operation operations swapAt_typed_order)
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (TargetOp evalOp)

variable {Labels : List Width → Type} {Γ Result Input extra : List Width}
variable {saved carried result : Width}
variable {before after : Block TargetOp Labels Γ Result}
variable {source : Source Input saved carried result extra} {mask : List Bool}

private theorem pull_order {kept pending trailing : List Operation} {next : Operation}
    (layout : operations before = kept ++ pending ++ (next :: trailing))
    (pulled : pullRetained? kept.length pending.length before = some after) :
    operations after = kept ++ (next :: (pending ++ trailing)) := by
  induction pending using List.reverseRecOn generalizing before after trailing with
  | nil =>
    simp only [List.length_nil, pullRetained?, Option.some.injEq] at pulled
    subst after
    simpa only [List.append_nil, List.nil_append] using layout
  | append_singleton pending last ih =>
    simp only [List.length_append, List.length_singleton, pullRetained?] at pulled
    obtain ⟨middle, crossed, continued⟩ := Option.bind_eq_some_iff.mp pulled
    obtain ⟨prior, left, right, rest, length, beforeOrder, afterOrder⟩ := swapAt_typed_order crossed
    have unfolded : operations before = (kept ++ pending) ++ (last :: next :: trailing) := by
      simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using layout
    obtain ⟨samePrior, sameTail⟩ := List.append_inj (beforeOrder.symm.trans unfolded)
      (by simpa only [List.length_append] using length)
    obtain ⟨leftEq, sameTail⟩ := List.cons.inj sameTail
    obtain ⟨rightEq, restEq⟩ := List.cons.inj sameTail
    rw [samePrior, leftEq, rightEq, restEq] at afterOrder
    simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using ih afterOrder continued

private theorem partition_order {kept pending rest : List Operation} {mask : List Bool}
    (size : mask.length = rest.length) (layout : operations before = kept ++ pending ++ rest)
    (done : partitionFrom? kept.length pending.length mask before = some after) :
    operations after = (kept ++ selected false mask rest) ++ (pending ++ selected true mask rest) := by
  induction mask generalizing kept pending rest before after with
  | nil =>
    simp only [partitionFrom?, Option.some.injEq] at done
    subst after
    have empty : rest = [] := List.length_eq_zero_iff.mp size.symm
    simp [selected, layout, empty]
  | cons move todo ih =>
    cases rest with
    | nil => simp at size
    | cons next rest =>
      have sizes : todo.length = rest.length := by simpa only [List.length_cons, Nat.add_right_cancel_iff] using size
      cases move with
      | true =>
        have continued : partitionFrom? kept.length (pending ++ [next]).length todo before = some after := by
          simpa only [partitionFrom?, List.length_append, List.length_singleton] using done
        have remaining : operations before = kept ++ (pending ++ [next]) ++ rest := by
          simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using layout
        simpa [selected, List.append_assoc] using ih sizes remaining continued
      | false =>
        simp only [partitionFrom?] at done
        obtain ⟨middle, pulled, continued⟩ := Option.bind_eq_some_iff.mp done
        have remaining : operations middle = (kept ++ [next]) ++ pending ++ rest := by
          simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using pull_order layout pulled
        have finished : partitionFrom? (kept ++ [next]).length pending.length todo middle = some after := by
          simpa only [List.length_append, List.length_singleton] using continued
        simpa [selected, List.append_assoc] using ih sizes remaining finished

private theorem length_retained {α : Type} {mask : List Bool} {values : List α}
    (size : mask.length = values.length) :
    (selected false mask values).length = mask.count false := by
  induction mask generalizing values with
  | nil => rfl
  | cons move rest ih =>
    cases values with
    | nil => simp at size
    | cons value values =>
      have sizes : rest.length = values.length := by simpa only [List.length_cons, Nat.add_right_cancel_iff] using size
      cases move <;> simp [selected, ← ih sizes]

private theorem pull_preserves {α : Type} (observe : Block TargetOp Labels Γ Result → α)
    (swap : ∀ {cut left right}, Header.Typed.swapAt? cut left = some right → observe right = observe left)
    {kept pending : Nat} (pulled : pullRetained? kept pending before = some after) :
    observe after = observe before := by
  induction pending generalizing before with
  | zero =>
    simp only [pullRetained?, Option.some.injEq] at pulled
    rw [pulled]
  | succ n ih =>
    obtain ⟨middle, crossed, unrolled⟩ := Option.bind_eq_some_iff.mp pulled
    exact (ih unrolled).trans (swap crossed)

private theorem partition_preserves {α : Type} (observe : Block TargetOp Labels Γ Result → α)
    (swap : ∀ {cut left right}, Header.Typed.swapAt? cut left = some right → observe right = observe left)
    {kept pending : Nat} (done : partitionFrom? kept pending mask before = some after) :
    observe after = observe before := by
  induction mask generalizing kept pending before with
  | nil =>
    simp only [partitionFrom?, Option.some.injEq] at done
    rw [done]
  | cons move mask ih =>
    cases move with
    | true => exact ih done
    | false =>
      obtain ⟨middle, pulled, continued⟩ := Option.bind_eq_some_iff.mp done
      exact (ih continued).trans (pull_preserves observe swap pulled)

theorem operation_order (emission : Emission source mask) :
    operations (emission.cfg.block .header) = selected false mask (operations (source.block .header)) ∧
    operations (emission.cfg.block .exit) = selected true mask (operations (source.block .header)) := by
  have partitioned := partition_order (kept := []) (pending := []) emission.size
    (by rfl : operations (source.block .header) = [] ++ [] ++ operations (source.block .header))
    emission.partitioned
  simp only [List.nil_append] at partitioned
  obtain ⟨keptOrder, sunkOrder⟩ := ExitSink.Suffix.operation_order emission.sunk
  change operations (emission.cfg.block .header) = (operations emission.header).take (mask.count false) at keptOrder
  change operations (emission.cfg.block .exit) = (operations emission.header).drop (mask.count false) at sunkOrder
  rw [keptOrder, sunkOrder, partitioned, ← length_retained emission.size]
  simp

theorem header_packets (emission : Emission source mask) (env : Env (SavedBank saved carried extra ++ Input)) :
    (((emission.cfg.block .header).eval evalOp Header.Typed.edgePackets env).map fun (slot, frame) =>
      (slot, emission.sunk.restorePacket frame)) = (source.block .header).eval evalOp Header.Typed.edgePackets env := by
  apply (ExitSink.Suffix.header_packets emission.sunk env).trans
  exact partition_preserves (fun code => code.eval evalOp Header.Typed.edgePackets env)
    (fun swapped => Header.Typed.swapAt?_edgePackets swapped env) emission.partitioned

theorem run_eq (emission : Emission source mask) (input : Env Input) (fuel : Nat) :
    emission.cfg.run evalOp fuel input = source.run evalOp fuel input := by
  apply (ExitSink.Suffix.run_eq emission.sunk input fuel).trans
  apply Header.Typed.run_eq_of_frames (source := source) (target := withHeader source emission.header) input rfl _ fuel
  intro frame
  obtain ⟨label, packet⟩ := frame
  cases label with
  | exit => rfl
  | header =>
    let env := packet.append input
    exact partition_preserves (fun code => code.eval evalOp (fun term vals => Terminator.eval vals term) env)
      (fun swapped => Header.Typed.swapAt?_eval swapped env) emission.partitioned

open Silmaril.MLIR.CF.SwitchAssert (Cfg) in
theorem denotePart (emission : Emission source mask) (input : Env Input) :
    (Cfg.embed emission.cfg).denotePart evalOp input = (Cfg.embed source).denotePart evalOp input := by
  apply Part.ext
  intro outcome
  simp only [Cfg.mem_denotePart_iff, Cfg.embed_run, run_eq emission]

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition

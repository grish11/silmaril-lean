module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Numbered.DeadProducer.Defs
import Silmaril.SSA.SeaOfNodes.GVN.Elimination.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Prune.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Split.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Numbered.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Numbered.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Numbered.DeadProducer.Proofs

open SeaOfNodes.Diamond (Model Ty Val ValueSort dataPorts)
open SeaOfNodes.GVN (newest read_newest read_weaken weaken)
open SeaOfNodes.Pure.Deletion.Iteration (Table)
open SeaOfNodes.GVN.Elimination (plug_read)
open RVSDG (Locals Tuple Wires extend)
open RVSDG.NestedTheta (Term)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond (bodyPorts thenBase_eval)
open Diamond.Prune (HeaderProjection lowerFlow_eval)
open Join (Opcode model)
open Nested.Numbered (branchBank branchBank_agrees nextBank)
open Blocks (Bank)
open Blocks.Prune (Mask)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} {carry merge atLatch : Mask regs}
variable (m : Model.{u, v, w} Op) {p : Program src entry}
variable (checked : Split.Checked p carry merge atLatch)
variable (table : Table Op (dataPorts atLatch.kept) (packetPorts out carry))

private theorem afterMerge_eval {args results : List (Ty Data)} {past suffix : List (List (Ty Data))}
    (incoming : Wires args past (dataPorts merge.kept))
    (finish : Wires args (extend (extend past (src p.join).body.producers) table.sigs)
        (packetPorts out carry) →
      Term (Opcode Op) args (extend (extend past (src p.join).body.producers) table.sigs) suffix results)
    (fuel : Nat) (input : Tuple (Val m.value) args) (locals : Locals (Val m.value) past)
    (inspect : Tuple (Val m.value) (packetPorts out carry) → Option (Tuple (Val m.value) results))
    (agrees : ∀ packet done, (finish packet).eval (model m) fuel input done = inspect (packet.read input done)) :
    (afterMerge checked table incoming finish).eval (model m) fuel input locals =
      inspect (table.eval m (checked.mergeTransfer.eval m (incoming.read input locals))) := by
  unfold afterMerge
  erw [thenBase_eval (observe := fun bank => inspect (table.eval m bank))]
  · erw [lowerFlow_eval, plug_read]
    rfl
  · intro latch later
    erw [thenBase_eval (observe := inspect), lowerFlow_eval, plug_read]
    · rfl
    · exact agrees

variable (projected : HeaderProjection (src p.header).body carry)
variable (same : ∀ old, table.eval m old = checked.latchTransfer.eval m old)
include same

private theorem bodyWith_run {results : List (Ty Data)} {suffix : List (List (Ty Data))}
    (finish : Wires (dataPorts carry.kept) (packetScope (p := p) (merge := merge) table) (packetPorts out carry) →
      Term (Opcode Op) (dataPorts carry.kept) (packetScope (p := p) (merge := merge) table) suffix results)
    (fuel : Nat) (old : Bank (regs := regs) m)
    (inspect : Tuple (Val m.value) (packetPorts out carry) → Option (Tuple (Val m.value) results))
    (agrees : ∀ packet done, (finish packet).eval (model m) fuel (carry.project old) done =
      inspect (packet.read (carry.project old) done)) :
    (bodyWith p projected checked table finish).run (model m) fuel (carry.project old) =
      inspect (observe p carry (nextBank p m old)) := by
  let result (bank : Bank (regs := merge.kept) m) := inspect (table.eval m (checked.mergeTransfer.eval m bank))
  unfold bodyWith Term.run
  erw [thenBase_eval (observe := fun header => result (merge.project (branchBank p m header)))]
  · erw [lowerFlow_eval]
    change result (merge.project (branchBank p m (projected.headerBank m (carry.project old)))) = _
    rw [projected.header_agrees, branchBank_agrees]
    change inspect (table.eval m (checked.mergeTransfer.eval m (incoming p merge m old (p.selected m old)))) = _
    rw [same, checked.split_agrees, checked.whole.incoming_agrees]
    rfl
  · intro current later
    exact MergePrune.Numbered.afterOuter_eval p m current _ fuel (carry.project old) later result
      (fun kept locals => afterMerge_eval m checked table kept finish fuel (carry.project old) locals inspect agrees)

omit same in
private theorem weaken_read {args ports : List (Ty Data)} {past : List (List (Ty Data))}
    (wires : Wires args past ports) (input : Tuple (Val m.value) args) (locals : Locals (Val m.value) past)
    (tag : Tuple (Val m.value) [.control 2]) :
    Wires.read (wires.map (fun _ wire => weaken [.control 2] wire)) input (locals.snoc tag) =
      wires.read input locals := by
  induction wires with
  | nil => rfl
  | cons wire _ ih => exact congrArg₂ Tuple.cons (read_weaken wire m input locals tag) ih

omit same in
private theorem routePacket_eval {args : List (Ty Data)} {past : List (List (Ty Data))}
    (packet : Wires args past (packetPorts out carry)) (fuel : Nat)
    (input : Tuple (Val m.value) args) (locals : Locals (Val m.value) past) :
    (routePacket (out := out) (carry := carry) packet).eval (model m) fuel input locals =
      (match packet.read input locals with
        | .cons test (.cons _ feedback) => some (RVSDG.Theta.bodyResult (model m) test.down feedback)) := by
  cases packet
  rename_i test rest
  cases rest
  rename_i returned feedback
  let condition := SeaOfNodes.Diamond.read m test input locals
  let tag : Tuple (Val m.value) [.control 2] := (model m).run (.select ⟨.onFalse⟩) (.cons condition .nil)
  simp only [routePacket, Term.eval, RVSDG.NestedTheta.Kind.eval]
  change some (Tuple.cons (F := Val m.value) (t := .control 2)
    (SeaOfNodes.Diamond.read m (newest .head) input (locals.snoc tag))
    (Wires.read (feedback.map (fun _ wire => weaken [.control 2] wire)) input (locals.snoc tag))) = _
  rw [read_newest, weaken_read]
  change some (.cons (tag.get .head) (Wires.read feedback input locals)) =
    some (RVSDG.Theta.bodyResult (model m) condition.down (Wires.read feedback input locals))
  cases h : condition.down <;>
    simp [tag, model, Join.selected, Join.slotIndex, SeaOfNodes.Diamond.Merge.slot,
      SeaOfNodes.Diamond.Projection.ofBool, RVSDG.Theta.bodyResult, h] <;> rfl

theorem packetWith_run (fuel : Nat) (old : Bank (regs := regs) m) :
    (packetWith p projected checked table).toGraph.run (model m) fuel (carry.project old) =
      some (observe p carry (nextBank p m old)) := by
  rw [← RVSDG.NestedTheta.Graph.run_toTerm, Term.toTerm_toGraph]
  exact bodyWith_run m checked table projected same .ret fuel old some (fun _ _ => rfl)

theorem thetaWith_run (fuel : Nat) (old : Bank (regs := regs) m) :
    (thetaWith p projected checked table).run (model m) fuel (carry.project old) =
      some (MergePrune.Numbered.latchPacket p carry m (nextBank p m old)) :=
  bodyWith_run m checked table projected same _ fuel old
    (fun | .cons test (.cons _ feedback) => some (RVSDG.Theta.bodyResult (model m) test.down feedback))
    (fun packet done => routePacket_eval m packet fuel (carry.project old) done)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Numbered.DeadProducer.Proofs

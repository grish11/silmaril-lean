module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Numbered.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Split.DeadProducer.Defs

/-! # Emit the checked shortened latch inside the original numbered θ -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Numbered.DeadProducer

open SeaOfNodes.Diamond (Ty ValueSort dataPorts)
open SeaOfNodes.GVN (newest weaken)
open SeaOfNodes.Pure.Deletion.Iteration (Table)
open SeaOfNodes.GVN.Elimination (plug)
open RVSDG (Wires extend)
open RVSDG.NestedTheta (Term)
open Diamond.Prune (HeaderProjection lowerFlow)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond (bodyPorts thenBase)
open MergePrune.Numbered (arm splitSigs)
open Join (Opcode)
open Nested.Numbered (KeptResult afterOuterWith)
open Blocks.Prune (Mask)

universe u v

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} {carry merge atLatch : Mask regs}
variable {p : Program src entry} (projected : HeaderProjection (src p.header).body carry)
variable (checked : Split.Checked p carry merge atLatch)
variable (table : Table Op (dataPorts atLatch.kept) (packetPorts out carry))

/-- Substitute the actual γ result into the merge, then the merge's narrowed
output into the shortened latch, retaining both ordered producer tables. -/
def afterMerge {args results : List (Ty Data)} {past suffix : List (List (Ty Data))}
    (incoming : Wires args past (dataPorts merge.kept))
    (finish : Wires args (extend (extend past (src p.join).body.producers) table.sigs)
        (packetPorts out carry) →
      Term (Opcode Op) args (extend (extend past (src p.join).body.producers) table.sigs) suffix results) :
    Term (Opcode Op) args past ((src p.join).body.producers ++ (table.sigs ++ suffix)) results :=
  let mergeCode := plug checked.mergeTransfer.flow checked.mergeTransfer.outgoing incoming
  thenBase (lowerFlow mergeCode.1 mergeCode.2) fun atLatch =>
    let latchCode := plug table.flow table.packet atLatch
    thenBase (lowerFlow latchCode.1 latchCode.2) finish

abbrev bodySigs (suffix : List (List (Ty Data))) :=
  (src p.header).body.producers ++ (splitSigs merge ++ ((src p.join).body.producers ++ (table.sigs ++ suffix)))

abbrev packetScope :=
  extend (extend (extend (extend [] (src p.header).body.producers) (splitSigs merge))
    (src p.join).body.producers) table.sigs

variable (p)

/-- Both the packet observer and θ body use the original γ regions and
the same inlined merge and certified shortened latch. -/
def bodyWith {results : List (Ty Data)} {suffix : List (List (Ty Data))}
    (finish : Wires (dataPorts carry.kept) (packetScope (p := p) (merge := merge) table) (packetPorts out carry) →
      Term (Opcode Op) (dataPorts carry.kept) (packetScope (p := p) (merge := merge) table) suffix results) :
    Term (Opcode Op) (dataPorts carry.kept) [] (bodySigs (p := p) (merge := merge) table suffix) results :=
  thenBase (lowerFlow projected.flow projected.outgoing) fun current =>
    afterOuterWith p (arm p merge) current (fun kept => afterMerge checked table kept finish)

def packetWith := bodyWith p projected checked table .ret

/-- Control tag 0 exits and tag 1 repeats. Feedback is read simultaneously;
the stopping word lives at the checked result port of the same bank. -/
def routePacket {args : List (Ty Data)} {past : List (List (Ty Data))}
    (packet : Wires args past (packetPorts out carry)) :
    Term (Opcode Op) args past [[.control 2]] (bodyPorts carry.kept) :=
  match packet with
  | .cons test (.cons _ feedback) =>
    .bind ⟨_, .base (.simple (.select ⟨.onFalse⟩)), .cons test .nil, Fin.elim0⟩ (fun i => i.elim0)
      (.ret (.cons (newest .head) (feedback.map fun _ wire => weaken [.control 2] wire)))

def thetaWith := bodyWith p projected checked table (routePacket (out := out) (carry := carry))

def lowerWith (result : KeptResult p (mask := carry)) :=
  Nested.Numbered.lowerWith p result (thetaWith p projected checked table)

variable (cut : Split.DeadProducer.Checked checked.latchTransfer)

def packetRegion := packetWith p projected checked cut.table

def thetaBody := thetaWith p projected checked cut.table

def lower (result : KeptResult p (mask := carry)) :=
  lowerWith p projected checked cut.table result

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Numbered.DeadProducer

module

public import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.SingleUser.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.MemRef.CF.Defs

/-! Apply the single-user Store rule at one incoming memory-diamond occurrence. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.SingleUser

open SeaOfNodes.Diamond (Slot)
open Discovery.MemRef.CF (Program lowerDiamond)

variable {args : List ValueSort}

/-- Local users name an operation in this arm. Its boundary export names
the memory Phi operand at the actual Region slot. -/
inductive User where
  | load
  | store (published : Nat)
  | incoming (arrival : Slot)

/-- Count every actual use of the arm-local version, including an export
to the Region. Return in an arm is precisely that incoming use. -/
def usersOf (graph : Graph args) (arrival : Slot) (version : Nat) : List User :=
  (Memory.DeadStore.SingleUser.usersOf version (graph.arm (graph.merge.predecessor arrival))).map fun
    | .load => .load
    | .store published => .store published
    | .ret => .incoming arrival

/-- Replace the table attached to one Region occurrence. -/
def replaceArm (graph : Graph args) (arrival : Slot) (arm : Memory.Graph args) : Graph args :=
  { graph with arm := fun edge => if edge = graph.merge.predecessor arrival then arm else graph.arm edge }

/-- Check the actual predecessor's adjacent pair and sole memory use.
The arm's export is included in the native check. -/
def rewrite (graph : Graph args) (arrival : Slot) (version : Nat) : Option (Graph args) :=
  (Memory.DeadStore.SingleUser.rewrite (graph.arm (graph.merge.predecessor arrival)) version).map
    (replaceArm graph arrival)

/-- Emit the checked edited graph. The original uses the same emitter. -/
def lower (cells : Nat) (graph : Graph args) (arrival : Slot) (version : Nat) :
    Option (Program cells args) :=
  (rewrite graph arrival version).map fun edited => lowerDiamond cells edited none

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.SingleUser

module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.RuntimeRoom.Defs

/-! Coloured completion observations of the stored whole θ at canonical entries. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.RuntimeRoom

open RVSDG (Tuple)
open RVSDG.NestedTheta.Petri (Finishes)
open RVSDG.OrderedRuntime.Structured (Threaded)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {P : EntrySignature}

/-- Reach a completed marking of the stored graph from its initial marking
using the canonical typed capture and heap tuple as root colours. -/
def GeneratedProgram.Completes (p : GeneratedProgram P.args) (model : EntryModel P)
    (initial : Heap model.cells) (output : Tuple (WireVal model.cells) (Threaded wordPorts)) : Prop :=
  Finishes (thetaRuntime model.cells) p.program.graph (encodeInput initial model.input) output

/-- Observe a whole result using a finite coloured firing witness. The
domain is existence of a completed trace. -/
noncomputable def GeneratedProgram.petriObserve (p : GeneratedProgram P.args) (model : EntryModel P)
    (initial : Heap model.cells) : Part (Tuple (WireVal model.cells) (Threaded wordPorts)) where
  Dom := ∃ output, p.Completes model initial output
  get witnessed := Classical.choose witnessed

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.RuntimeRoom

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.PetriRoom

open Silmaril.Logic.Institution
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {P : EntrySignature}

/-- Use the same generated sentences with the coloured completion observer. -/
def Holds (s : RuntimeRoom.Sentence P) (model : EntryModel P) : Prop :=
  s.HoldsWith (RuntimeRoom.GeneratedProgram.petriObserve · model)

def room (P : EntrySignature) : Room.{0, 0, 0} where
  Sen := RuntimeRoom.Sentence P
  Mod := (RuntimeRoom.room P).Mod
  Sat m s := Holds s m.as

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.PetriRoom

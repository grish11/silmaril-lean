module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction.Defs

/-! Rooms of the generated three-loop sentences with canonical typed models. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction

open CategoryTheory Silmaril.Logic.Institution
open Memory.Diamond.Institution (reduct)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {P Q : EntrySignature}

/-- Each choice uses the same emitted chain syntax and its own finite witnesses. -/
inductive Backend where
  | numbered
  | memref
  | coloured

def Backend.Holds : Backend → Sentence P → EntryModel P → Prop
  | .numbered => Sentence.NumberedHolds
  | .memref => Sentence.MemRefHolds
  | .coloured => Sentence.ColouredHolds

/-- A model fixes one typed capture valuation and cell count. Equations
and termination range over initialized heaps at that valuation. -/
def room (backend : Backend) (P : EntrySignature) : Room.{0, 0, 0} where
  Sen := Sentence P
  Mod := Cat.of (Discrete (EntryModel P))
  Sat m s := backend.Holds s m.as

def modelReduct (backend : Backend) (h : P ⟶ Q) : (room backend Q).Mod ⥤ (room backend P).Mod :=
  Discrete.functor (fun m => Discrete.mk (reduct h m))

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction

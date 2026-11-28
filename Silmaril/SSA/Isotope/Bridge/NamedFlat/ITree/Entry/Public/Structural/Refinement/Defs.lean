module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Stores.Defs

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Public

open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

variable {V K : Type 1} [DecidableEq V] [DecidableEq K] {F : Type}
  {signature : PrimitiveSignature F} {source target : CFG V K F} {exits : List K} {fields : K → List V}
  {inputType rightType : PacketType} {outputs : Fin exits.length → PacketType}
  (left : StructuralEntry signature source exits fields inputType outputs)
  (right : StructuralEntry signature target exits fields rightType outputs)

def StructuralEntry.seed? (initial : V → Value Atom) : Option (Denote inputType) :=
  decodeSeed? inputType (left.evalSeed initial)

/-- Compare the two actual public starts after decoding their independent
structural seeds from the same named store. -/
def StructuralEntry.refinementFromStore? [DecidableEq F] (initial : V → Value Atom) : Option Bool := do
  let leftPacket ← left.seed? initial
  let rightPacket ← right.seed? initial
  return left.program.refinementBetween? right.program 0 leftPacket 0 rightPacket

/-- Report the existing finite-store verdict and whether it is vacuous. -/
structure CaptureRefinement where
  emptyDomain : Bool
  verdict : Option Bool
  deriving DecidableEq, Repr

/-- Run the finite-store decision on the checked structural capture
representatives. An empty joint domain is reported separately. -/
def StructuralEntry.refinementOverCaptures [DecidableEq F] : CaptureRefinement :=
  let stores := left.jointStores right
  ⟨stores.isEmpty, combineStoreVerdicts (stores.map (left.refinementFromStore? right))⟩

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Public

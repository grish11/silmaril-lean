module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Refinement.Defs

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Public

open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
open LambdaSSA (FiniteCFG)
open Silmaril.Elgot.ITree (HandledTrace Trace)

structure CaptureTraceWitness (V : Type 1) {F : Type} (signature : PrimitiveSignature F) where
  initial : V → Value Atom
  trace : Program.ObservationTrace signature

variable {V K : Type 1} [DecidableEq V] [DecidableEq K] {F : Type}
  {signature : PrimitiveSignature F} {source target : CFG V K F} {exits : List K} {fields : K → List V}
  {inputType rightType : PacketType} {outputs : Fin exits.length → PacketType}
  (left : StructuralEntry signature source exits fields inputType outputs)
  (right : StructuralEntry signature target exits fields rightType outputs)

/-- The unrestricted shared reply policy witnesses a difference on the
original named runners at the returned representative. -/
def CaptureTraceWitness.Refutes (witness : CaptureTraceWitness V signature) : Prop :=
  witness.initial ∈ left.jointStores right ∧
    HandledTrace signature.traceModel.step ()
      (LiveOut.observeRaw signature.primitive exits fields source witness.initial) witness.trace ∧
    ¬ HandledTrace signature.traceModel.step ()
      (LiveOut.observeRaw signature.primitive exits fields target witness.initial) witness.trace

def StructuralEntry.explainRefinementFromStore? [DecidableEq F]
    (initial : V → Value Atom) : Option (Program.ObservationTrace signature) :=
  (left.seed? initial).bind fun leftPacket => (right.seed? initial).bind fun rightPacket =>
    (left.program.explainRefinementBetween? right.program 0 leftPacket 0 rightPacket).map
      (Trace.map FiniteCFG.packedTreeOutput)

/-- Find the first rejected representative with the existing decision,
then run the packed trace extractor at that store. -/
def StructuralEntry.explainRefinementOverCaptures? [DecidableEq F] : Option (CaptureTraceWitness V signature) :=
  ((left.jointStores right).find? fun initial => left.refinementFromStore? right initial == some false).bind
    fun initial => (left.explainRefinementFromStore? right initial).map (CaptureTraceWitness.mk initial)

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Public

module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.Defs

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Public

open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
open LambdaSSA (FiniteCFG)

variable {V K : Type 1} [DecidableEq V] [DecidableEq K] {F : Type}
  {signature : PrimitiveSignature F} {a b : Nat} {inputs : Fin a → PacketType}
  {outputs : Fin b → PacketType} {program : Program signature inputs outputs} {input : Fin a}

/-- The actual named table after live-out attachment has a checked
packet-closed readback and the same erased table as the checked public entry.
The registers and external label names themselves can differ. -/
structure Readback (entry : Program.PackedEntry program input)
    (source : CFG V K F) (exits : List K) (fields : K → List V) where
  captureCount : Nat
  captures : Fin captureCount → V
  exitCount : exits.length = program.exits.length
  closed : RoundTrip.PacketClosed (LiveOut.attach fields source)
  blocks : Nat
  blockCount : (LiveOut.attach fields source).blocks.length = blocks
  flat : FiniteCFG F blocks exits.length captureCount
  accepted : NamedFlat.elaborateAt (LiveOut.attach fields source) exits captures blocks blockCount = some flat
  agrees : flat.erase = entry.target.erase

/-- Reuse a successful reverse lowering's exact readback. The additional
check relates its positional table to the chosen finite public dispatcher. -/
def Readback.ofLowered {κ : Type 1}
    {P : LambdaSSA.Semantics.Interaction.Typed.Ordered.FlatInstitution.Signature.{0,0} κ}
    {I : Entry.Interface κ V K} {fields : K → List (V × Ty κ)} {blocks : Nat}
    {code : FiniteCFG P.Instr blocks I.exits.length I.slots}
    {signature : PrimitiveSignature P.Instr} {program : Program signature inputs outputs}
    (entry : Program.PackedEntry program input) (lowered : Entry.Reverse.Lowered I fields code)
    (exitCount : I.exits.length = program.exits.length) (sameCode : code.erase = entry.target.erase) :
    Readback entry lowered.source I.exits (fun k => (fields k).map Prod.fst) :=
  ⟨I.slots, I.names, exitCount, lowered.closed, blocks, lowered.count, code, lowered.readback, sameCode⟩

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Public

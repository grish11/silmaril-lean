module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.Thms

/-! # Exact readback certificates for an emitted reverse table -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse

open Silmaril.SSA.LambdaRTL (CFG)
open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics.Interaction.Typed.Ordered

universe u v

variable {κ V K : Type (u + 1)} [DecidableEq V] [DecidableEq K]
  {P : FlatInstitution.Signature.{u, v} κ} {I : Interface κ V K}
  {fields : K → List (V × Ty κ)} {blocks : Nat} {code : FiniteCFG P.Instr blocks I.exits.length I.slots}

/-- Exact scoped readback suffices to construct the certificate for this
mutable table. Its block closure follows from the elaboration itself. -/
def Lowered.ofReadback (source : CFG V K P.Instr)
    (count : (withLiveOut fields source).blocks.length = blocks)
    (readback : elaborateAt (withLiveOut fields source) I.exits I.names blocks count = some code) :
    Lowered I fields code :=
  ⟨source, elaborateAt_packetClosed _ _ _ count readback, count, readback⟩

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse

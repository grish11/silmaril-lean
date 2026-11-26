module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Materialize.Outline.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.PacketLocal.Flat.Defs

/-! # Admit an outlined arm with the existing inferred-capture path -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.Materialize.Outline

open PacketLocal
open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics.Interaction.Typed.Ordered

universe u v
variable {κ K : Type (u + 1)} [DecidableEq K]
  {n blocks : Nat} {P : FlatInstitution.Signature.{u, v} κ}
  {context : BoundCtx (Ty κ) n} {exits : List K} {external : Fin exits.length → Ty κ}
  {fields : K → List (Register × Ty κ)}
  {g : FiniteCFG P.Instr blocks exits.length n}

abbrev Compiled (s : Selection g) :=
  let code := Materialize.graph (graph s)
  CompiledFlat (context := context) (external := external) (fields := fields)
    (Capture.Carry.graphList code (Capture.Carry.inferSlots code))

/-- The supplied label table includes a name for the appended block.
The register plan covers both its packet decoder and operand binding.
The existing exact readback still checks their use at the chosen live-outs. -/
def compile? [DecidableEq κ] [DecidableEq P.Instr] (s : Selection g)
    (R : Fin blocks → Ty κ) (left : Ty κ)
    (registers : Registers Register) (labels : Fin (blocks + 1) → K) :
    Option (Compiled (context := context) (external := external) (fields := fields) s) :=
  compileFlatInferred? (Materialize.graph (graph s)) (packets R s.selected left) registers labels

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.Materialize.Outline

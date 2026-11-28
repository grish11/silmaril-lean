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

abbrev Checked (s : Selection g) :=
  let code := Materialize.graph (graph s)
  CheckedFlat (context := context) (external := external) (fields := fields)
    (Capture.Carry.graphList code (Capture.Carry.inferSlots code))

/-- Outline and materialize a selected arm, then check named readback and
typed reversion. The register plan and appended block label are supplied. -/
def compileChecked? [DecidableEq κ] [DecidableEq P.Instr] (s : Selection g)
    (R : Fin blocks → Ty κ) (active : Ty κ)
    (registers : Registers Register) (labels : Fin (blocks + 1) → K) :
    Option (Checked (context := context) (external := external) (fields := fields) s) :=
  compileCheckedInferred? (Materialize.graph (graph s)) (packets R s.selected active) registers labels

abbrev Compiled (s : Selection g) :=
  let code := Materialize.graph (graph s)
  CompiledFlat (context := context) (external := external) (fields := fields)
    (Capture.Carry.graphList code (Capture.Carry.inferSlots code))

/-- The supplied label table includes a name for the appended block.
The register plan covers both its packet decoder and operand binding.
The existing exact readback still checks their use at the chosen live-outs. -/
def compile? [DecidableEq κ] [DecidableEq P.Instr] (s : Selection g)
    (R : Fin blocks → Ty κ) (active : Ty κ)
    (registers : Registers Register) (labels : Fin (blocks + 1) → K) :
    Option (Compiled (context := context) (external := external) (fields := fields) s) :=
  (compileChecked? s R active registers labels).bind CheckedFlat.checkRank

/-- Run one named emission after both outlines, with names for both appended
blocks and an exact checker for the resulting register plan. -/
def compileBoth? [DecidableEq κ] [DecidableEq P.Instr] (s : TwoArms g)
    (R : Fin blocks → Ty κ) (firstActive secondActive : Ty κ)
    (registers : Registers Register) (labels : Fin (blocks + 1 + 1) → K) :
    Option (Compiled (context := context) (external := external) (fields := fields) s.second) :=
  compile? s.second (packets R s.first.selected firstActive) secondActive registers labels

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.Materialize.Outline

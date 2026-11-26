module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Materialize.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.PacketLocal.Flat.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Capture.Carry.Infer.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Materialize.Admission

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.Materialize

open PacketLocal
open LambdaSSA (FiniteCFG Region)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (region)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Isotope.Semantics (encodeValue)

universe u v
variable {κ K : Type (u + 1)} [DecidableEq K]
  {n blocks : Nat} {P : FlatInstitution.Signature.{u, v} κ}
  {context : BoundCtx (Ty κ) n} {exits : List K} {external : Fin exits.length → Ty κ}
  {fields : K → List (Register × Ty κ)}
  {g : FiniteCFG P.Instr blocks exits.length n} {R : Fin blocks → Ty κ}
  [AtomValues κ] {Events : Type u → Type u}

local notation "ports" => numberedInterface context exits external
local notation "exitTypes" => Interface.external (LiveOut.exitInterface ports fields)
local notation "A" => Region.packedInputType context.toList
local notation "C" => AtomValues.carrier (κ := κ)

/-- Admission compares the original typed table to the named runner, including
the same caller input, ordered exits, and selected mutable-store reads. -/
theorem packed_observe (typed : g.HasType context R exitTypes)
    (M : Model (κ := κ) Events P.Instr)
    (c : CompiledFlat (context := context) (external := external) (fields := fields)
      (Capture.Carry.graphList (graph g) (Capture.Carry.inferSlots (graph g))))
    (x : Record.Input context) (ambient : Env (Sigma C)) :
    region M.raw (extend ambient (encodeValue C A x)) (Program.ofCFGEntry typed).code =
      LiveOut.observe M ports fields c.lowered.source x :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.Materialize.packed_observe typed M c x ambient

/-- The original typed table and the actual packed reversion agree at
every input of the original public interface. -/
theorem packed_roundTrip (typed : g.HasType context R exitTypes)
    (M : Model (κ := κ) Events P.Instr)
    (c : CompiledFlat (context := context) (external := external) (fields := fields)
      (Capture.Carry.graphList (graph g) (Capture.Carry.inferSlots (graph g))))
    (x : Record.Input context) (ambient : Env (Sigma C)) :
    region M.raw (extend ambient (encodeValue C A x)) (Program.ofCFGEntry typed).code =
      region M.raw (extend ambient (encodeValue C A x)) c.admission.program.code :=
  (packed_observe typed M c x ambient).trans (c.admission.packed_tree M x ambient).symm

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.Materialize

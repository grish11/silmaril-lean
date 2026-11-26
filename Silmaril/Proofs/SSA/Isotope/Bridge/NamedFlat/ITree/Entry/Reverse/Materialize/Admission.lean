module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Materialize.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.PacketLocal.Flat.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Capture.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Capture.Carry.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.Materialize

open Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat
open Silmaril.Isotope.Bridge.NamedFlat.Entry
open Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse
open Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.PacketLocal
open Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.Materialize
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

theorem packed_observe (typed : g.HasType context R exitTypes)
    (M : Model (κ := κ) Events P.Instr)
    (c : CompiledFlat (context := context) (external := external) (fields := fields)
      (Capture.Carry.graphList (graph g) (Capture.Carry.inferSlots (graph g))))
    (x : Record.Input context) (ambient : Env (Sigma C)) :
    region M.raw (extend ambient (encodeValue C A x)) (Program.ofCFGEntry typed).code =
      LiveOut.observe M ports fields c.lowered.source x := by
  let env := inputEnv context x
  let carried := Capture.Carry.graphList (graph g) (Capture.Carry.inferSlots (graph g))
  let admittedType := Capture.Carry.graphList_hasType (graph_hasType typed) (Capture.Carry.inferSlots (graph g))
  have original :
      region M.raw (extend ambient (encodeValue C A x)) (Program.ofCFGEntry typed).code =
        (region M.raw env g.erase >>= fun p => pure (FiniteCFG.packedTreeOutput p)) := by
    rw [← inputEnv_packet]
    exact Capture.packed_context_tree M.raw typed ambient env
  have compiled :
      region M.raw (extend ambient (encodeValue C A x)) (Program.ofCFGEntry admittedType).code =
        (region M.raw env carried.erase >>= fun p => pure (FiniteCFG.packedTreeOutput p)) := by
    rw [← inputEnv_packet]
    exact Capture.packed_context_tree M.raw admittedType ambient env
  have same := (Capture.Carry.graphList_tree M.raw (graph g) (Capture.Carry.inferSlots (graph g)) env).trans
    (graph_tree M.raw g env)
  rw [same] at compiled
  exact original.trans (compiled.symm.trans (c.lowered.packed_observe M admittedType x ambient))

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.Materialize

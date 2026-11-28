module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Deletion.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Deletion.Correctness
import Silmaril.SSA.SeaOfNodes.Loop.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Deletion

open Diamond (Dataflow Model Signature Ty Val ValueSort dataPorts sortValue)
open RVSDG (Locals Tuple Wires)

universe u v w

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {args : List (Ty Data)} {past sigs : List (List (Ty Data))}
variable {out removed : ValueSort Data} {flow : Dataflow Op args past sigs}

/-- Routing all occurrences of an ordered packet preserves its values. -/
theorem Route.wires_read {target : List (List (Ty Data))} {route : Route args past target}
    (m : Model.{u,v,w} Op) (entry : Tuple (Val m.value) args)
    {old : Locals (Val m.value) past} {new : Locals (Val m.value) target}
    (agree : route.Agrees m entry old new) {ports : List (Ty Data)}
    (wires : Wires args past ports) {mapped : Wires args target ports}
    (routed : route.wires? wires = some mapped) :
    wires.read entry old = mapped.read entry new :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Deletion.wires_read m entry agree wires routed

/-- Successful routing preserves every routed read from the original table. -/
theorem erase_sound (candidate : Producer flow removed) (m : Model.{u,v,w} Op)
    (entry : Tuple (Val m.value) args) (locals : Locals (Val m.value) past)
    {erasure : Erasure Op args past sigs} (accepted : erase? candidate = some erasure) :
    Route.Agrees erasure.route m entry (flow.eval m entry locals) (erasure.flow.eval m entry locals) :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Deletion.erase_agrees m entry candidate locals accepted

variable {inputs carried : List (ValueSort Data)} {entrySigs headerSigs : List (List (Ty Data))}
variable {loop : Loop.Graph Op inputs carried entrySigs headerSigs out}
variable {candidate : Producer loop.header removed}
variable {rewritten : DeletedLoop Op inputs carried entrySigs out}
variable (accepted : delete? loop candidate = some rewritten)
include accepted

/-- An accepted loop has exactly one fewer header binding. -/
theorem delete_count :
    rewritten.headerSigs.length + 1 = headerSigs.length :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Deletion.delete_size accepted

variable (m : Model.{u,v,w} Op) (input : Tuple (Val m.value) (dataPorts inputs))

/-- The original entry column establishes the same first latch tuple. -/
theorem delete_initial :
    rewritten.graph.initial m input = loop.initial m input :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Deletion.delete_initial m accepted input

/-- Deletion preserves the full activation transition at every old tuple.
In particular, it preserves the entire simultaneous backedge latch tuple. -/
theorem delete_step (old : Tuple (Val m.value) (dataPorts carried)) :
    rewritten.graph.step m input old = loop.step m input old :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Deletion.delete_step m accepted input old

/-- Every bounded evaluation agrees, including exhaustion of the budget. -/
theorem delete_evalBackedges (budget : Nat) :
    rewritten.graph.evalBackedges m budget input = loop.evalBackedges m budget input :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Deletion.delete_eval m accepted input budget

/-- The rewritten graph has the same finite return relation. -/
theorem delete_returns (value : sortValue m.value out) :
    rewritten.graph.Returns m input value ↔ loop.Returns m input value := by
  simp only [Loop.Graph.returns_iff_evalBackedges, delete_evalBackedges accepted m input]

end Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Deletion

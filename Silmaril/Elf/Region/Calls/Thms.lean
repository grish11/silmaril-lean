module

public import Silmaril.Elf.Region.Calls.Defs
public import Silmaril.Semantics.Function.Thms
import Silmaril.Proofs.Elf.Region.FunctionCalls

@[expose] public section
namespace Silmaril.Elf.Region.Calls
open Silmaril.Semantics.Function
open Silmaril.Machine.Region (BinaryObject)

theorem readable_rows (source : BinaryObject) (plan : Plan) :
    ReadableRows source plan (rows (extract source plan)) := Proofs.readable_rows source plan

theorem decomposition_problem (source : BinaryObject) (plan : Plan) :
    DecomposeProblem (ReadableRows source plan) source (asModel source (extract source plan)) :=
  fun name body candidate => readable_rows source plan name body candidate.2

theorem finding_evidence {source : BinaryObject} {plan : Plan} {row : Row} {finding : Finding}
    (member : row ∈ extract source plan) (available : row.available = true) (found : finding ∈ row.findings) :
    FindingAt source plan finding := Proofs.finding_evidence member available found

theorem mem_directArcs {inventory : Inventory} {source : Nat} {dest : Node signature} :
    (source, dest) ∈ directArcs inventory ↔ DirectEdge inventory (.localFn source) dest :=
  Proofs.mem_directArcs

theorem reach_sound {inventory : Inventory} {entry rounds : Nat} {dest : Node signature}
    (mem : dest ∈ reach inventory entry rounds) :
    Reachable (directGraph (analysis inventory).may) (.localFn entry) dest :=
  Proofs.iterate_sound (fun _ h => (List.mem_singleton.mp h).symm ▸ Relation.ReflTransGen.refl)
    (fun _ _ path edge => Relation.ReflTransGen.tail path edge) mem

theorem nonemptyReach_sound {inventory : Inventory} {entry rounds : Nat} {dest : Node signature}
    (mem : dest ∈ nonemptyReach inventory entry rounds) :
    CallPath (directGraph (analysis inventory).may) (.localFn entry) dest :=
  Proofs.iterate_sound (fun _ h => Relation.TransGen.single (Proofs.successor_iff.mp h))
    (fun _ _ path edge => Relation.TransGen.tail path edge) mem

theorem reach_exact {inventory : Inventory} {entry rounds : Nat}
    (fixed : expand inventory (reach inventory entry rounds) = reach inventory entry rounds) :
    ReachProblem (directGraph (analysis inventory).may) (.localFn entry)
      {dest | dest ∈ reach inventory entry rounds} :=
  reach_problem_of_certificate ⟨Proofs.root_mem inventory entry rounds,
    fun {_ _} h edge => Proofs.step_closed fixed h edge, fun {_} mem => reach_sound mem⟩

theorem checked_reach {inventory : Inventory} {entry rounds : Nat}
    (done : stable inventory (reach inventory entry rounds) = true) :
    ReachProblem (directGraph (analysis inventory).may) (.localFn entry)
      {dest | dest ∈ (query inventory entry rounds).knownVertices} :=
  reach_exact (Proofs.fixed_of_stable done)

theorem checked_nonempty {inventory : Inventory} {entry rounds : Nat}
    (done : stable inventory (nonemptyReach inventory entry rounds) = true) :
    PathProblem (directGraph (analysis inventory).may) (.localFn entry)
      {dest | dest ∈ nonemptyReach inventory entry rounds} :=
  fun _ => ⟨nonemptyReach_sound, Proofs.nonempty_complete (Proofs.fixed_of_stable done)⟩

theorem frontier_sound {inventory : Inventory} {entry rounds : Nat} {leaf : Stub}
    (mem : leaf ∈ (query inventory entry rounds).knownFrontier) :
    leaf ∈ foreignFrontier (directGraph (analysis inventory).may) entry :=
  Proofs.path_iff_reach.mpr (reach_sound (Proofs.mem_frontier.mp mem))

theorem frontier_exact {inventory : Inventory} {entry rounds : Nat}
    (done : stable inventory (reach inventory entry rounds) = true) :
    FrontierProblem (directGraph (analysis inventory).may) entry
      {leaf | leaf ∈ (query inventory entry rounds).knownFrontier} := by
  ext leaf
  exact Proofs.mem_frontier.trans ((checked_reach done _).trans Proofs.path_iff_reach.symm)

theorem reachable_arcs_exact {inventory : Inventory} {entry rounds caller : Nat} {dest : Node signature}
    (done : stable inventory (reach inventory entry rounds) = true) :
    (caller, dest) ∈ (query inventory entry rounds).knownCalls ↔
      DirectEdge inventory (.localFn caller) dest ∧
        Reachable (directGraph (analysis inventory).may) (.localFn entry) (.localFn caller) :=
  Proofs.mem_knownCalls.trans (and_congr_right fun _ => checked_reach done _)

theorem bounded_embed (inventory : Inventory) (targets : CallSite signature → Option (Set (Node signature))) :
    MayCover (boundedAnalysis inventory targets).may (analysis inventory).may :=
  Proofs.bounded_embed inventory targets

theorem bounded_cover {inventory : Inventory} {targets : CallSite signature → Option (Set (Node signature))}
    {actual : Calls signature} (top : CallGraphProblem actual (analysis inventory))
    (narrow : ∀ edge, actual edge → edge.dispatch = .indirect → admits (targets edge.origin) edge.callee) :
    CallGraphProblem actual (boundedAnalysis inventory targets) := Proofs.bounded_cover top narrow

end Silmaril.Elf.Region.Calls

module

public import Silmaril.Elf.Region.Calls.General.Defs
public import Silmaril.Elf.Region.Calls.Thms
import Silmaril.Proofs.Elf.Region.GeneralCalls

@[expose] public section
namespace Silmaril.Elf.Region.Calls
open Silmaril.Semantics.Function

theorem direct_embeds {inventory : Inventory} {targets : Targets} {source dest : Node signature}
    (edge : DirectEdge inventory source dest) : (arcGraph (knownArcs inventory targets)).edge source dest :=
  Proofs.direct_embeds edge

theorem known_edge {inventory : Inventory} {targets : Targets} {source dest : Node signature}
    (edge : (arcGraph (knownArcs inventory targets)).edge source dest) :
    (mayGraph (declaredAnalysis inventory targets).may).edge source dest := Proofs.known_edge edge

theorem finite_reach_sound {arcs : List (Nat × Node signature)} {entry rounds : Nat} {dest : Node signature}
    (mem : dest ∈ finiteReach arcs entry rounds) : Reachable (arcGraph arcs) (.localFn entry) dest :=
  Proofs.finite_reach_sound mem

theorem finite_reach_exact {arcs : List (Nat × Node signature)} {entry rounds : Nat}
    (done : stableArcs arcs (finiteReach arcs entry rounds) = true) :
    ReachProblem (arcGraph arcs) (.localFn entry) {dest | dest ∈ finiteReach arcs entry rounds} :=
  Proofs.finite_reach_exact done

theorem finite_path_sound {arcs : List (Nat × Node signature)} {entry rounds : Nat} {dest : Node signature}
    (mem : dest ∈ finitePaths arcs entry rounds) : CallPath (arcGraph arcs) (.localFn entry) dest :=
  Proofs.finite_path_sound mem

theorem finite_paths_exact {arcs : List (Nat × Node signature)} {entry rounds : Nat}
    (done : stableArcs arcs (finitePaths arcs entry rounds) = true) :
    PathProblem (arcGraph arcs) (.localFn entry) {dest | dest ∈ finitePaths arcs entry rounds} :=
  fun _ => ⟨finite_path_sound, Proofs.finite_path_complete done⟩

theorem closed_reach {inventory : Inventory} {targets : Targets} {entry rounds : Nat}
    (closed : (queryGeneral inventory targets entry rounds).issues = []) :
    ReachProblem (mayGraph (declaredAnalysis inventory targets).may) (.localFn entry)
      {dest | dest ∈ (queryGeneral inventory targets entry rounds).knownVertices} := Proofs.closed_reach closed

theorem closed_paths {inventory : Inventory} {targets : Targets} {entry rounds pathRounds : Nat}
    (closed : (queryGeneral inventory targets entry rounds).issues = [])
    (done : stableArcs (knownArcs inventory targets) (finitePaths (knownArcs inventory targets) entry pathRounds) = true) :
    PathProblem (mayGraph (declaredAnalysis inventory targets).may) (.localFn entry)
      {dest | dest ∈ finitePaths (knownArcs inventory targets) entry pathRounds} := Proofs.closed_paths closed done

theorem closed_frontier {inventory : Inventory} {targets : Targets} {entry rounds : Nat}
    (closed : (queryGeneral inventory targets entry rounds).issues = []) :
    FrontierProblem (mayGraph (declaredAnalysis inventory targets).may) entry
      {leaf | leaf ∈ (queryGeneral inventory targets entry rounds).knownFrontier} := Proofs.closed_frontier closed

theorem known_frontier_sound {inventory : Inventory} {targets : Targets} {entry rounds : Nat} {leaf : Stub}
    (mem : leaf ∈ (queryGeneral inventory targets entry rounds).knownFrontier) :
    leaf ∈ foreignFrontier (mayGraph (declaredAnalysis inventory targets).may) entry :=
  Proofs.known_frontier_sound mem

theorem direct_path_embeds {inventory : Inventory} {targets : Targets} {entry : Nat} {dest : Node signature}
    (path : CallPath (directGraph (analysis inventory).may) (.localFn entry) dest) :
    CallPath (arcGraph (knownArcs inventory targets)) (.localFn entry) dest :=
  Relation.TransGen.mono (fun _ _ edge => direct_embeds edge) _ _ path

theorem frontier_bound_sound {inventory : Inventory} {targets : Targets} {entry rounds : Nat} {leaf : Stub}
    (path : leaf ∈ foreignFrontier (mayGraph (declaredAnalysis inventory targets).may) entry) :
    admits (queryGeneral inventory targets entry rounds).frontierBound leaf := Proofs.frontier_bound path

theorem frontier_bound_of_cover {inventory : Inventory} {targets : Targets} {entry rounds : Nat} {leaf : Stub}
    {actual : Calls signature} (cover : CallGraphProblem actual (declaredAnalysis inventory targets))
    (path : leaf ∈ foreignFrontier (mayGraph actual) entry) :
    admits (queryGeneral inventory targets entry rounds).frontierBound leaf :=
  frontier_bound_sound (path_mono cover (fun _ _ => trivial) path)

theorem declared_mono {inventory : Inventory} {old new : Targets}
    (widen : ∀ site dest, admits (targetSet old site) dest → admits (targetSet new site) dest) :
    MayCover (declaredAnalysis inventory old).may (declaredAnalysis inventory new).may := Proofs.declared_mono widen

end Silmaril.Elf.Region.Calls

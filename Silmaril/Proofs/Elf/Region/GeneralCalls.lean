module

public import Silmaril.Elf.Region.Calls.General.Defs
public import Silmaril.Semantics.Function.Thms
import Silmaril.Proofs.Elf.Region.FunctionCalls

public section
namespace Silmaril.Elf.Region.Calls.Proofs
open Silmaril.Semantics.Function

theorem arc_mem {arcs : List (Nat × Node signature)} {caller : Nat} {dest : Node signature} :
    (arcGraph arcs).edge (.localFn caller) dest ↔ (caller, dest) ∈ arcs := by
  change dest ∈ arcSuccessors arcs (.localFn caller) ↔ _
  rw [arcSuccessors, List.mem_filterMap]
  refine ⟨?_, fun mem => ⟨(caller, dest), mem, by simp⟩⟩
  rintro ⟨⟨origin, callee⟩, mem, hit⟩
  by_cases eq : origin = caller
  · simp [eq] at hit
    subst origin; subst callee
    exact mem
  · simp [eq] at hit

theorem mem_indirectArcs {inventory : Inventory} {targets : Targets} {caller : Nat} {dest : Node signature} :
    (caller, dest) ∈ indirectArcs inventory targets ↔
      ∃ site, site.caller = caller ∧ IndirectAt inventory site ∧ dest ∈ (targets site).getD [] := by
  constructor
  · intro mem
    obtain ⟨row, inInventory, found⟩ := List.mem_flatMap.mp mem
    obtain ⟨finding, inRow, hit⟩ := List.mem_flatMap.mp found
    cases finding with
    | direct | gap => cases hit
    | indirect site =>
      obtain ⟨node, listed, eq⟩ := List.mem_map.mp hit
      cases eq
      exact ⟨site, rfl, ⟨row, inInventory, inRow⟩, listed⟩
  · rintro ⟨site, rfl, ⟨row, inInventory, inRow⟩, listed⟩
    exact List.mem_flatMap.mpr ⟨row, inInventory,
      List.mem_flatMap.mpr ⟨.indirect site, inRow, List.mem_map.mpr ⟨dest, listed, rfl⟩⟩⟩

theorem listed_admitted {targets : Targets} {site : CallSite signature} {dest : Node signature}
    (listed : dest ∈ (targets site).getD []) : admits (targetSet targets site) dest := by
  cases eq : targets site with
  | none => simp [targetSet, eq, admits]
  | some nodes => simpa [targetSet, eq, admits] using listed

theorem direct_embeds {inventory : Inventory} {targets : Targets} {source dest : Node signature}
    (edge : DirectEdge inventory source dest) : (arcGraph (knownArcs inventory targets)).edge source dest := by
  cases source with
  | foreign stub => exact (foreign_leaf _ _ stub _ edge).elim
  | localFn caller => exact arc_mem.mpr (List.mem_append_left _ (mem_directArcs.mpr edge))

theorem known_edge {inventory : Inventory} {targets : Targets} {source dest : Node signature}
    (edge : (arcGraph (knownArcs inventory targets)).edge source dest) :
    (mayGraph (declaredAnalysis inventory targets).may).edge source dest := by
  cases source with
  | foreign _ => cases edge
  | localFn caller =>
    rcases List.mem_append.mp (arc_mem.mp edge) with direct | indirect
    · obtain ⟨⟨site, tag, callee⟩, witnessed, rfl, src, dst⟩ := mem_directArcs.mp direct
      exact ⟨⟨site, .direct, callee⟩, witnessed, trivial, src, dst⟩
    · obtain ⟨site, rfl, recorded, listed⟩ := mem_indirectArcs.mp indirect
      exact ⟨⟨site, .indirect, dest⟩, ⟨targetSet targets site, ⟨rfl, recorded⟩, listed_admitted listed⟩,
        trivial, rfl, rfl⟩

theorem closed_edge {inventory : Inventory} {targets : Targets} {source dest : Node signature}
    (edge : (mayGraph (declaredAnalysis inventory targets).may).edge source dest)
    (noTop : ∀ site, source = .localFn site.caller → IndirectAt inventory site → (targets site).isNone = false) :
    (arcGraph (knownArcs inventory targets)).edge source dest := by
  obtain ⟨⟨site, tag, callee⟩, witnessed, _, rfl, rfl⟩ := edge
  apply arc_mem.mpr
  cases tag with
  | direct =>
    exact List.mem_append_left _ (mem_directArcs.mpr ⟨⟨site, .direct, dest⟩, witnessed, rfl, rfl, rfl⟩)
  | indirect =>
    obtain ⟨_, ⟨rfl, recorded⟩, admitted⟩ := witnessed
    apply List.mem_append_right _ (mem_indirectArcs.mpr ⟨site, rfl, recorded, ?_⟩)
    cases eq : targets site with
    | none =>
      have impossible := noTop site rfl recorded
      simp [eq] at impossible
    | some nodes => simpa [targetSet, eq, admits] using admitted

theorem has_top_issue {inventory : Inventory} {targets : Targets} {site : CallSite signature}
    (recorded : IndirectAt inventory site) (unknown : (targets site).isNone = true) :
    OpenReason.topTarget site ∈ siteIssues inventory targets site.caller := by
  obtain ⟨row, inInventory, inRow⟩ := recorded
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨row, inInventory,
    List.mem_filterMap.mpr ⟨Finding.indirect site, inRow, by simp [unknown]⟩⟩)

theorem no_top_of_closed {inventory : Inventory} {targets : Targets} {entry rounds : Nat}
    (closed : (queryGeneral inventory targets entry rounds).issues = [])
    {site : CallSite signature} (seen : .localFn site.caller ∈ (queryGeneral inventory targets entry rounds).knownVertices)
    (recorded : IndirectAt inventory site) : (targets site).isNone = false := by
  by_contra unknown
  have issue : OpenReason.topTarget site ∈ (queryGeneral inventory targets entry rounds).issues :=
    List.mem_append_right _ (List.mem_flatMap.mpr ⟨.localFn site.caller, seen, has_top_issue recorded (by simpa using unknown)⟩)
  simp [closed] at issue

theorem stable_of_closed {inventory : Inventory} {targets : Targets} {entry rounds : Nat}
    (closed : (queryGeneral inventory targets entry rounds).issues = []) :
    stableArcs (knownArcs inventory targets) (queryGeneral inventory targets entry rounds).knownVertices = true := by
  change (if stableArcs _ _ then [] else [OpenReason.fuel]) ++ _ = [] at closed
  have fuel := (List.append_eq_nil_iff.mp closed).1
  split at fuel
  · assumption
  · contradiction

theorem finite_reach_sound {arcs : List (Nat × Node signature)} {entry rounds : Nat} {dest : Node signature}
    (mem : dest ∈ finiteReach arcs entry rounds) : Reachable (arcGraph arcs) (.localFn entry) dest :=
  iterate_arcs_sound (fun _ h => (List.mem_singleton.mp h).symm ▸ Relation.ReflTransGen.refl)
    (fun _ _ path edge => Relation.ReflTransGen.tail path edge) mem

theorem finite_path_sound {arcs : List (Nat × Node signature)} {entry rounds : Nat} {dest : Node signature}
    (mem : dest ∈ finitePaths arcs entry rounds) : CallPath (arcGraph arcs) (.localFn entry) dest :=
  iterate_arcs_sound (fun _ h => Relation.TransGen.single h) (fun _ _ path edge => Relation.TransGen.tail path edge) mem

theorem finite_path_complete {arcs : List (Nat × Node signature)} {entry rounds : Nat}
    (done : stableArcs arcs (finitePaths arcs entry rounds) = true)
    {dest : Node signature} (path : CallPath (arcGraph arcs) (.localFn entry) dest) :
    dest ∈ finitePaths arcs entry rounds := by
  induction path with
  | single edge => exact arc_seed_mem arcs rounds edge
  | tail _ edge ih => exact arc_step_closed (arcs_fixed_of_stable done) ih edge

theorem finite_reach_exact {arcs : List (Nat × Node signature)} {entry rounds : Nat}
    (done : stableArcs arcs (finiteReach arcs entry rounds) = true) :
    ReachProblem (arcGraph arcs) (.localFn entry) {dest | dest ∈ finiteReach arcs entry rounds} :=
  reach_problem_of_certificate ⟨arc_seed_mem arcs rounds (List.Mem.head _),
    fun {_ _} mem edge => arc_step_closed (arcs_fixed_of_stable done) mem edge, fun {_} => finite_reach_sound⟩

theorem closed_reach {inventory : Inventory} {targets : Targets} {entry rounds : Nat}
    (closed : (queryGeneral inventory targets entry rounds).issues = []) :
    ReachProblem (mayGraph (declaredAnalysis inventory targets).may) (.localFn entry)
      {dest | dest ∈ (queryGeneral inventory targets entry rounds).knownVertices} := by
  refine reach_problem_of_certificate ⟨arc_seed_mem _ rounds (List.Mem.head _), ?_, ?_⟩
  · intro source dest seen step
    exact arc_step_closed (arcs_fixed_of_stable (stable_of_closed closed)) seen
      (closed_edge step (fun site eq recorded => no_top_of_closed closed (eq ▸ seen) recorded))
  · intro dest mem
    exact Relation.ReflTransGen.mono (fun _ _ edge => known_edge edge) _ _ (finite_reach_sound mem)

theorem closed_paths {inventory : Inventory} {targets : Targets} {entry rounds pathRounds : Nat}
    (closed : (queryGeneral inventory targets entry rounds).issues = [])
    (done : stableArcs (knownArcs inventory targets) (finitePaths (knownArcs inventory targets) entry pathRounds) = true) :
    PathProblem (mayGraph (declaredAnalysis inventory targets).may) (.localFn entry)
      {dest | dest ∈ finitePaths (knownArcs inventory targets) entry pathRounds} := by
  intro dest
  refine ⟨fun mem => Relation.TransGen.mono (fun _ _ edge => known_edge edge) _ _ (finite_path_sound mem), ?_⟩
  intro path
  apply finite_path_complete done
  have step {source target : Node signature}
      (prior : Reachable (mayGraph (declaredAnalysis inventory targets).may) (.localFn entry) source)
      (edge : (mayGraph (declaredAnalysis inventory targets).may).edge source target) :
      (arcGraph (knownArcs inventory targets)).edge source target :=
    closed_edge edge (fun site eq recorded => no_top_of_closed closed (eq ▸ (closed_reach closed _).mpr prior) recorded)
  induction path with
  | single edge => exact .single (step .refl edge)
  | tail prior edge ih => exact .tail ih (step prior.to_reflTransGen edge)

theorem foreign_reach_iff_path {g : Silmaril.Semantics.Graph.RelGraph (Node signature)} {entry : Nat} {leaf : Stub} :
    Reachable g (.localFn entry) (.foreign leaf) ↔ CallPath g (.localFn entry) (.foreign leaf) := by
  refine ⟨fun reach => ?_, Relation.TransGen.to_reflTransGen⟩
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp reach with impossible | path
  · cases impossible
  · exact path

theorem closed_frontier {inventory : Inventory} {targets : Targets} {entry rounds : Nat}
    (closed : (queryGeneral inventory targets entry rounds).issues = []) :
    FrontierProblem (mayGraph (declaredAnalysis inventory targets).may) entry
      {leaf | leaf ∈ (queryGeneral inventory targets entry rounds).knownFrontier} := by
  ext leaf
  exact mem_frontier.trans ((closed_reach closed _).trans foreign_reach_iff_path)

theorem known_frontier_sound {inventory : Inventory} {targets : Targets} {entry rounds : Nat} {leaf : Stub}
    (mem : leaf ∈ (queryGeneral inventory targets entry rounds).knownFrontier) :
    leaf ∈ foreignFrontier (mayGraph (declaredAnalysis inventory targets).may) entry :=
  foreign_reach_iff_path.mp (Relation.ReflTransGen.mono (fun _ _ edge => known_edge edge) _ _
    (finite_reach_sound (mem_frontier.mp mem)))

theorem frontier_bound {inventory : Inventory} {targets : Targets} {entry rounds : Nat} {leaf : Stub}
    (path : leaf ∈ foreignFrontier (mayGraph (declaredAnalysis inventory targets).may) entry) :
    admits (queryGeneral inventory targets entry rounds).frontierBound leaf := by
  unfold GeneralReport.frontierBound
  split
  · rename_i empty
    have closed : (queryGeneral inventory targets entry rounds).issues = [] := List.isEmpty_iff.mp empty
    exact (closed_frontier closed).symm ▸ path
  · trivial

theorem declared_mono {inventory : Inventory} {old new : Targets}
    (widen : ∀ site dest, admits (targetSet old site) dest → admits (targetSet new site) dest) :
    MayCover (declaredAnalysis inventory old).may (declaredAnalysis inventory new).may := by
  rintro ⟨site, tag, dest⟩ witness
  cases tag with
  | direct => exact witness
  | indirect =>
    obtain ⟨_, ⟨rfl, recorded⟩, admitsDest⟩ := witness
    exact ⟨targetSet new site, ⟨rfl, recorded⟩, widen site dest admitsDest⟩

end Silmaril.Elf.Region.Calls.Proofs

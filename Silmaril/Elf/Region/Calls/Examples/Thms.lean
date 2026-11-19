module

public import Silmaril.Elf.Region.Calls.Examples.Defs
public import Silmaril.Elf.Region.Calls.General.Thms
public import Silmaril.Elf.Region.Calls.Thms
public import Silmaril.Elf.Region.Calls.Semantic.Thms
public import Silmaril.Semantics.Function.Effects.Thms
import Silmaril.Proofs.Elf.Region.CallExamples

@[expose] public section
namespace Silmaril.Elf.Region.Calls.Examples
open Silmaril.Semantics.Function

theorem direct_inventory : arcLabels inventory = [(0, 6), (6, 12)] := by decide +kernel
theorem certified_partition_count : partitionCount = some 3 := by decide +kernel
theorem hello_puts : arcLabels helloInventory = [(0x1060, 0x1050)] := by decide +kernel
theorem frontier : (query inventory 0 3).knownFrontier = [external] := by decide +kernel
theorem complete_scan : (query inventory 0 3).incomplete = false := by decide +kernel
theorem fuel_not_complete : (query inventory 0 0).incomplete = true := by decide +kernel
theorem indirect_is_open : (query indirectInventory 0 2).incomplete = true := by decide +kernel
theorem ambiguous_is_open : (query ambiguousInventory 0 2).incomplete = true := by decide +kernel
theorem unseen_opcode_is_open : (query unsupportedInventory 0 2).incomplete = true := by decide +kernel
theorem unqualified_jump_is_open : (query (tailInventory false) 0 2).incomplete = true := by decide +kernel
theorem fallthrough_is_open : (query fallthroughInventory 0 2).incomplete = true := by decide +kernel
theorem declared_tail_arc : arcLabels (tailInventory true) = [(0, 2)] := by decide +kernel
theorem direct_runner_rejects_indirect :
    queryDirect indirectInventory 0 2 = .error (query indirectInventory 0 2) := rfl
theorem indirect_is_not_empty : (analysis indirectInventory).may ⟨⟨0, 0, .invoke⟩, .indirect,
    .foreign external⟩ :=
  ⟨none, ⟨rfl, extractRow (objectOfCode [0xff, 0xd0, 0xc3]) ⟨[⟨"indirect", 0, 3⟩], [], []⟩
    ⟨"indirect", 0, 3⟩, List.Mem.head _, List.Mem.head _⟩, trivial⟩

theorem frontier_certified : FrontierProblem (directGraph (analysis inventory).may) 0
    {leaf | leaf ∈ (query inventory 0 3).knownFrontier} := frontier_exact rfl

theorem nonempty_certified : PathProblem (directGraph (analysis inventory).may) (.localFn 0)
    {dest | dest ∈ nonemptyReach inventory 0 3} := checked_nonempty rfl

theorem actual_path : CallPath (mayGraph (analysis inventory).may) (.localFn 0) (.foreign external) :=
  consecutive_path Proofs.certificate.may_cover (.cons Proofs.actual_entry (.single Proofs.actual_worker))

theorem entry_body : entryBoundary.semanticBodies fixture 0 entry :=
  Proofs.certificate.body_sound ⟨rfl, rfl, rfl, rfl⟩

theorem refined_path : Consecutive refinedMachine fixture (.localFn 0) initial (.foreign external) afterWorker :=
  .cons Proofs.refined_entry (.single Proofs.refined_worker)

theorem refined_cover : CallGraphProblem (refinedMachine.actualCalls fixture) (analysis inventory) :=
  ext_covers 64 (restrict_sites Proofs.cover (fun _ _ h => h.1))

theorem refined_path_projection : CallPath (mayGraph (analysis inventory).may) (.localFn 0) (.foreign external) :=
  consecutive_path refined_cover refined_path

theorem symbolic_args_bound : argEffects.Sound (fun _ => targetBound) :=
  Effects.Problem.abstractInput_sound Proofs.entry_effects (fun _ _ _ => le_rfl)

theorem mixed_frontier : mixedReport.knownFrontier = [mixedExternal] := by decide +kernel
theorem unreachable_top_stays_closed : mixedReport.issues = [] := rfl
theorem reachable_top_is_reported : widenedReport.issues = [.topTarget ⟨10, 10, .invoke⟩] := rfl
theorem reachable_top_keeps_witness : widenedReport.knownFrontier = [mixedExternal] := by decide +kernel
theorem reachable_top_opens_bound : widenedReport.frontierBound = none := rfl
theorem empty_known_frontier_can_be_top :
    (queryGeneral mixedInventory mixedTargets 10 3).knownFrontier = [] ∧
    (queryGeneral mixedInventory mixedTargets 10 3).frontierBound = none := ⟨rfl, rfl⟩
theorem scan_gap_opens_bound : (queryGeneral unsupportedInventory (fun _ => none) 0 3).frontierBound = none := rfl
theorem fuel_opens_bound : (queryGeneral mixedInventory mixedTargets 0 0).frontierBound = none := rfl

theorem unknown_is_not_empty (future : Stub) : admits widenedReport.frontierBound future := trivial

theorem mixed_exact_frontier : FrontierProblem (mayGraph (declaredAnalysis mixedInventory mixedTargets).may) 0
    {leaf | leaf ∈ mixedReport.knownFrontier} := closed_frontier unreachable_top_stays_closed

theorem mixed_exact_paths : PathProblem (mayGraph (declaredAnalysis mixedInventory mixedTargets).may) (.localFn 0)
    {dest | dest ∈ finitePaths (knownArcs mixedInventory mixedTargets) 0 3} :=
  closed_paths unreachable_top_stays_closed rfl

theorem mixed_path : CallPath (mayGraph (declaredAnalysis mixedInventory mixedTargets).may)
    (.localFn 0) (.foreign mixedExternal) := mixed_exact_paths _ |>.mp (List.Mem.tail _ (List.Mem.head _))

theorem mixed_path_is_not_execution : ¬ ∃ final,
    Consecutive mixedMachine mixedObject (.localFn 0) mixedInitial (.foreign mixedExternal) final :=
  Proofs.mixed_no_execution

theorem widening_preserves_path : CallPath (mayGraph (declaredAnalysis mixedInventory widenedTargets).may)
    (.localFn 0) (.foreign mixedExternal) :=
  path_mono (declared_mono Proofs.widening_admits) (fun _ _ => trivial) mixed_path

open Silmaril.Elf.Staged.Pinned.HelloGcc in
theorem hello_symbol_window : (symbolWindow L s28_31).map (fun spec => (spec.entry, spec.size)) = some (0x1060, 27) :=
  by decide +kernel

end Silmaril.Elf.Region.Calls.Examples

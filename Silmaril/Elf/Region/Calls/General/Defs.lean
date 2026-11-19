module

public import Silmaril.Elf.Region.Calls.Defs

/-! # Finite may-call queries

Finite bounds refer to observed indirect sites. The projection follows only
explicitly listed targets. Reachable Top sites or byte/ownership gaps leave
the frontier open, even if the finite projection has stabilized.
-/

@[expose] public section
namespace Silmaril.Elf.Region.Calls
open Silmaril.Semantics.Function

abbrev Targets := CallSite signature → Option (List (Node signature))

def targetSet (targets : Targets) (site : CallSite signature) : Option (Set (Node signature)) :=
  (targets site).map fun nodes => {node | node ∈ nodes}

def declaredAnalysis (inventory : Inventory) (targets : Targets) : Analysis signature :=
  boundedAnalysis inventory (targetSet targets)

def indirectArcs (inventory : Inventory) (targets : Targets) : List (Nat × Node signature) :=
  inventory.flatMap fun row => row.findings.flatMap fun finding => match finding with
    | .indirect site => ((targets site).getD []).map (site.caller, ·)
    | _ => []

def knownArcs (inventory : Inventory) (targets : Targets) : List (Nat × Node signature) :=
  directArcs inventory ++ indirectArcs inventory targets

def arcGraph (arcs : List (Nat × Node signature)) : Silmaril.Semantics.Graph.RelGraph (Node signature) :=
  ⟨fun source dest => dest ∈ arcSuccessors arcs source⟩

def finiteReach (arcs : List (Nat × Node signature)) (entry rounds : Nat) : List (Node signature) :=
  (expandArcs arcs)^[rounds] [.localFn entry]

def finitePaths (arcs : List (Nat × Node signature)) (entry rounds : Nat) : List (Node signature) :=
  (expandArcs arcs)^[rounds] (arcSuccessors arcs (.localFn entry))

inductive OpenReason where
  | fuel
  | missingOrAmbiguous (caller : Nat)
  | scanGap (caller : Nat) (gap : Gap)
  | topTarget (site : CallSite signature)

def siteIssues (inventory : Inventory) (targets : Targets) (caller : Nat) : List OpenReason :=
  (if (inventory.filter fun row => row.body.entry == caller).length = 1 then []
    else [.missingOrAmbiguous caller]) ++
  inventory.flatMap fun row => row.findings.filterMap fun finding => match finding with
    | .indirect site => if site.caller = caller ∧ (targets site).isNone = true then some (.topTarget site) else none
    | .gap gap => if row.body.entry = caller then some (.scanGap caller gap) else none
    | _ => none

structure GeneralReport where
  knownVertices : List (Node signature)
  knownFrontier : List Stub
  issues : List OpenReason

/-- An open report exposes its known witnesses but conservatively permits any
foreign identity, including one not in the declared stub list. -/
def GeneralReport.frontierBound (report : GeneralReport) : Option (Set Stub) :=
  if report.issues.isEmpty then some {leaf | leaf ∈ report.knownFrontier} else none

def queryGeneral (inventory : Inventory) (targets : Targets) (entry rounds : Nat) : GeneralReport :=
  let arcs := knownArcs inventory targets
  let seen := finiteReach arcs entry rounds
  ⟨seen, seen.filterMap fun node => match node with | .foreign stub => some stub | _ => none,
    (if stableArcs arcs seen then [] else [.fuel]) ++ seen.flatMap fun node => match node with
      | .localFn caller => siteIssues inventory targets caller
      | .foreign _ => []⟩

end Silmaril.Elf.Region.Calls

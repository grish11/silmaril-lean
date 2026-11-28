module

public import Silmaril.SSA.PEG.Figure19.Placement.Defs
public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Automatic.Defs

/-! # One shared branch inside a checked single loop

The proposal consists of a demanded φ row and one primitive shared by
its two arms. The graph supplies the boundary, old-store bindings, strict
paths, and all primitive orders. The prebranch temporaries are local to
a successful continuation step. -/

@[expose] public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Region.Placement

open RVSDG (Port Tuple)
open Figure19 (Assumptions Derives StrictPath)

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {carried vars outs : List (Ty Data)} {result : Ty Data} {n : Nat}
variable {g : Graph P carried [result] n 1}

/-- Only the installed old-store θ references are available as assumptions. -/
def assumptions (d : Descriptor g) (depth : Nat) : Assumptions n :=
  (List.finRange carried.length).map fun slot => (depth, (d.theta.get (portAt carried slot)).id)

/-- The shared row must actually depend on an installed θ of this loop. -/
structure LoopDependency (d : Descriptor g) (shared : Fin n) where
  slot : Fin carried.length
  theta : (g.node (d.theta.get (portAt carried slot)).id).label.thetaLoop = some 0
  path : StrictPath g (d.theta.get (portAt carried slot)).id shared

def LoopDependency.check (d : Descriptor g) (shared : Fin n) :
    Option (LoopDependency d shared) :=
  (List.finRange carried.length).findSome? fun slot => do
    let anchor := (d.theta.get (portAt carried slot)).id
    if theta : (g.node anchor).label.thetaLoop = some 0 then
      let path ← StrictPath.check g anchor n shared
      return ⟨slot, theta, path.path⟩
    else none

/-- Checked placement premises before sequencing. The φ itself is an
unconditional output of the update vector; its arms are still lazy. -/
structure BranchPlacement (d : Descriptor g) (depth : Fin 1 → Nat) (branch shared : Fin n) where
  updateSlot : Port carried (g.sort branch)
  demanded : d.next.get updateSlot = Ref.ofId g.sort branch
  flag : Ref g.sort .bool
  yes : Ref g.sort (g.sort branch)
  no : Ref g.sort (g.sort branch)
  row : g.node branch = .ofLabel .phi (.cons flag (.cons yes (.cons no .nil)))
  trueUse : StrictPath g shared yes.id
  falseUse : StrictPath g shared no.id
  loopUse : LoopDependency d shared
  branchTyped : Derives g depth .inward (depth 0) (assumptions d (depth 0)) branch
  sharedFresh : shared.val ∉ refNumbers d.theta

def BranchPlacement.check (d : Descriptor g) (depth : Fin 1 → Nat) (branch shared : Fin n) :
    Option (BranchPlacement d depth branch shared) := do
  let some demand := lookup (Ref.ofId g.sort branch) d.next | none
  match row : g.node branch with
  | ⟨_, .phi, .cons flag (.cons yes (.cons no .nil))⟩ => do
    let some trueUse := StrictPath.check g shared n yes.id | none
    let some falseUse := StrictPath.check g shared n no.id | none
    let some loopUse := LoopDependency.check d shared | none
    let ctx := assumptions d (depth 0)
    let some branchTyped := Figure19.checkAt g depth .inward (n + 1) (depth 0) ctx branch | none
    if fresh : shared.val ∉ refNumbers d.theta then
      return ⟨demand.val, demand.property, flag, yes, no, row, trueUse.path,
        falseUse.path, loopUse, branchTyped.proves, fresh⟩
    else none
  | _ => none

/-- Synthesize and check a primitive-only slice from an available scope. -/
def primitiveSchedule (scope : Tuple (Ref g.sort) vars) (roots : Tuple (Ref g.sort) outs) :
    Option (Schedule g true roots scope) := do
  let some order := scopedOrder g scope roots | none
  Schedule.check g roots order scope true

/-- Bind the flag and shared computation before branching. Each arm
returns the selected value plus the inherited scope, so the join keeps
one φ slot and the same old store until the terminal update projection. -/
def BranchPlacement.schedule {d : Descriptor g} {depth : Fin 1 → Nat} {branch shared : Fin n}
    (site : BranchPlacement d depth branch shared) : Option (Schedule g true d.next d.theta) := do
  let sharedRef := Ref.ofId g.sort shared
  let some order := scopedOrder g d.theta (.cons site.flag (.cons sharedRef .nil)) | none
  Schedule.checkThen g d.next (fun scope => do
    let some test := lookup site.flag scope | none
    let some _ := lookup sharedRef scope | none
    if fresh : branch.val ∉ refNumbers scope then
      let yes ← primitiveSchedule scope (.cons site.yes scope)
      let no ← primitiveSchedule scope (.cons site.no scope)
      let tail ← primitiveSchedule (.cons (Ref.ofId g.sort branch) scope) d.next
      return .branch rfl branch site.flag site.yes site.no fresh site.row test.val test.property
        yes no tail
    else none) order d.theta

structure Accepted (g : Graph P carried [result] n 1) (branch shared : Fin n) where
  region : Certificate g false true
  admission : Figure19.Admission g .inward
  placement : BranchPlacement region.descriptor admission.depth branch shared
  scheduled : placement.schedule = some region.update

/-- Check inward placement and derive the primitive orders from the graph.
Boundary discovery and whole-graph demand ranking reuse the single-loop
reverter. The proposal contains row identities only. -/
def extract [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    (g : Graph P carried [result] n 1) (branch shared : Fin n) :
    Option (Accepted g branch shared) := do
  let some d := Automatic.inferBoundary g | none
  let some boundary := checkBoundary g d false | none
  let some admission := Figure19.check g .inward (n + 1) | none
  let some placement := BranchPlacement.check d admission.depth branch shared | none
  let rank := Automatic.inferDemandRank g
  if ranked : rank.check g = true then
    let guard ← primitiveSchedule d.theta d.guardRoots
    match scheduled : placement.schedule with
    | none => none
    | some update =>
      return ⟨⟨d, boundary.valid, rank, ranked, guard, update⟩, admission, placement, scheduled⟩
  else none

end Silmaril.SSA.PEG.Simple.Revert.While.Region.Placement

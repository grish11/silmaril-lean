module

public import Silmaril.SSA.PEG.Figure19.Placement.MustEval.Defs
public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Placement.Defs

/-! # Sharing discovered by must-demand analysis

The parentless loop and old store come from the existing region checker.
One update-root φ may share a primitive across its lazy arms. Arm
roots may themselves be φ nodes, with primitive guard and leaf slices.
-/

@[expose] public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Region.Placement.MustEval

open RVSDG (Tuple)
open Figure19 (Derives)
open Figure19.MustEval (Table analyze)

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {carried vars : List (Ty Data)} {result t : Ty Data} {n : Nat}
variable {g : Graph P carried [result] n 1}

/-- Schedule the result of a lazy arm and preserve its incoming scope.
Recursive branch guards see only the inherited store and temporaries
whose inputs are already available. The branch-local temporaries do
not escape the arm. -/
def armSchedule (g : Graph P carried [result] n 1) :
    Nat → {t : Ty Data} → (root : Ref g.sort t) → {vars : List (Ty Data)} →
      (scope : Tuple (Ref g.sort) vars) → Option (Schedule g true (.cons root scope) scope)
  | 0, _, _, _, _ => none
  | fuel + 1, _, ⟨i, rfl⟩, _, scope =>
    let root := Ref.ofId g.sort i
    if i.val ∈ refNumbers scope then primitiveSchedule scope (.cons root scope)
    else
      match row : g.node i with
      | ⟨_, .phi, .cons flag (.cons yes (.cons no .nil))⟩ => do
        let some order := scopedOrder g scope (.cons flag .nil) | none
        Schedule.checkThen g (.cons root scope) (fun extended => do
          let some test := lookup flag extended | none
          if fresh : i.val ∉ refNumbers extended then
            let trueArm ← armSchedule g fuel yes extended
            let falseArm ← armSchedule g fuel no extended
            let some reads := Reads.check (.cons root extended) (.cons root scope) | none
            return .branch rfl i flag yes no fresh row test.val test.property
              trueArm falseArm (.done reads)
          else none) order scope
      | _ => primitiveSchedule scope (.cons root scope)
termination_by structural fuel _ _ _ _ => fuel

/-- The checked proposal identifies a demanded feedback φ and certifies
both arm demands at a single iteration. The shared row must be a fresh
primitive with a strict dependency on an installed θ. -/
structure Candidate (d : Descriptor g) (depth : Fin 1 → Nat) (table : Table n) where
  branch : Fin n
  shared : Fin n
  updateSlot : RVSDG.Port carried (g.sort branch)
  demanded : d.next.get updateSlot = Ref.ofId g.sort branch
  flag : Ref g.sort .bool
  yes : Ref g.sort (g.sort branch)
  no : Ref g.sort (g.sort branch)
  row : g.node branch = .ofLabel .phi (.cons flag (.cons yes (.cons no .nil)))
  trueUse : shared ∈ table[yes.id.val]
  falseUse : shared ∈ table[no.id.val]
  loopUse : LoopDependency d shared
  typed : Derives g depth .inward (depth 0) (assumptions d (depth 0)) shared

/-- Check the proposal against the given table, excluding candidates
already demanded by the outer flag. The accepted extractor fixes the
table to the result of the analysis. -/
def Candidate.check (d : Descriptor g) (depth : Fin 1 → Nat) (table : Table n)
    (branch shared : Fin n) : Option (Candidate d depth table) := do
  let some demand := lookup (Ref.ofId g.sort branch) d.next | none
  let ⟨_, .op _, _⟩ := g.node shared | none
  if shared.val ∈ refNumbers d.theta then none
  else
    match row : g.node branch with
    | ⟨_, .phi, .cons flag (.cons yes (.cons no .nil))⟩ =>
      if uses : shared ∈ table[yes.id.val] ∧ shared ∈ table[no.id.val] ∧
          shared ∉ table[flag.id.val] then do
        let some loopUse := LoopDependency.check d shared | none
        let some typed := Figure19.checkAt g depth .inward (n + 1) (depth 0)
          (assumptions d (depth 0)) shared | none
        return ⟨branch, shared, demand.val, demand.property, flag, yes, no, row,
          uses.1, uses.2.1, loopUse, typed.proves⟩
      else none
    | _ => none

def Candidate.schedule {d : Descriptor g} {depth : Fin 1 → Nat} {table : Table n}
    (site : Candidate d depth table) : Option (Schedule g true d.next d.theta) := do
  let shared := Ref.ofId g.sort site.shared
  let root := Ref.ofId g.sort site.branch
  let some order := scopedOrder g d.theta (.cons site.flag (.cons shared .nil)) | none
  Schedule.checkThen g d.next (fun scope => do
    let some test := lookup site.flag scope | none
    let some _ := lookup shared scope | none
    if fresh : site.branch.val ∉ refNumbers scope then
      let yes ← armSchedule g n site.yes scope
      let no ← armSchedule g n site.no scope
      let tail ← primitiveSchedule (.cons root scope) d.next
      return .branch rfl site.branch site.flag site.yes site.no fresh site.row test.val
        test.property yes no tail
    else none) order d.theta

structure Accepted (g : Graph P carried [result] n 1) where
  region : Certificate g false true
  admission : Figure19.Admission g .inward
  candidate : Candidate region.descriptor admission.depth (analyze g)
  scheduled : candidate.schedule = some region.update

/-- Try the update ports in order and the rows in table order, computing
the demand table once. Every selected pair passes the schedule checker.
Recognition is conservative and does not require row IDs from the caller. -/
def extract [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    (g : Graph P carried [result] n 1) : Option (Accepted g) := do
  let some d := Automatic.inferBoundary g | none
  let some boundary := checkBoundary g d false | none
  let some admission := Figure19.check g .inward (n + 1) | none
  let rank := Automatic.inferDemandRank g
  if ranked : rank.check g = true then
    let guard ← primitiveSchedule d.theta d.guardRoots
    let table := analyze g
    (List.finRange carried.length).findSome? fun slot =>
      let branch := (d.next.get (portAt carried slot)).id
      (List.finRange n).findSome? fun shared => do
        let some site := Candidate.check d admission.depth table branch shared | none
        match scheduled : site.schedule with
        | none => none
        | some update =>
          return ⟨⟨d, boundary.valid, rank, ranked, guard, update⟩, admission, site, scheduled⟩
  else none

end Silmaril.SSA.PEG.Simple.Revert.While.Region.Placement.MustEval

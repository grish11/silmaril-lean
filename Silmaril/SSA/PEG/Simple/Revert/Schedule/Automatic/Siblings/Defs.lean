module

public import Silmaril.SSA.PEG.Simple.Revert.Schedule.Automatic.Cuts.Defs

/-! # Infer cut and export anchors for sequential parentless PEG loops -/

public section

namespace Silmaril.SSA.PEG.Simple.Revert.Schedule.Automatic.Siblings

open RVSDG (Tuple)
open PEG.Reindex.Automatic (refIds)

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n l : Nat}

inductive Failure where
  | invalidRank
  | noLoops
  | nestedKey (key : Nat)
  | dependencyCycle
  | coverage
  | missingExport (key : Nat)
  | iterationValue (row : Nat)
  | checkedCuts (reason : Cuts.Failure)
  deriving DecidableEq, Repr

private def loopRows (g : Graph P params results n l) (key : Fin l) : List (Fin n) :=
  (List.finRange n).filter fun i => (g.node i).label.loop == some key

private def footprint (g : Graph P params results n l) (i : Fin n) : Option (List (Fin l)) :=
  (Cuts.dependencyRows g [] [i]).map (List.filterMap fun j => (g.node j).label.loop)

private def order (prerequisites : Fin l → List (Fin l)) :
    Nat → List (Fin l) → Option (List (Fin l))
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, pending@(_ :: _) => do
    let key ← pending.find? fun key => (prerequisites key).all fun other => other ∉ pending
    return key :: (← order prerequisites fuel (pending.erase key))

private def isParameter (g : Graph P params results n l) (row : Fin n) : Bool :=
  match g.node row with
  | ⟨_, .param _, _⟩ => true
  | _ => false

private def isSample {ins : List (Ty Data)} {t : Ty Data} : Label P params (Fin l) ins t → Bool
  | .eval _ => true
  | .pass _ => true
  | _ => false

private def rowTuple (g : Graph P params results n l) :
    (rows : List (Fin n)) → Tuple (Ref g.sort) (rows.map g.sort)
  | [] => .nil
  | i :: tail => .cons (Ref.ofId g.sort i) (rowTuple g tail)

/-- Plan from consumers back to producers. Each output bundle includes
both the demanded values computed here and all references to forward. -/
private def boundaries (g : Graph P params results n l) (owner : Fin n → Option (Fin l))
    (samples : List (Fin n)) :
    List (Fin l) → List (Fin n) → List (Cuts.Boundary g) → Except Failure (List (Cuts.Boundary g))
  | [], _, done => .ok done
  | key :: earlier, exports, later => do
    unless exports.any (fun row => owner row == some key) do throw (.missingExport key.val)
    let some readouts := Cuts.dependencyRows g samples exports | throw .coverage
    if let some row := readouts.find? (fun i => (g.node i).label.thetaLoop.isSome) then
      throw (.iterationValue row.val)
    else
      let frontier := (List.finRange n).filter fun row =>
        isParameter g row || (owner row).any (· != key)
      let some seen := Cuts.dependencyRows g frontier (exports ++ loopRows g key) | throw .coverage
      let inputs := seen.filter fun row => row ∈ frontier
      let b : Cuts.Boundary g := ⟨_, _, rowTuple g inputs, rowTuple g exports⟩
      boundaries g owner samples earlier inputs (b :: later)
termination_by structural remaining _ _ => remaining

/-- Propose canonical anchors in dependency order, breaking ties by loop
key. Rows with loop dependencies belong to their latest prerequisite
loop. Parameter-only computations can remain local to a consuming leaf. -/
def inferBoundaries (g : Graph P params results n l) : Except Failure (List (Cuts.Boundary g)) := do
  let active := (List.finRange l).filter fun key => !(loopRows g key).isEmpty
  if active.isEmpty then throw .noLoops
  if let some key := active.find? (fun key => (g.forest.parent key).isSome) then
    throw (.nestedKey key.val)
  else
    let footprints := Vector.ofFn (footprint g)
    if covered : ∀ i, (footprints.get i).isSome then
      let used := fun i => (footprints.get i).get (covered i)
      let prerequisites := fun key => ((loopRows g key).flatMap used).filter (· != key)
      let some ordered := order prerequisites active.length active | throw .dependencyCycle
      let reverse := ordered.reverse
      let owner := fun row => reverse.find? fun key => key ∈ used row
      let samples := (List.finRange n).filter fun row => isSample (g.node row).label
      let rootIds := refIds g.roots
      let exports := (List.finRange n).filter fun row => row ∈ rootIds
      boundaries g owner samples reverse exports []
    else throw .coverage

/-- Infer cuts from a typed graph and use the existing leaf and schedule
checkers. Rank admission covers the original table. The search budget
is passed to the shared fixed-cut order search. -/
def discover [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    (g : Graph P params results n l) (roles : CountedRoles P) (rank : DemandRank n l) (budget : Nat) :
    Except Failure (Found g (.counted roles) rank) := do
  unless rank.check g do throw .invalidRank
  match inferBoundaries g with
  | .error reason => .error reason
  | .ok cuts => (Cuts.discover g (.counted roles) rank cuts budget).mapError Failure.checkedCuts

end Silmaril.SSA.PEG.Simple.Revert.Schedule.Automatic.Siblings

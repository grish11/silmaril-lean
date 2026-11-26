module

public import Silmaril.SSA.PEG.Simple.Revert.While.Nested.Region.Defs
public import Silmaril.SSA.PEG.Simple.Revert.While.Nested.Automatic.Defs

/-! # Discover a graph-local parent/child descriptor -/

@[expose] public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Nested.Region.Automatic

open RVSDG (Port Tuple)
open Simple.Revert.While.Region (nodeAt lookup)

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {outer : List (Ty Data)} {result t : Ty Data} {n l : Nat}

structure OuterSlot (g : Graph P outer [result] n l) (t : Ty Data) where
  theta : Ref g.sort t
  initial : Ref g.sort t
  next : Ref g.sort t

/-- The old outer store is ordered by input port. Reading θ rows
directly permits the single designated eval to observe only one slot. -/
def outerCandidate [DecidableEq Data] (g : Graph P outer [result] n l)
    (key : Fin l) (port : Port outer t) (i : Fin n) : Option (OuterSlot g t) := do
  let some theta := Ref.check g.sort t i.val | none
  let ⟨_, .theta owner, args⟩ := nodeAt g theta | none
  let initial := args.get .head
  let ⟨_, .param p, _⟩ := nodeAt g initial | none
  letI := Check.portEq p port
  if owner = key ∧ p = port then some ⟨theta, initial, args.get (.tail .head)⟩ else none

def readOuter [DecidableEq Data] (g : Graph P outer [result] n l) (key : Fin l) :
    {vars : List (Ty Data)} → Tuple (Port outer) vars → Option (Tuple (OuterSlot g) vars)
  | _, .nil => some .nil
  | _, .cons port tail => do
    let [row] := (List.finRange n).filterMap (outerCandidate g key port) | none
    return .cons row (← readOuter g key tail)

def thetaCount (g : Graph P outer [result] n l) (key : Fin l) : Nat :=
  (List.finRange n).countP fun i => (g.node i).label.thetaLoop == some key

def passFlag (g : Graph P outer [result] n l) (key : Fin l) (pass : Ref g.sort .count) :
    Option (Ref g.sort .bool) := do
  let ⟨_, .pass owner, args⟩ := nodeAt g pass | none
  if owner = key then some (args.get .head) else none

/-- Recover an untrusted descriptor. The child store is ordered by its
eval rows, with one eval per child θ. The existing checker validates
the primitive capture and commit slices over the inferred scopes. -/
def describe [DecidableEq Data] (g : Graph P outer [result] n l) (negate : P [.bool] .bool) :
    Option (Σ inner, {d : Descriptor g inner // d.negate = negate}) := do
  let some header := Nested.Automatic.locate g | none
  let some outerFlag := passFlag g header.outerKey header.outerPass | none
  let some childFlag := passFlag g header.childKey header.childPass | none
  if thetaCount g header.outerKey != outer.length then none else
    let some old := readOuter g header.outerKey (ports outer) | none
    let oldRefs := old.map fun _ row => row.theta
    let ⟨_, .eval _, args⟩ := nodeAt g (g.roots.get .head) | none
    let some returned := lookup (args.get .head) oldRefs | none
    let exits := Nested.Automatic.bundleIds g header.childKey
    if exits.isEmpty || thetaCount g header.childKey != exits.length then none else
      let some ⟨inner, child⟩ := Nested.Automatic.bundleAt g header.childKey header.childPass exits | none
      return ⟨inner, ⟨{
        outerKey := header.outerKey
        childKey := header.childKey
        outerTheta := oldRefs
        outerInit := old.map fun _ row => row.initial
        outerNext := old.map fun _ row => row.next
        outerFlag := outerFlag
        outerPass := header.outerPass
        returnSlot := returned.val
        childTheta := child.map fun _ row => row.theta
        childInit := child.map fun _ row => row.initial
        childNext := child.map fun _ row => row.next
        childFlag := childFlag
        childPass := header.childPass
        childExit := child.map fun _ row => row.exit
        negate := negate }, rfl⟩⟩

structure Recovered (g : Graph P outer [result] n l) (negate : P [.bool] .bool) where
  inner : List (Ty Data)
  certificate : Accepted g inner
  negate_eq : certificate.descriptor.negate = negate

/-- The supplied rank and discovered boundary must pass the unchanged
graph-local checker on the input graph. -/
def extract [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    (g : Graph P outer [result] n l) (rank : DemandRank n l) (negate : P [.bool] .bool) :
    Option (Recovered g negate) := do
  let ⟨inner, descriptor⟩ ← describe g negate
  let checked ← Region.check g descriptor.val rank
  return ⟨inner, checked.val, (congrArg Descriptor.negate checked.property).trans descriptor.property⟩

end Silmaril.SSA.PEG.Simple.Revert.While.Nested.Region.Automatic

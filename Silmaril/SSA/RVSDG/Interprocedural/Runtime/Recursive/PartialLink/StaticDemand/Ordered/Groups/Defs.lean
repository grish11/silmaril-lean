module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Defs

/-! Disjoint demand slots for independently checked φ groups. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {earlier later calls : MemberSummaries V S} {imports : Ports (Ty V S)}
variable {past familyPast : List (Ports (Ty V S))}

open Continuation.Partial.Executable (Actions)
open NestedTheta.Liveness (Demand)

abbrev leftIndex (earlier later : MemberSummaries V S) (i : Fin earlier.members.length) :
    Fin (earlier.members ++ later.members).length :=
  (i.castAdd later.members.length).cast List.length_append.symm

abbrev rightIndex (earlier later : MemberSummaries V S) (i : Fin later.members.length) :
    Fin (earlier.members ++ later.members).length :=
  (i.natAdd earlier.members.length).cast List.length_append.symm

def slotCases (earlier later : MemberSummaries V S)
    {result : Fin (earlier.members ++ later.members).length → Sort _}
    (left : ∀ i, result (leftIndex earlier later i))
    (right : ∀ j, result (rightIndex earlier later j))
    (i : Fin (earlier.members ++ later.members).length) : result i :=
  Fin.addCases (motive := fun j => result (j.cast List.length_append.symm))
    left right (i.cast List.length_append)

theorem slotCases_left (earlier later : MemberSummaries V S)
    {result : Fin (earlier.members ++ later.members).length → Sort _}
    {left right} (i : Fin earlier.members.length) :
    slotCases earlier later (result := result) left right (leftIndex earlier later i) = left i :=
  Fin.addCases_left i

theorem slotCases_right (earlier later : MemberSummaries V S)
    {result : Fin (earlier.members ++ later.members).length → Sort _}
    {left right} (j : Fin later.members.length) :
    slotCases earlier later (result := result) left right (rightIndex earlier later j) = right j :=
  Fin.addCases_right j

/-- Add fresh dispatch slots while preserving the earlier slot numbers. -/
def append (earlier later : MemberSummaries V S) : MemberSummaries V S where
  members := earlier.members ++ later.members
  captures := slotCases earlier later earlier.captures later.captures
  live := slotCases earlier later earlier.live later.live
  monotone i low high le := slotCases earlier later
    (result := fun j => slotCases earlier later (result := fun _ => Demand → List Address) earlier.live later.live j low ⊆
      slotCases earlier later (result := fun _ => Demand → List Address) earlier.live later.live j high)
    (fun j => by simpa only [slotCases_left] using earlier.monotone j le)
    (fun j => by simpa only [slotCases_right] using later.monotone j le) i

theorem append_at_old (earlier later : MemberSummaries V S) (i : Fin earlier.members.length) :
    (append earlier later).at (leftIndex earlier later i) = earlier.at i := by
  simp [MemberSummaries.at, append, leftIndex, List.getElem_append_left i.isLt, slotCases_left]

theorem append_at_new (earlier later : MemberSummaries V S) (j : Fin later.members.length) :
    (append earlier later).at (rightIndex earlier later j) = later.at j := by
  simp [MemberSummaries.at, append, rightIndex, List.getElem_append_right, slotCases_right]

/-- The actual outer capture wires for a checked group. Its family
specifies the body summaries and the slots available inside the bodies. -/
structure GroupBinding (Op : Dialect.{u, v} (ValueSort V S) S) (later : MemberSummaries V S)
    (imports : Ports (Ty V S)) (past : List (Ports (Ty V S)))
    (calls : MemberSummaries V S := later) (familyPast : List (Ports (Ty V S)) := []) where
  family : StaticDemand.Family Op later imports calls familyPast
  captures : Wires imports past family.context

/-- Use a family at the same linker prefix as its actual capture wires. -/
def GroupBinding.ofFamily (family : StaticDemand.Family Op later imports calls past) :
    GroupBinding Op later imports past calls past :=
  ⟨family, family.captures⟩

def GroupBinding.term (binding : GroupBinding Op later imports past calls familyPast) : PhiTerm Op imports past later.members :=
  ⟨binding.family.context, binding.captures, binding.family.group.definitions⟩

abbrev SlotGuard (m : Machine.{u, v, w} Op) (summary : MemberSummary V S) :=
  m.Val summary.fn.port → Tuple m.Val summary.captures → Prop

def Guard.combine (left : Guard m earlier) (right : Guard m later) : Guard m (append earlier later) :=
  slotCases earlier later (result := fun i => SlotGuard m ((append earlier later).at i))
    (fun i => (append_at_old earlier later i).symm ▸ left i)
    (fun i => (append_at_new earlier later i).symm ▸ right i)

abbrev DispatchAt (actions : Actions m σ) (summary : MemberSummary V S)
    (left right : SlotGuard m summary) :=
  ∀ fL fR capsL capsR, left fL capsL → right fR capsR → CallAgrees actions summary fL fR capsL capsR

theorem Guard.combine_left (left : Guard m earlier) (right : Guard m later) (i : Fin earlier.members.length) :
    (left.combine right) (leftIndex earlier later i) = (append_at_old earlier later i).symm ▸ left i :=
  slotCases_left _ _ i

theorem Guard.combine_right (left : Guard m earlier) (right : Guard m later) (i : Fin later.members.length) :
    (left.combine right) (rightIndex earlier later i) = (append_at_new earlier later i).symm ▸ right i :=
  slotCases_right _ _ i

def GroupBinding.read (binding : GroupBinding Op later imports past calls familyPast) (inputs : Tuple m.Val imports)
    (locals : Locals m.Val past) : Tuple m.Val binding.family.context :=
  binding.captures.read inputs locals

def GroupBinding.locals (binding : GroupBinding Op later imports past calls familyPast) (inputs : Tuple m.Val imports)
    (old : Locals m.Val past) : Locals m.Val (past ++ [memberPorts later.members]) :=
  old.snoc (binding.family.references (binding.read inputs old))

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered

module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Family.Defs
public import Silmaril.Semantics.Dataflow.FiniteHeight.Thms
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Finset.Union

/-! Joint backwards demand on the finite signatures of a statically resolved φ group. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand

open NestedTheta.Liveness

universe u v
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {entry results : Ports (Ty V S)} {past sigs : List (Ports (Ty V S))} {loops : Bool}

/-- Replace the abstract reads of recursive calls without changing their typed signatures. -/
structure MemberTransfer (n : Nat) where
  live : Fin n → Demand → List Address
  monotone : ∀ i {low high : Demand}, (∀ p, low p = true → high p = true) → live i low ⊆ live i high

def MemberTransfer.LE {n : Nat} (low high : MemberTransfer n) : Prop :=
  ∀ i demand, low.live i demand ⊆ high.live i demand

def MemberSummaries.withReads (table : MemberSummaries V S)
    (reads : MemberTransfer table.members.length) : MemberSummaries V S :=
  ⟨table.members, table.captures, reads.live, reads.monotone⟩

/-- Use a signature-only index when writing bodies for synthesis. A template
can also reuse a supplied summary's signatures and typed bodies. -/
def MemberSummaries.signaturesOnly (members : List (Function V S))
    (captures : Fin members.length → Ports (Ty V S)) : MemberSummaries V S :=
  ⟨members, captures, fun _ _ => [], by intro _ _ _ _ _ h; exact h⟩

abbrev TransferFor : Option (MemberSummaries V S) → Type
  | none => PUnit
  | some table => MemberTransfer table.members.length

def withTransfer : (member : Option (MemberSummaries V S)) → TransferFor member → Option (MemberSummaries V S)
  | none, _ => none
  | some table, reads => some (table.withReads reads)

/-- Reuse the same checked wire syntax with a different abstract summary. -/
def Code.withTransfer : {entry results : Ports (Ty V S)} → {past sigs : List (Ports (Ty V S))} →
    {loops : Bool} → {member : Option (MemberSummaries V S)} →
    Code Op entry past sigs results loops member → (reads : TransferFor member) →
    Code Op entry past sigs results loops (StaticDemand.withTransfer member reads)
  | _, _, _, _, _, _, .ret wires, _ => .ret wires
  | _, _, _, _, _, _, .primitive op wires rest, reads => .primitive op wires (rest.withTransfer reads)
  | _, _, _, _, _, _, .apply target captures body args rest, reads =>
    .apply target captures (body.withTransfer reads) args (rest.withTransfer reads)
  | _, _, _, _, _, _, .gamma extra sigs selector wires arms rest, reads =>
    .gamma extra sigs selector wires (fun i => (arms i).withTransfer reads) (rest.withTransfer reads)
  | _, _, _, _, _, _, .theta wires body rest, reads =>
    .theta wires (body.withTransfer reads) (rest.withTransfer reads)
  | _, _, _, _, _, _, .callAt (table := table) i target captures args rest, reads =>
    .callAt (table := table.withReads reads)
      i target captures args (rest.withTransfer reads)

namespace Family

variable (shape : MemberSummaries V S)

/-- Interpret the body call slots using a candidate table for the local
members. Extra slots can have fixed summaries. The lifted transfer must
preserve inclusion between candidates. -/
structure CallTransfer (shape : MemberSummaries V S) where
  signatures : MemberSummaries V S
  lift : MemberTransfer shape.members.length → MemberTransfer signatures.members.length
  lift_mono : ∀ {low high}, low.LE high → (lift low).LE (lift high)

def CallTransfer.local (shape : MemberSummaries V S) : CallTransfer shape :=
  ⟨shape, id, fun h => h⟩

/-- The linked member bodies and capture wires, before summary closure is certified.
The rows use the local members of `shape`. The body index fixes all typed
call slots, including any earlier summaries supplied by `calls`. -/
structure Template (Op : Dialect.{u, v} (ValueSort V S) S) (shape : MemberSummaries V S)
    (imports : Ports (Ty V S)) (calls : CallTransfer shape := .local shape)
    (past : List (Ports (Ty V S)) := []) where
  context : Ports (Ty V S)
  captures : Wires imports past context
  memberWires : (i : Fin shape.members.length) →
    Wires (context ++ memberPorts shape.members) (memberOutputs (shape.members.take i.val))
      (memberPorts shape.members ++ (shape.at i).captures)
  sigs : Fin shape.members.length → List (Ports (Ty V S))
  body : (i : Fin shape.members.length) →
    Code Op ((memberPorts shape.members ++ (shape.at i).captures) ++ (shape.at i).fn.args)
      [] (sigs i) (shape.at i).fn.results true (some calls.signatures)

abbrev OutputMask (i : Fin shape.members.length) := Feedback.Mask (shape.at i).fn.results.length
abbrev InputIndex (i : Fin shape.members.length) := Fin ((shape.at i).captures ++ (shape.at i).fn.args).length

/-- A finite table is a set of (member, output mask, input position) bits.
Inclusion is exactly the pointwise order on the member rows. Materializing
the set keeps each lookup independent of earlier transfer rounds. -/
abbrev Bit := Σ i : Fin shape.members.length, OutputMask shape i × InputIndex shape i
abbrev Rows := Finset (Bit shape)

def row (rows : Rows shape) (i : Fin shape.members.length) (wanted : OutputMask shape i) :
    Finset (InputIndex shape i) :=
  Finset.univ.filter fun p => (⟨i, wanted, p⟩ : Bit shape) ∈ rows

def demandMask {arity : Nat} (demand : Demand) : Feedback.Mask arity :=
  Finset.univ.filter fun p => demand p.val

def inputAddresses {arity : Nat} (live : Feedback.Mask arity) : List Address :=
  (List.finRange arity).filterMap fun p => if p ∈ live then some (.arg p.val) else none

theorem inputAddresses_mono {n : Nat} {low high : Feedback.Mask n} (le : low ⊆ high) :
    inputAddresses low ⊆ inputAddresses high := by
  intro a h
  obtain ⟨p, listed, selected⟩ := List.mem_filterMap.mp h
  split at selected
  · exact List.mem_filterMap.mpr ⟨p, listed, by rw [ite_eq_left (le (by assumption))]; exact selected⟩
  · simp at selected

/-- Use the union over subdemands when reading a candidate row. This gives
a monotone callable summary even before the rows themselves are monotone. -/
def readRow (rows : Rows shape) (i : Fin shape.members.length) (demand : Demand) :
    Finset (InputIndex shape i) :=
  (demandMask demand).powerset.biUnion (row shape rows i)

def rowTransfer (rows : Rows shape) : MemberTransfer shape.members.length where
  live i demand := inputAddresses (readRow shape rows i demand)
  monotone i {low high} more := by
    have masks : (demandMask low : OutputMask shape i) ⊆ demandMask high := by
      intro q h
      simp only [demandMask, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
      exact more q.val h
    exact inputAddresses_mono
      (Finset.biUnion_subset_biUnion_of_subset_left (row shape rows i) (Finset.powerset_mono.2 masks))

variable {shape} {imports : Ports (Ty V S)} {calls : CallTransfer shape}

/-- The finite projection of a supplied monotone transfer. -/
def rowsOfTransfer (reads : MemberTransfer shape.members.length) : Rows shape :=
  Finset.univ.filter fun bit => .arg bit.2.2.val ∈ reads.live bit.1 (Feedback.includes bit.2.1)

/-- A simultaneous round reads the actual shared plans and removes the
reserved reference prefix when projecting the live capture/formal ports. -/
def step (template : Template Op shape imports calls past) (reads : MemberTransfer shape.members.length) : Rows shape :=
  Finset.univ.filter fun bit =>
    let live := ((template.body bit.1).withTransfer (calls.lift reads)).plan (Feedback.includes bit.2.1)
    Address.arg ((memberPorts shape.members).length + bit.2.2.val) ∈ live.live

/-- A bound counts every possible live-input bit in each finite output row. -/
def height : Silmaril.Semantics.Dataflow.FiniteHeight.HeightBound (Rows shape) :=
  .finset _

variable (template : Template Op shape imports calls past)

def Template.round (rows : Rows shape) : Rows shape :=
  step template (rowTransfer shape rows)

/-- Stop at the first stable table. The height bound is also a bound on the
number of strict ascents, with one extra check for equality. -/
def Template.synthesize : Rows shape :=
  match Silmaril.Semantics.Dataflow.iterateUntilStable template.round ((height (shape := shape)).bound + 1) ⊥ with
  | some rows => rows
  | none => ⊥

def Template.summaries : MemberSummaries V S :=
  let reads := rowTransfer shape template.synthesize
  shape.withReads reads

/-- The computed transfer at the body's typed call slots. -/
def Template.callReads : MemberTransfer calls.signatures.members.length :=
  calls.lift (rowTransfer shape template.synthesize)

def Template.ReferenceSafe : Prop :=
  ∀ i (p : Fin (memberPorts shape.members).length),
    .arg p.val ∉ (((template.body i).withTransfer template.callReads).plan (fun _ => true)).live

end Family
end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand

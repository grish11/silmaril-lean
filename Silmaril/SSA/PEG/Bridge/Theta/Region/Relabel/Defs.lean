module

public import Silmaril.SSA.PEG.Bridge.Theta.Region.Tuple.Defs
public import Silmaril.SSA.RVSDG.Theta.Institution.Defs
public import Silmaril.SSA.PEG.Thms

/-! # Relabel a checked loop in place -/

@[expose] public section

namespace Silmaril.SSA.PEG.Bridge.Theta.Region.Relabel

open RVSDG (Port Tuple)
open Simple.Revert.While.Region (Certificate Descriptor Schedule Boundary nodeAt)
open Silmaril.SSA.PEG.Bridge.Theta.Region.Ordered (Bundle scalarView)

variable {Data : Type} {P Q : InstructionSet.{0,0} Data}
variable {carried results vars outs : List (Ty Data)} {result t : Ty Data} {n l : Nat}
variable {g : Graph P carried [result] n 1} {allowInvariant : Bool}

def node (f : InstructionMap P Q) {sort : Fin n → Ty Data}
    (row : Node P carried (Fin l) sort t) : Node Q carried (Fin l) sort t :=
  ⟨row.inputs, row.label.map f id, row.args⟩

/-- A projection-reducing presentation of `Graph.mapOps`. All reference and
loop identities, including θ delays, stay in place. -/
def table (f : InstructionMap P Q) (g : Graph P carried results n l) : Graph Q carried results n l :=
  ⟨g.forest, g.sort, fun i => node f (g.node i), g.roots⟩

private theorem kind_map (f : InstructionMap P Q) {ins : List (Ty Data)}
    (label : Label P carried (Fin l) ins t) (p : Fin ins.length) :
    (label.map f id).kind p = label.kind p := by
  cases label <;> rfl

theorem rank_check (f : InstructionMap P Q) (g : Graph P carried results n l) (rank : DemandRank n l) :
    rank.check (table f g) = rank.check g := by
  unfold DemandRank.check
  simp only [table, node, kind_map]
  rfl

def descriptor (f : InstructionMap P Q) (d : Descriptor g) : Descriptor (table f g) :=
  ⟨d.theta, d.initial, d.next, d.guard, d.negated, f d.negate, d.pass, d.returnSlot⟩

theorem nodeAt_map (f : InstructionMap P Q) (r : Ref g.sort t) :
    nodeAt (table f g) r = node f (nodeAt g r) := by
  obtain ⟨i, typed⟩ := r
  cases typed
  rfl

theorem boundary (f : InstructionMap P Q) {d : Descriptor g} (b : Boundary g d allowInvariant) :
    Boundary (table f g) (descriptor f d) allowInvariant where
  parentless := b.parentless
  initialRow _ p := (nodeAt_map f (d.initial.get p)).trans (congrArg (node f) (b.initialRow _ p))
  thetaRow := by
    intro t p
    have mapped : d.FeedbackSlot p → (descriptor f d).FeedbackSlot p := fun row =>
      (nodeAt_map f (d.theta.get p)).trans (congrArg (node f) row)
    cases allowInvariant
    · exact mapped (b.thetaRow _ p)
    · exact (b.thetaRow _ p).imp mapped id
  negationRow := (nodeAt_map f d.negated).trans (congrArg (node f) b.negationRow)
  passRow := (nodeAt_map f d.pass).trans (congrArg (node f) b.passRow)
  evalRow := (nodeAt_map f (g.roots.get .head)).trans (congrArg (node f) b.evalRow)

/-- Relabelling preserves the certified schedule, including local operand
positions and its ordered projection. No opcode comparison is involved. -/
def schedule (f : InstructionMap P Q) {roots : Tuple (Ref g.sort) outs} :
    {vars : List (Ty Data)} → {scope : Tuple (Ref g.sort) vars} →
      Schedule g false roots scope → Schedule (table f g) false roots scope
  | _, _, .done reads => .done reads
  | _, _, .bind i op refs fresh row reads tail =>
    .bind i (f op) refs fresh (congrArg (node f) row) reads (schedule f tail)
  | _, _, .branch enabled .. => nomatch enabled

def certificate (f : InstructionMap P Q) (cert : Certificate g allowInvariant) :
    Certificate (table f g) allowInvariant :=
  ⟨descriptor f cert.descriptor, boundary f cert.boundary, cert.rank,
    (rank_check f g cert.rank).trans cert.ranked, schedule f cert.guard, schedule f cert.update⟩

def bundle (f : InstructionMap P Q) {g : Graph P carried carried n 1} {slot : Port carried result}
    (b : Bundle g slot allowInvariant) : Bundle (table f g) slot allowInvariant where
  scalar := certificate f b.scalar
  roots t p :=
    (nodeAt_map (g := scalarView g slot) f (g.roots.get p)).trans (congrArg (node f) (b.roots t p))

/-- The synthetic branch adapter is fixed by changes of signature. -/
def opcode (f : InstructionMap P Q) : RVSDG.Institution.OpcodeMap (Opcode P) (Opcode Q)
  | _, _, .primitive op => .primitive (f op)
  | _, _, .branch => .branch

end Silmaril.SSA.PEG.Bridge.Theta.Region.Relabel

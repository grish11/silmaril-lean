module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Family.Synthesis.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Feedback
import Silmaril.SSA.RVSDG.NestedTheta.Liveness.Demand.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Proofs

open NestedTheta.Liveness

universe u v
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {entry results : Ports (Ty V S)} {past sigs : List (Ports (Ty V S))} {loops : Bool}
variable {member : Option (MemberSummaries V S)}

abbrev TransferLE : {member : Option (MemberSummaries V S)} → TransferFor member → TransferFor member → Prop
  | none, _, _ => True
  | some _, low, high => ∀ i demand, low.live i demand ⊆ high.live i demand

theorem plan_compare (code : Code Op entry past sigs results loops member)
    {left right : TransferFor member} (reads : TransferLE left right) {low high : Demand}
    (more : ∀ p, p < results.length → low p = true → high p = true) :
    ((code.withTransfer left).plan low).live ⊆ ((code.withTransfer right).plan high).live := by
  induction code generalizing low high with
  | ret wires =>
    apply prepend_mono (fun _ h => h) (selectWires_compare wires ?_)
    intro ty i bound h
    cases ty with
    | state => rfl
    | control | value => exact more i bound h
  | primitive _ _ _ ih => exact prepend_mono (ih reads more) (fun _ h => h)
  | apply _ captures _ arguments _ ihBody ihRest =>
    have suffix := ihRest reads more
    exact prepend_mono suffix
      (applyReads_mono (ihBody reads (fun _ _ => resultDemand_mono suffix _)) captures arguments)
  | @gamma _ _ captures outs _ _ _ _ extra _ selector wires arms rest ihArm ihRest =>
    let kind : NestedTheta.Kind (Instruction Op) (.control (extra + 2) :: captures) outs := .base (.gamma extra)
    exact prepend_mono (ihRest reads more)
      (NestedTheta.Kind.demandReads_compare kind (.cons selector wires) _ (ihRest reads more) _ _ (fun i _ _ more => ihArm i reads fun p _ => more p))
  | @theta _ _ carried _ _ _ _ wires body rest ihBody ihRest =>
    exact prepend_mono (ihRest reads more)
      (NestedTheta.Kind.demandReads_compare (.theta (Op := Instruction Op) carried) wires _ (ihRest reads more) _ _
        (fun _ _ _ more => ihBody reads fun p _ => more p))
  | @callAt _ _ _ _ table i _ captures arguments _ ih =>
    have suffix := ih reads more
    exact prepend_mono suffix (applyReads_mono
      (fun _ h => right.monotone i (resultDemand_mono suffix) (reads i _ h)) captures arguments)

set_option backward.isDefEq.respectTransparency false in
theorem transfer_term (code : Code Op entry past sigs results loops member) (reads : TransferFor member) :
    (code.withTransfer reads).term = code.term := by
  induction code with
  | ret => rfl
  | primitive _ _ _ ih => simp only [Code.withTransfer, Code.term, ih]
  | apply _ _ _ _ _ _ ih => simp only [Code.withTransfer, Code.term, ih]
  | @gamma entry _ captures outs past _ _ _ extra armSigs selector wires arms rest ihArm ihRest =>
    let node : NestedTheta.Node (Instruction Op) entry past outs :=
      ⟨.control (extra + 2) :: captures, .base (.gamma extra), .cons selector wires, armSigs⟩
    exact congrArg₂ (NestedTheta.Term.bind node) (funext fun i => ihArm i reads) (ihRest reads)
  | theta _ _ _ ihBody ihRest => simp only [Code.withTransfer, Code.term, ihBody, ihRest]
  | callAt _ _ _ _ _ ih =>
    simp only [Code.withTransfer, Code.term]
    rw [ih reads]

private theorem origin_arg_lt {Ty : Type u} {inputs : Ports Ty} {locals : List (Ports Ty)} {ty : Ty}
    (source : Origin inputs locals ty) {p : Nat} (h : Address.arg p = source.address) : p < inputs.length := by
  cases source with
  | output => cases h
  | arg q =>
    cases h
    induction q with
    | head => exact Nat.zero_lt_succ _
    | tail _ ih => exact Nat.succ_lt_succ ih

private theorem selected_arg_lt {Ty : Type u} {inputs users : Ports Ty} {locals : List (Ports Ty)}
    (wires : Wires inputs locals users) (selected : Ty → Nat → Bool)
    {p : Nat} (h : Address.arg p ∈ selectWires selected wires) : p < inputs.length := by
  induction wires generalizing selected with
  | nil => simp [selectWires] at h
  | cons source rest ih =>
    simp only [selectWires, List.mem_append] at h
    rcases h with head | tail
    · split at head
      · exact origin_arg_lt source (List.mem_singleton.mp head)
      · simp at head
    · exact ih _ tail

private theorem wired_arg_lt {Ty : Type u} {inputs users : Ports Ty} {locals : List (Ports Ty)}
    (wires : Wires inputs locals users) {p : Nat}
    (h : Address.arg p ∈ wires.addresses) : p < inputs.length := by
  induction wires with
  | nil => simp [Wires.addresses] at h
  | cons source rest ih =>
    exact (List.mem_cons.mp h).elim (origin_arg_lt source) ih

theorem plan_arg_in_range (code : Code Op entry past sigs results loops member) (wanted : Demand)
    {p : Nat} (h : Address.arg p ∈ (code.plan wanted).live) : p < entry.length := by
  induction code generalizing wanted with
  | ret wires =>
    exact selected_arg_lt wires wanted.observes (by
      simpa only [Code.plan, DemandPlan.prepend, transfer, List.filter_nil, List.append_nil] using h)
  | primitive _ operands _ ih =>
    exact (List.mem_append.mp h).elim (wired_arg_lt operands) (fun tail => ih _ (List.mem_filter.mp tail).1)
  | apply _ captures _ arguments _ _ ihRest =>
    exact (List.mem_append.mp h).elim
      (fun reads => (List.mem_append.mp reads).elim (selected_arg_lt captures _) (selected_arg_lt arguments _))
      (fun tail => ihRest _ (List.mem_filter.mp tail).1)
  | gamma _ _ selector wires _ _ _ ihRest =>
    exact (List.mem_append.mp h).elim
      (fun reads => (List.mem_cons.mp reads).elim (origin_arg_lt selector) (selected_arg_lt wires _))
      (fun tail => ihRest _ (List.mem_filter.mp tail).1)
  | theta wires _ _ _ ihRest =>
    exact (List.mem_append.mp h).elim (selected_arg_lt wires _) (fun tail => ihRest _ (List.mem_filter.mp tail).1)
  | callAt _ _ captures arguments _ ih =>
    exact (List.mem_append.mp h).elim
      (fun reads => (List.mem_append.mp reads).elim (selected_arg_lt captures _) (selected_arg_lt arguments _))
      (fun tail => ih _ (List.mem_filter.mp tail).1)

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Proofs

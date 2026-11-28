module

public import Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay.Defs
import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize.Thms
import Silmaril.SSA.SeaOfNodes.Pure.Deletion.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.Pure.SuffixReplay

open Silmaril.SSA.SeaOfNodes.Diamond (Ty Val ValueSort dataPorts)
open Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Deletion (Route)
open Silmaril.SSA.SeaOfNodes.GVN.Elimination (Rewrite Routing)
open Silmaril.SSA.SeaOfNodes.Pure
open Silmaril.SSA.SeaOfNodes.Pure.ConstantFold
open Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.RightSpine (WordWire)
open Silmaril.SSA.SeaOfNodes.Pure.SubZero (Opcode model wordPort)
open Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay
open Silmaril.SSA.RVSDG (Tuple Wires extend)

variable {inputs : List (ValueSort Unit)} {ports : List (Ty Unit)}
variable {block : Block inputs ports} {after : State inputs ports block.sigs}
variable (entry : Tuple (Val model.value) (dataPorts inputs))

theorem program_eval (block : Block inputs ports) :
    block.program.eval model entry = (block.packet.read entry (block.flow.eval model entry PUnit.unit)).get .head := by
  cases block with
  | mk sigs flow packet =>
    cases packet
    rfl

private theorem wires_total {args : List (Ty Unit)} {old new : List (List (Ty Unit))}
    (route : Routing args old new) (wires : Wires args old ports) :
    Route.wires? (fun wire => some (route wire)) wires = some (Routing.wires route wires) := by
  induction wires with
  | nil => rfl
  | cons wire tail ih => simp [Route.wires?, Routing.wires, Tuple.map, ih]

private theorem wires_identity {args : List (Ty Unit)} {old : List (List (Ty Unit))}
    (wires : Wires args old ports) : Route.wires? (fun wire => some wire) wires = some wires := by
  induction wires with
  | nil => rfl
  | cons wire tail ih => simp [Route.wires?, ih]

private theorem wires_compose {args : List (Ty Unit)} {old mid new : List (List (Ty Unit))}
    (first : Route args old mid) (second : Route args mid new) (wires : Wires args old ports) :
    Route.wires? (fun wire => (first wire).bind second) wires =
      (Route.wires? first wires).bind (Route.wires? second) := by
  induction wires with
  | nil => rfl
  | cons wire tail ih =>
    cases head : first wire with
    | none => simp [Route.wires?, head]
    | some mapped =>
      cases rest : Route.wires? first tail <;>
        cases next : second mapped <;> simp [Route.wires?, head, next, ih, rest]

theorem compose_agrees {first : State inputs ports block.sigs} {next : State inputs ports first.block.sigs}
    (before : Agrees block first entry) (after : Agrees first.block next entry) :
    Agrees block (first.compose next) entry := by
  constructor
  · intro t wire routed found
    cases middle : first.route wire with
    | none => simp [State.compose, middle] at found
    | some mapped =>
      exact (before.1 wire mapped middle).trans (after.1 mapped routed (by
        simpa [State.compose, middle] using found))
  · change Route.wires? (fun wire => (first.route wire).bind next.route) block.packet = _
    rw [wires_compose, before.2]
    exact after.2

theorem fromRewrite_agrees (edit : Rewrite Opcode (dataPorts inputs) [] block.sigs)
    (agree : Routing.Agrees edit.route model entry (block.flow.eval model entry PUnit.unit)
      (edit.flow.eval model entry PUnit.unit)) :
    Agrees block (fromRewrite block edit) entry := by
  constructor
  · intro t wire mapped found
    have equal : edit.route wire = mapped := Option.some.inj found
    rw [← equal]
    exact agree t wire
  · exact wires_total edit.route block.packet

theorem step_agrees {action : Action} {wire : WordWire (dataPorts inputs) (extend [] block.sigs)}
    (accepted : step block action wire = .ok after) : Agrees block after entry := by
  cases nominated : AddIdealize.Replay.nominate block.program wire with
  | error reason => simp [step, nominated] at accepted
  | ok candidate =>
    cases action with
    | idealize =>
      cases chosen : AddIdealize.step ⟨fun _ => none⟩ block.program candidate with
      | error reason => simp [step, nominated, chosen] at accepted
      | ok edit =>
        cases edit with
        | none => simp [step, nominated, chosen] at accepted
        | some applied =>
          have same : fromRewrite block applied.rewrite = after := by
            simpa only [step, nominated, chosen, Except.ok.injEq] using accepted
          subst after
          exact fromRewrite_agrees entry applied.rewrite (AddIdealize.step_agrees chosen entry)
    | deleteUnused =>
      cases chosen : Deletion.delete? candidate block.packet with
      | none => simp [step, nominated, chosen] at accepted
      | some deleted =>
        simp only [step, nominated, chosen, Except.ok.injEq] at accepted
        subst after
        exact ⟨Deletion.delete?_agrees chosen model entry PUnit.unit,
          (Deletion.delete?_eq_some_iff.mp chosen).2⟩

private theorem advance_agrees {before : State inputs ports block.sigs} {request : Request inputs block.sigs}
    (agree : Agrees block before entry) (accepted : advance before request = .ok after) :
    Agrees block after entry := by
  cases routed : before.route request.wire with
  | none => simp [advance, routed] at accepted
  | some wire =>
    cases checked : step before.block request.action wire with
    | error reason => simp [advance, routed, checked, Except.map] at accepted
    | ok edit =>
      simp only [advance, routed, checked, Except.map, Except.ok.injEq] at accepted
      subst after
      exact compose_agrees entry agree (step_agrees entry checked)

private theorem runFrom_agrees {before : State inputs ports block.sigs}
    (agree : Agrees block before entry) {index : Nat} {requests : List (Request inputs block.sigs)}
    (accepted : runFrom before index requests = .ok after) : Agrees block after entry := by
  induction requests generalizing before index with
  | nil =>
    cases accepted
    exact agree
  | cons request rest ih =>
    cases applied : advance before request with
    | error reason => simp [runFrom, applied] at accepted
    | ok next =>
      exact ih (advance_agrees entry agree applied) (by simpa only [runFrom, applied] using accepted)

theorem run_agrees {requests : List (Request inputs block.sigs)} (accepted : run block requests = .ok after) :
    Agrees block after entry :=
  runFrom_agrees entry ⟨fun _ _ found => by cases found; rfl, wires_identity block.packet⟩ accepted

variable {original : List (List (Ty Unit))}

theorem runFrom_append (state : State inputs ports original) (index : Nat)
    (pre post : List (Request inputs original)) :
    runFrom state index (pre ++ post) =
      (runFrom state index pre).bind (fun next => runFrom next (index + pre.length) post) := by
  induction pre generalizing state index with
  | nil => simp [runFrom, Except.bind]
  | cons request rest ih =>
    cases checked : advance state request with
    | error reason => simp [runFrom, checked, Except.bind]
    | ok next =>
      simp only [List.cons_append, runFrom, checked]
      rw [ih, List.length_cons, Nat.add_right_comm]
      simp only [Nat.add_assoc]

end Silmaril.Proofs.SSA.SeaOfNodes.Pure.SuffixReplay

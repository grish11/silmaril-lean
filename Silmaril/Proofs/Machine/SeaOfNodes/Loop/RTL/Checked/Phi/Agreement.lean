module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Checked.Phi.Defs
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Checked.Thms
public import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Reindex.Thms
import Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Thms

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Checked.Phi.Proofs

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA (StepsNWithin)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (Reg entry inputs model word)
open Silmaril.SSA
open Silmaril.SSA.SeaOfNodes.Loop (appendTuple)
open Silmaril.SSA.SeaOfNodes.Diamond (Val)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA
  (Atom LayoutMatch encode_injective inputEnv inputRefs_match instruction terminatorRegion)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

theorem lowerChecked_eq_some_iff (g : WordLoop) (targets : Targets) :
    lowerChecked g = some targets ↔ Checked.lower g = some targets.1 ∧ targets.2 = Generic.lower g := by
  rcases targets with ⟨rtl, ssa⟩
  cases machine : Checked.lower g <;> simp [lowerChecked, machine, eq_comm]

theorem activation_agrees (p : Profile) (seed delta old : Word) (fr : Frame Reg) (mem : Memory)
    (hold : fr.get .phi = some old) (hdelta : fr.get (.arg 1) = some delta) :
    let after := p.headerFrame fr old delta
    let halt := p.guardWord old delta = 0
    let next := p.update.eval old delta
    let eval := Eval (instruction model)
      (extend (inputEnv model (entry seed delta)) (Generic.packResult model (out := word) old))
      (Generic.header p.graph) mem
    StepsNWithin p.lower [] 4 ⟨⟨0, 1, 0⟩, fr, [], mem⟩
      (if halt then ⟨⟨0, 2, 0⟩, after.set (.node 3) old, [], mem⟩
       else ⟨⟨0, 1, 0⟩, after.set .phi next, [], mem⟩) ∧
    (if halt then eval 1 (Generic.packResult model (out := word) old) mem
     else eval 0 (Generic.packResult model (out := word) next) mem) := by
  refine ⟨p.header_activation fr mem old delta hold hdelta, ?_⟩
  have run := Generic.header_eval p.graph model (entry seed delta) (.cons old .nil) mem
  rw [p.native_step seed delta old] at run
  by_cases halt : p.guardWord old delta = 0
  · simp only [ite_eq_left halt] at run ⊢
    exact run
  · simp only [ite_eq_right halt] at run ⊢
    exact run

theorem entry_slot_transfer_iff (p : Profile) (order : Fin 2 ≃ Generic.HeaderIncoming p.graph)
    (seed delta : Word) (start finish : Memory) (label : Nat) (payload : Value (Atom model)) :
    Eval (instruction model) (inputEnv model (entry seed delta))
        (terminatorRegion (Generic.slotBranch p.graph order (order.symm (Generic.headerIncoming p.graph .entry))))
        start label payload finish ↔
      label = 0 ∧ payload = Generic.packResult model (out := word) seed ∧ finish = start := by
  rw [Generic.slot_branch_roundtrip]
  change Eval (instruction model) (inputEnv model (entry seed delta))
    (.br (Generic.edge p.graph .entry).target (Generic.edge p.graph .entry).argument)
    start label payload finish ↔ _
  rw [PhiView.latch_eq_transfer (instruction model) (Generic.phiView p.graph)]
  have matched : LayoutMatch model (Generic.entryLayout p.graph) (inputEnv model (entry seed delta))
      (entry seed delta) (p.graph.preheader.eval model (entry seed delta) PUnit.unit) :=
    ⟨inputRefs_match model (entry seed delta), trivial⟩
  rw [Generic.entry_latch p.graph model (entry seed delta) matched]
  rfl

theorem feedback_slot_transfer_iff (p : Profile) (order : Fin 2 ≃ Generic.HeaderIncoming p.graph)
    (seed delta old : Word) {env : Env (Atom model)}
    (matched : let args := appendTuple (.cons (F := Val model.value) (t := .value word) old .nil) (entry seed delta)
      LayoutMatch model (Generic.headerLayout p.graph) env args
        (p.graph.header.eval model args PUnit.unit))
    (start finish : Memory) (label : Nat) (payload : Value (Atom model)) :
    Eval (instruction model) (extend env .unit)
        (terminatorRegion (Generic.slotBranch p.graph order (order.symm (Generic.headerIncoming p.graph .backedge))))
        start label payload finish ↔
      label = 0 ∧ payload = Generic.packResult model (out := word) (p.update.eval old delta) ∧ finish = start := by
  rw [Generic.slot_branch_roundtrip]
  change Eval (instruction model) (extend env .unit)
    (.br (Generic.edge p.graph .backedge).target (Generic.edge p.graph .backedge).argument)
    start label payload finish ↔ _
  rw [PhiView.latch_eq_transfer (instruction model) (Generic.phiView p.graph),
    Generic.feedback_latch p.graph model (entry seed delta) (.cons old .nil) matched,
    p.latch_feedback seed delta old]
  rfl

theorem returns_iff {g : WordLoop} {targets : Targets}
    (accepted : lowerChecked g = some targets)
    (seed delta : Word) (initial final : Memory) (returned : List Word) :
    targets.1.oracle 0 [seed, delta] initial returned final ↔
      ∃ value : Word, returned = [value] ∧
        Eval (instruction model) (inputEnv model (entry seed delta)) targets.2
          initial 0 (Generic.packResult model (out := word) value) final := by
  obtain ⟨ok, typed⟩ := (lowerChecked_eq_some_iff g targets).mp accepted
  rw [typed, Checked.lower_returns_iff ok]
  constructor
  · rintro ⟨value, source, rfl, memory⟩
    subst final
    exact ⟨value, rfl, (Generic.returns_iff g model (entry seed delta) initial value).mp source⟩
  · rintro ⟨value, rfl, run⟩
    obtain ⟨observed, source, _, payload, memory⟩ :=
      (Generic.lower_eval_iff g model (entry seed delta) initial final 0
        (Generic.packResult model (out := word) value)).mp run
    have same : value = observed := encode_injective model (sort := word) (Value.pair.inj payload).1
    exact ⟨observed, source, congrArg (fun word => [word]) same, memory⟩

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Checked.Phi.Proofs

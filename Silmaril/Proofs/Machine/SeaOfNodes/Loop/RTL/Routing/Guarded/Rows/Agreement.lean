module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Reindex.Thms
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Execution

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Proofs

open Silmaril.Machine.Lir (Memory)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA (Steps)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (Reg model word)
open Silmaril.SSA
open Silmaril.SSA.SeaOfNodes.Loop (appendTuple)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA
  (Atom LayoutMatch encodeTuple inputEnv instruction terminatorRegion)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

theorem lowerChecked_eq_some_iff (arity : Nat) (spec : Spec) (targets : Checked.Phi.Targets) :
    lowerChecked arity spec = some targets ↔
      ∃ p, checkPlan arity spec = some p ∧ (lowerBankFunc p.graph).WellFormed ∧
        targets = (lowerBank p.graph, Generic.lower p.graph) := by
  rw [lowerChecked, Option.bind_eq_some_iff]
  apply exists_congr
  intro p
  apply and_congr_right
  intro _
  by_cases ok : (lowerBankFunc p.graph).WellFormed <;> simp [ok, eq_comm]

theorem activation_agrees {arity : Nat} (p : Plan arity) (input old : WordTuple arity)
    (fr : Frame Reg) (mem : Memory) (agree : ArgsMatch fr (appendTuple old input)) :
    let eval := Eval (instruction model) (extend (inputEnv model input) (encodeTuple model old))
      (Generic.header p.graph) mem
    Steps (lowerBank p.graph) ⟨⟨0, 1, 0⟩, fr, [], mem⟩ (p.successor input old fr mem) ∧
      if p.guardWord old = 0 then eval 1 (Generic.packResult model (out := word) (p.exitValue old)) mem
      else eval 0 (encodeTuple model (p.nextBank input old)) mem := by
  refine ⟨header_activation p input old fr mem agree, ?_⟩
  have run := Generic.header_eval p.graph model input old mem
  rw [native_step p input old fr agree] at run
  by_cases halt : p.guardWord old = 0
  · simp only [ite_eq_left halt] at run ⊢
    exact run
  · simp only [ite_eq_right halt] at run ⊢
    exact run

theorem feedback_slot_transfer_iff {arity : Nat} (p : Plan arity)
    (order : Fin 2 ≃ Generic.HeaderIncoming p.graph) (input old : WordTuple arity)
    {env : Env (Atom model)}
    (matched : let args := appendTuple old input
      LayoutMatch model (Generic.headerLayout p.graph) env args (p.graph.header.eval model args PUnit.unit))
    (start finish : Memory) (label : Nat) (payload : Value (Atom model)) :
    Eval (instruction model) (extend env .unit)
        (terminatorRegion (Generic.slotBranch p.graph order
          (order.symm (Generic.headerIncoming p.graph .backedge))))
        start label payload finish ↔
      label = 0 ∧ payload = encodeTuple model (p.nextBank input old) ∧ finish = start := by
  rw [Generic.slot_branch_roundtrip]
  change Eval (instruction model) (extend env .unit)
    (.br (Generic.edge p.graph .backedge).target (Generic.edge p.graph .backedge).argument)
    start label payload finish ↔ _
  rw [PhiView.latch_eq_transfer (instruction model) (Generic.phiView p.graph),
    Generic.feedback_latch p.graph model input old matched, feedback_latch p input old]
  rfl

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Proofs

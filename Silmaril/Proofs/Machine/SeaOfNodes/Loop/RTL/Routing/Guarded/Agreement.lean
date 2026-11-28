module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Reindex.Thms
import Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Thms
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Execution

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Proofs

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA (Prog StepsNWithin)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (Reg model word)
open Silmaril.SSA
open Silmaril.SSA.SeaOfNodes.Loop (appendTuple)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA
  (Atom LayoutMatch encodeTuple encode_injective inputEnv instruction terminatorRegion)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

theorem lowerChecked_eq_some_iff (g : Native) (targets : Checked.Phi.Targets) :
    lowerChecked g = some targets ↔
      (∃ p : Profile, g = graph p) ∧ (lowerBankFunc g).WellFormed ∧
        targets = (rtl g, Generic.lower g) := by
  rw [lowerChecked, Option.bind_eq_some_iff]
  by_cases typed : (lowerBankFunc g).WellFormed
  · constructor
    · rintro ⟨p, recognized, lowered⟩
      have same : g = graph p := (recognize_eq_some_iff g p).mp recognized
      exact ⟨⟨p, same⟩, typed, (Option.some.inj ((ite_eq_left typed).symm.trans lowered)).symm⟩
    · rintro ⟨⟨p, same⟩, _, rfl⟩
      exact ⟨p, (recognize_eq_some_iff g p).mpr same, ite_eq_left typed⟩
  · simp [typed]

theorem activation_agrees (p : Profile) (input : WordTuple 2) (first second : Word)
    (fr : Frame Reg) (mem : Memory)
    (hfirst : fr.get (.arg 2) = some first) (hsecond : fr.get (.arg 3) = some second) :
    let eval := Eval (instruction model) (extend (inputEnv model input) (encodeTuple model (pair first second)))
      (Generic.header (graph p)) mem
    StepsNWithin (rtl (graph p)) [] 4 ⟨⟨0, 1, 0⟩, fr, [], mem⟩ (successor p fr first second mem) ∧
      if p.guardWord first second = 0 then eval 1 (Generic.packResult model (out := word) second) mem
      else eval 0 (encodeTuple model (pair (p.update.eval first second) first)) mem := by
  refine ⟨header_activation p fr first second mem hfirst hsecond, ?_⟩
  have run := Generic.header_eval (graph p) model input (pair first second) mem
  rw [native_step] at run
  by_cases halt : p.guardWord first second = 0
  · simp only [ite_eq_left halt] at run ⊢
    exact run
  · simp only [ite_eq_right halt] at run ⊢
    exact run

theorem feedback_slot_transfer_iff (p : Profile) (order : Fin 2 ≃ Generic.HeaderIncoming (graph p))
    (input : WordTuple 2) (first second : Word) {env : Env (Atom model)}
    (matched : let args := appendTuple (pair first second) input
      LayoutMatch model (Generic.headerLayout (graph p)) env args
        ((graph p).header.eval model args PUnit.unit))
    (start finish : Memory) (label : Nat) (payload : Value (Atom model)) :
    Eval (instruction model) (extend env .unit)
        (terminatorRegion (Generic.slotBranch (graph p) order
          (order.symm (Generic.headerIncoming (graph p) .backedge))))
        start label payload finish ↔
      label = 0 ∧ payload = encodeTuple model (pair (p.update.eval first second) first) ∧ finish = start := by
  rw [Generic.slot_branch_roundtrip]
  change Eval (instruction model) (extend env .unit)
    (.br (Generic.edge (graph p) .backedge).target (Generic.edge (graph p) .backedge).argument)
    start label payload finish ↔ _
  rw [PhiView.latch_eq_transfer (instruction model) (Generic.phiView (graph p)),
    Generic.feedback_latch (graph p) model input (pair first second) matched,
    feedback_latch p input first second]
  rfl

theorem returns_iff {g : Native} {targets : Checked.Phi.Targets} (accepted : lowerChecked g = some targets)
    (input : WordTuple 2) (initial final : Memory) (returned : List Word) :
    targets.1.oracle 0 (words input) initial returned final ↔
      ∃ value : Word, returned = [value] ∧
        Eval (instruction model) (inputEnv model input) targets.2
          initial 0 (Generic.packResult model (out := word) value) final := by
  obtain ⟨⟨p, rfl⟩, _, rfl⟩ := (lowerChecked_eq_some_iff g targets).mp accepted
  rw [rtl_returns_iff]
  constructor
  · rintro ⟨value, source, rfl, memory⟩
    subst final
    exact ⟨value, rfl, (Generic.returns_iff (graph p) model input initial value).mp source⟩
  · rintro ⟨value, rfl, run⟩
    obtain ⟨observed, source, _, payload, memory⟩ :=
      (Generic.lower_eval_iff (graph p) model input initial final 0
        (Generic.packResult model (out := word) value)).mp run
    have same : value = observed := encode_injective model (sort := word) (Value.pair.inj payload).1
    exact ⟨observed, source, congrArg (fun word => [word]) same, memory⟩

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Proofs

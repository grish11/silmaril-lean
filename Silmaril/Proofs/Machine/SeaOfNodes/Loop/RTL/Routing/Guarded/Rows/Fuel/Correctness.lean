module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Thms
public import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Fuel.Thms
import Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Thms

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Proofs

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (Reg model word)
open Silmaril.SSA.SeaOfNodes.Loop (Graph appendTuple)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (encode_injective inputEnv instruction)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

variable {arity : Nat} (p : Plan arity)

private theorem next_matches (input old : WordTuple arity) (fr : Frame Reg)
    (agree : ArgsMatch fr (appendTuple old input)) :
    ArgsMatch (bindWords arity (p.testFrame fr old) (p.nextBank input old))
      (appendTuple (p.nextBank input old) input) :=
  bank_matches_at (input_matches_at (testFrame_args p input old fr agree)) (p.nextBank input old)

private theorem exit_run (old : WordTuple arity) (fr : Frame Reg) (mem : Memory) (extra : Nat) :
    run (lowerBank p.graph) (extra + 1)
      ⟨⟨0, 2, 0⟩, (p.testFrame fr old).set .phi (p.exitValue old), [], mem⟩ =
      .returned [p.exitValue old] mem := rfl

private theorem header_fuel_sound (input : WordTuple arity) (initial final : Memory)
    (returned : List Word) (fuel : Nat) (old : WordTuple arity) (fr : Frame Reg)
    (agree : ArgsMatch fr (appendTuple old input))
    (observed : run (lowerBank p.graph) fuel ⟨⟨0, 1, 0⟩, fr, [], initial⟩ = .returned returned final) :
    ∃ count value, p.graph.ReturnsAfter model input count old value ∧
      p.activationSteps * (count + 1) + 1 ≤ fuel ∧ returned = [value] ∧ final = initial := by
  induction fuel using Nat.strongRecOn generalizing fr old with
  | ind fuel ih =>
    obtain ⟨remaining, spent, rest⟩ :=
      run_after_prefix (header_activation_steps p input old fr initial agree) observed
    have branch := native_step p input old fr agree
    by_cases halt : p.guardWord old = 0
    · rw [Plan.successor, ite_eq_left halt] at rest
      cases remaining with
      | zero => cases rest
      | succ extra =>
        rw [exit_run] at rest
        obtain ⟨rfl, rfl⟩ := Result.returned.inj rest
        exact ⟨0, p.exitValue old, .exit (branch.trans (ite_eq_left halt)),
          by simp only [Nat.zero_add, Nat.mul_one]; omega, rfl, rfl⟩
    · rw [Plan.successor, ite_eq_right halt] at rest
      have shorter : remaining < fuel := by
        have positive : 0 < p.activationSteps := by simp [Plan.activationSteps]
        omega
      obtain ⟨count, value, source, enough, same, mem⟩ :=
        ih remaining shorter (p.nextBank input old) _ (next_matches p input old fr agree) rest
      refine ⟨count + 1, value, .backedge (branch.trans (ite_eq_right halt)) source, ?_, same, mem⟩
      rw [Nat.mul_succ]
      omega

private theorem header_fuel_complete (input : WordTuple arity) (initial : Memory)
    {count : Nat} {old : WordTuple arity} {value : Word}
    (source : p.graph.ReturnsAfter model input count old value) :
    ∀ (fr : Frame Reg), ArgsMatch fr (appendTuple old input) →
      ∀ fuel, p.activationSteps * (count + 1) + 1 ≤ fuel →
      run (lowerBank p.graph) fuel ⟨⟨0, 1, 0⟩, fr, [], initial⟩ = .returned [value] initial := by
  refine Graph.ReturnsAfter.rec (g := p.graph) (m := model) (input := input)
    (motive := fun count old value _ => ∀ (fr : Frame Reg), ArgsMatch fr (appendTuple old input) →
      ∀ fuel, p.activationSteps * (count + 1) + 1 ≤ fuel →
      run (lowerBank p.graph) fuel ⟨⟨0, 1, 0⟩, fr, [], initial⟩ = .returned [value] initial) ?_ ?_ source
  · intro old value selected fr agree fuel enough
    have branch := (native_step p input old fr agree).symm.trans selected
    have halt : p.guardWord old = 0 := by
      by_contra taken
      rw [ite_eq_right taken] at branch
      cases branch
    rw [ite_eq_left halt] at branch
    obtain rfl := Sum.inl.inj branch
    have activation := header_activation_steps p input old fr initial agree
    rw [Plan.successor, ite_eq_left halt] at activation
    simp only [Nat.zero_add, Nat.mul_one] at enough
    let extra := fuel - (p.activationSteps + 1)
    have spent : fuel = p.activationSteps + (extra + 1) := by dsimp [extra]; omega
    rw [spent, run_through_prefix activation, exit_run]
  · intro count old next value selected _ ih fr agree fuel enough
    have branch := (native_step p input old fr agree).symm.trans selected
    have taken : p.guardWord old ≠ 0 := by
      intro halt
      rw [ite_eq_left halt] at branch
      cases branch
    rw [ite_eq_right taken] at branch
    obtain rfl := Sum.inr.inj branch
    have activation := header_activation_steps p input old fr initial agree
    rw [Plan.successor, ite_eq_right taken] at activation
    rw [Nat.mul_succ] at enough
    let remaining := fuel - p.activationSteps
    have spent : fuel = p.activationSteps + remaining := by dsimp [remaining]; omega
    have bound : p.activationSteps * (count + 1) + 1 ≤ remaining := by dsimp [remaining]; omega
    rw [spent, run_through_prefix activation]
    exact ih _ (next_matches p input old fr agree) remaining bound

theorem runMain_fuel_iff (input : WordTuple arity) (initial final : Memory)
    (returned : List Word) (fuel : Nat) :
    (lowerBank p.graph).runMain fuel 0 (words input) initial = .returned returned final ↔
      ∃ count value, p.graph.ReturnsAfter model input count (p.graph.initial model input) value ∧
        p.rtlFuel count ≤ fuel ∧ returned = [value] ∧ final = initial := by
  let fr := bindWords 0 Frame.empty input
  let old := p.graph.initial model input
  have start : (lowerBank p.graph).start 0 (words input) initial = some ⟨⟨0, 0, 0⟩, fr, [], initial⟩ := by
    change ((Frame.empty.writeAll (paramRegs 0 arity) (words input)).map
      (fun regs => (⟨⟨0, 0, 0⟩, regs⟩ : Point × Frame Reg))).map
        (fun entered => (⟨entered.1, entered.2, [], initial⟩ : State Reg)) = _
    rw [bindWords_write]
    rfl
  have args := bindWords_args input
  have entryStep := step_bank_entry p.graph input fr [] initial args
  have agree := bank_matches_at args old
  cases fuel with
  | zero =>
    simp only [Prog.runMain, start, run, reduceCtorEq, false_iff]
    rintro ⟨count, _, _, enough, _, _⟩
    simp [Plan.rtlFuel] at enough
  | succ fuel =>
    simp only [Prog.runMain, start, run, entryStep]
    constructor
    · intro observed
      obtain ⟨count, value, source, enough, same, mem⟩ :=
        header_fuel_sound p input initial final returned fuel old _ agree observed
      exact ⟨count, value, source, by unfold Plan.rtlFuel; omega, same, mem⟩
    · rintro ⟨count, value, source, enough, rfl, memory⟩
      subst final
      exact header_fuel_complete p input initial source _ agree fuel (by unfold Plan.rtlFuel at enough; omega)

theorem rtl_returns_iff (input : WordTuple arity) (initial final : Memory) (returned : List Word) :
    (lowerBank p.graph).oracle 0 (words input) initial returned final ↔
      ∃ value : Word, p.graph.Returns model input value ∧ returned = [value] ∧ final = initial := by
  constructor
  · rintro ⟨start, started, finish, path, observed⟩
    obtain ⟨fuel, result⟩ := fuel_of_steps path observed
    have whole : (lowerBank p.graph).runMain fuel 0 (words input) initial = .returned returned final := by
      simpa [Prog.runMain, started] using result
    obtain ⟨count, value, source, _, same, mem⟩ := (runMain_fuel_iff p input initial final returned fuel).mp whole
    exact ⟨value, ⟨count, source⟩, same, mem⟩
  · rintro ⟨value, ⟨count, source⟩, rfl, memory⟩
    subst final
    have whole := (runMain_fuel_iff p input initial initial [value] (p.rtlFuel count)).mpr
      ⟨count, value, source, Nat.le_refl _, rfl, rfl⟩
    unfold Prog.runMain at whole
    split at whole
    · exact ⟨_, by assumption, run_returned whole⟩
    · cases whole

private theorem budget_mono (count budget : Nat) :
    p.rtlFuel count ≤ p.rtlFuel budget ↔ count ≤ budget := by
  have positive : 0 < p.activationSteps := by simp [Plan.activationSteps]
  simp only [Plan.rtlFuel, Nat.add_le_add_iff_right, Nat.mul_le_mul_left_iff positive]

theorem bounded_returns_iff (input : WordTuple arity) (initial final : Memory)
    (returned : List Word) (budget : Nat) :
    (lowerBank p.graph).runMain (p.rtlFuel budget) 0 (words input) initial = .returned returned final ↔
      ∃ value : Word, Generic.Fuel.run model (inputEnv model input) (budget + 1) (Generic.lower p.graph) =
        some (0, Generic.packResult model (out := word) value) ∧
        returned = [value] ∧ final = initial := by
  rw [runMain_fuel_iff, Generic.Fuel.run_succ]
  constructor
  · rintro ⟨count, value, source, enough, same, mem⟩
    have evaluated := (p.graph.evalBackedges_eq_some_iff model input value budget).mpr
      ⟨count, (budget_mono p count budget).mp enough, source⟩
    exact ⟨value, by rw [evaluated]; rfl, same, mem⟩
  · rintro ⟨value, evaluated, same, mem⟩
    cases source : p.graph.evalBackedges model budget input with
    | none => rw [source] at evaluated; cases evaluated
    | some observed =>
      rw [source] at evaluated
      have eq : Generic.packResult model (out := word) observed = Generic.packResult model (out := word) value :=
        congrArg Prod.snd (Option.some.inj evaluated)
      have wordEq : observed = value := encode_injective model (sort := word) (Value.pair.inj eq).1
      subst observed
      obtain ⟨count, enough, returns⟩ := (p.graph.evalBackedges_eq_some_iff model input value budget).mp source
      exact ⟨count, value, returns, (budget_mono p count budget).mpr enough, same, mem⟩

theorem bounded_absence_iff (input : WordTuple arity) (initial : Memory) (budget : Nat) :
    ((lowerBank p.graph).runMain (p.rtlFuel budget) 0 (words input) initial).returnedValues? = none ↔
      Generic.Fuel.run model (inputEnv model input) (budget + 1) (Generic.lower p.graph) = none := by
  constructor
  · intro absent
    have ssa := Generic.Fuel.run_succ p.graph model input budget
    cases source : p.graph.evalBackedges model budget input with
    | none => simpa only [source, Option.map_none] using ssa
    | some result =>
      have typed : Generic.Fuel.run model (inputEnv model input) (budget + 1) (Generic.lower p.graph) =
          some (0, Generic.packResult model (out := word) result) := by
        rw [ssa, source]
        rfl
      have machine := (bounded_returns_iff p input initial initial [result] budget).mpr ⟨result, typed, rfl, rfl⟩
      rw [machine] at absent
      cases absent
  · intro absent
    cases result : (lowerBank p.graph).runMain (p.rtlFuel budget) 0 (words input) initial with
    | returned words final =>
      obtain ⟨word, typed, _, _⟩ := (bounded_returns_iff p input initial final words budget).mp result
      rw [absent] at typed
      cases typed
    | running _ | trapped _ | stuck => rfl

theorem returns_iff {spec : Spec} {targets : Checked.Phi.Targets}
    (accepted : lowerChecked arity spec = some targets) (input : WordTuple arity)
    (initial final : Memory) (returned : List Word) :
    targets.1.oracle 0 (words input) initial returned final ↔
      ∃ value : Word, returned = [value] ∧
        Eval (instruction model) (inputEnv model input) targets.2
          initial 0 (Generic.packResult model (out := word) value) final := by
  obtain ⟨plan, _, _, rfl⟩ := (lowerChecked_eq_some_iff arity spec targets).mp accepted
  rw [rtl_returns_iff]
  constructor
  · rintro ⟨value, native, rfl, mem⟩
    subst final
    exact ⟨value, rfl, (Generic.returns_iff plan.graph model input initial value).mp native⟩
  · rintro ⟨value, rfl, observed⟩
    obtain ⟨result, native, _, payload, mem⟩ :=
      (Generic.lower_eval_iff plan.graph model input initial final 0
        (Generic.packResult model (out := word) value)).mp observed
    have same : value = result := encode_injective model (sort := word) (Value.pair.inj payload).1
    exact ⟨result, native, congrArg (fun v => [v]) same, mem⟩

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Proofs

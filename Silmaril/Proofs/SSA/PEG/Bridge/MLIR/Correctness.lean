module

public import Silmaril.SSA.PEG.Bridge.MLIR.Defs
public import Silmaril.SSA.PEG.Bridge.RVSDG.Thms
public import Silmaril.SSA.RVSDG.MLIR.Regionless.Thms

public section

namespace Silmaril.SSA.PEG.Bridge.Proofs

open RVSDG (Tuple)
open Silmaril.SSA.RVSDG.MLIR

variable {Data : Type} {P : InstructionSet.{0,0} Data}
variable {params results : List (Ty Data)} {n : Nat}

private theorem pullback_run_eq (m : TotalModel P) :
    @((profileMap P).pullback m.toMLIR).run = @m.toRVSDG.run := by
  funext ins outs opcode input
  cases opcode with
  | @apply ins out op =>
    let args : Tuple m.toRVSDG.Val (valuePorts ins) := input
    let eval (xs : Tuple m.toRVSDG.Val (valuePorts ins)) :
        Tuple m.toRVSDG.Val (valuePorts [out]) := .cons (op.eval m (fromPorts ins xs)) .nil
    let round := Regionless.of_toAssignment ins args
    change Regionless.ofAssignment [out] (Regionless.toAssignment [out]
      (eval (Regionless.ofAssignment ins (Regionless.toAssignment ins args)))) = eval args
    exact (Regionless.of_toAssignment [out] _).trans (congrArg eval round)

theorem pullback_toMLIR (m : TotalModel P) :
    (profileMap P).pullback m.toMLIR = m.toRVSDG :=
  congrArg (RVSDG.Model.mk m.toPEG.Value (fun _ => PEmpty)) (pullback_run_eq m)

theorem mlir_correct (g : Graph P params results n 0) (ordered : Ordered g)
    (m : TotalModel P) (env : Tuple m.toPEG.Value params) (idx : Index 0)
    (wf : WellFounded g.Demand) :
    g.observe m.toPEG (g.denote m.toPEG env wf) idx =
      (fromPorts results (Regionless.ofAssignment (F := m.toRVSDG.Val) results (fun i =>
        (translateMLIR g ordered i).denote m.toMLIR
          (Regionless.toAssignment params (toPorts (F := m.toRVSDG.Val) env))))).map (fun _ => some) := by
  let input := toPorts (F := m.toRVSDG.Val) env
  let run := (translate g ordered).2.run m.toRVSDG input
  have components :
      (fun i => (translateMLIR g ordered i).denote m.toMLIR
        (Regionless.toAssignment params input)) = Regionless.toAssignment results run := by
    funext i
    have h := Regionless.denote_translateGraph (profileMap P) m.toMLIR
      (translate g ordered).2 (Regionless.toAssignment params input) i
    have round := Regionless.of_toAssignment params input
    have eqRun : (translate g ordered).2.run ((profileMap P).pullback m.toMLIR) input = run := by
      change (translate g ordered).2.run
        ⟨m.toPEG.Value, fun _ => PEmpty, @((profileMap P).pullback m.toMLIR).run⟩ input = run
      rw [pullback_run_eq m]
    exact h.trans (congrArg (fun xs => Regionless.toAssignment results xs i)
      ((congrArg ((translate g ordered).2.run ((profileMap P).pullback m.toMLIR)) round).trans eqRun))
  rw [components]
  exact (observe_translate g ordered m env idx wf).trans (congrArg
    (fun xs => (fromPorts results xs).map (fun _ => some))
    (Regionless.of_toAssignment results run).symm)

private theorem some_injective {F : Ty Data → Type} {ts : List (Ty Data)}
    {a b : Tuple F ts} (eq : a.map (fun _ => some) = b.map (fun _ => some)) : a = b := by
  induction a with
  | nil => cases b; rfl
  | cons x xs ih =>
    cases b with
    | cons y ys =>
      have head : some x = some y := congrArg (fun xs => xs.get .head) eq
      have tail : xs.map (fun _ => some) = ys.map (fun _ => some) :=
        congrArg (fun | .cons _ tail => tail) eq
      exact congrArg₂ Tuple.cons (Option.some.inj head) (ih tail)

theorem rvsdg_satisfaction (e : Equation P) (m : TotalModel P) :
    e.toRVSDG.toRVSDG.Holds m.toRVSDG ↔ e.Holds m := by
  constructor
  · intro target env idx
    rw [observe_translate e.lhs e.leftOrdered, observe_translate e.rhs e.rightOrdered]
    exact congrArg (fun xs => (fromPorts e.results xs).map (fun _ => some))
      (target (toPorts (F := m.toRVSDG.Val) env))
  · intro source input
    let env : Tuple m.toPEG.Value e.params := fromPorts e.params input
    have left := observe_translate e.lhs e.leftOrdered m env Fin.elim0 e.leftOrdered.demandWellFounded
    have right := observe_translate e.rhs e.rightOrdered m env Fin.elim0 e.rightOrdered.demandWellFounded
    have same := left.symm.trans ((source env Fin.elim0).trans right)
    have eq := congrArg (toPorts (F := m.toRVSDG.Val)) (some_injective same)
    have round : toPorts (F := m.toRVSDG.Val) env = input := to_fromPorts input
    change (translate e.lhs e.leftOrdered).2.run m.toRVSDG input =
      (translate e.rhs e.rightOrdered).2.run m.toRVSDG input
    simpa only [to_fromPorts, round] using eq

theorem mlir_satisfaction (e : Equation P) (m : TotalModel P) :
    e.toMLIR.Holds m.toMLIR ↔ e.Holds m := by
  rw [Equation.toMLIR, Regionless.satisfaction, pullback_toMLIR]
  exact rvsdg_satisfaction e m

end Silmaril.SSA.PEG.Bridge.Proofs

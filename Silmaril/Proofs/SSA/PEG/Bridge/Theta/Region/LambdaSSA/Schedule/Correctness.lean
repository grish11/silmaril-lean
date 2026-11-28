module

public import Silmaril.SSA.PEG.Bridge.Theta.Region.LambdaSSA.Schedule.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Thms
public import Silmaril.SSA.PEG.Bridge.RVSDG.Thms
public import Silmaril.SSA.PEG.Simple.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.Theta.Operational.Thms

public section

namespace Silmaril.SSA.PEG.Bridge.Theta.Region.LambdaSSA.Schedule.Proofs

open RVSDG (Port Tuple)
open RVSDG.LambdaSSA.Theta
open Isotope (Value)
open Isotope.LambdaSSA (Tm Region Ren)
open Isotope.LambdaSSA.Semantics (Env extend InstrDeterministic)
open Isotope.LambdaSSA.Semantics.Region (Eval)
open Simple.Revert.While.Region (Reads Schedule)

universe u

variable {Data : Type} {P : InstructionSet.{0,0} Data} {σ : Type u}
variable {carried vars outs ins : List (Ty Data)} {t : Ty Data} {n : Nat}
variable {g : Graph P carried [t] n 1}
variable {Γ labels : List (Code Data)}
variable (m : TotalModel P)

theorem instruction_deterministic : InstrDeterministic (instruction m (σ := σ)) := by
  intro op arg start a finishA b finishB ha hb
  obtain ⟨xs, rfl, rfl, rfl⟩ := ha
  obtain ⟨ys, same, rfl, rfl⟩ := hb
  have encoded := Operational.pack_injective (Region.model m) same
  have decoded := congrArg (fromPorts (F := (Region.model m).Val) op.inputs) encoded
  have sameArgs : xs = ys :=
    (from_toPorts (F := (Region.model m).Val) xs).symm.trans
      (decoded.trans (from_toPorts (F := (Region.model m).Val) ys))
  cases sameArgs
  exact ⟨rfl, rfl⟩

theorem field_hasType (p : Port vars t) {arg : Tm (Primitive P)}
    (typed : arg.HasType Γ (Packet vars)) :
    (field p arg).HasType Γ (.base (.value t)) := by
  induction p generalizing Γ arg with
  | head => exact .let₂ typed (.var rfl)
  | tail _ ih => exact .let₂ typed (ih (.var rfl))

theorem field_eval (p : Port vars t) {arg : Tm (Primitive P)} {env : Env (Atom m)}
    {state : σ} {store : Tuple m.toPEG.Value vars}
    (ran : Isotope.LambdaSSA.Semantics.Tm.Eval (instruction m) env arg state (pack m store) state) :
    Isotope.LambdaSSA.Semantics.Tm.Eval (instruction m) env (field p arg) state
      (.atom ⟨.value t, store.get p⟩) state := by
  induction p generalizing env arg with
  | head =>
    cases store
    exact .let₂ ran .var
  | tail p ih =>
    cases store
    exact .let₂ ran (ih .var)

theorem tupleTerm_hasType (layout : Layout P vars)
    (typed : layout.Typed Γ)
    (slots : Tuple (Port vars) ins) : (tupleTerm layout slots).HasType Γ (Packet ins) := by
  induction slots with
  | nil => exact .unit
  | cons p _ ih => exact .pair (typed _ p) ih

theorem tupleTerm_eval (layout : Layout P vars)
    (env : Env (Atom m)) (store : Tuple m.toPEG.Value vars) (state : σ)
    (aligned : layout.Evaluates m env store state)
    (slots : Tuple (Port vars) ins) :
    Isotope.LambdaSSA.Semantics.Tm.Eval (instruction m) env (tupleTerm layout slots) state
      (pack m (slots.map fun _ p => store.get p)) state := by
  induction slots with
  | nil => exact .unit
  | cons p _ ih => exact .pair (aligned _ p) ih

private theorem args_eval {scope : Tuple (Ref g.sort) vars} {refs : Tuple (Ref g.sort) ins}
    (reads : Reads scope refs) (store : Tuple m.toPEG.Value vars) :
    reads.args.eval m.toPEG store = some (reads.slots.map fun _ p => store.get p) := by
  induction reads with
  | nil => rfl
  | cons _ _ _ ih => simp [Reads.args, Reads.slots, Simple.Args.eval, Simple.Expr.evalLift, Tuple.map, ih]

theorem emit_hasType {roots : Tuple (Ref g.sort) outs} {scope : Tuple (Ref g.sort) vars}
    (schedule : Schedule g false roots scope) (layout : Layout P vars) (finish : Layout P outs → Region (Primitive P))
    (typed : layout.Typed Γ)
    (finishTyped : ∀ (Δ : List (Code Data)) (outputs : Layout P outs),
      outputs.Typed Δ →
      (finish outputs).HasType Δ labels) :
    (emit schedule layout finish).HasType Γ labels := by
  induction schedule generalizing Γ with
  | done reads =>
    exact finishTyped Γ _ (fun _ p => typed _ (reads.slots.get p))
  | bind _ op _ _ _ reads tail ih =>
    refine .let₁ (.op (tupleTerm_hasType layout typed reads.slots)) (ih layout.push finish ?_ finishTyped)
    intro _ p
    cases p with
    | head => exact .var rfl
    | tail p => exact (typed _ p).rename (Ren.wk _ _)
  | branch enabled => cases enabled

theorem emit_eval {roots : Tuple (Ref g.sort) outs} {scope : Tuple (Ref g.sort) vars}
    (schedule : Schedule g false roots scope) (layout : Layout P vars) (finish : Layout P outs → Region (Primitive P))
    (env : Env (Atom m)) (store : Tuple m.toPEG.Value vars) (output : Tuple m.toPEG.Value outs)
    (state : σ) (label : Nat) (result : Value (Atom m))
    (aligned : layout.Evaluates m env store state)
    (ran : schedule.lower.runLoopFree m.toPEG store = some output)
    (finishEval : ∀ (outputs : Layout P outs) (localEnv : Env (Atom m)),
      outputs.Evaluates m localEnv output state →
      Eval (instruction m) localEnv (finish outputs) state label result state) :
    Eval (instruction m) env (emit schedule layout finish) state label result state := by
  induction schedule generalizing env with
  | done reads =>
    have projected : reads.slots.map (fun _ p => store.get p) = output := Option.some.inj ran
    refine finishEval _ env (fun t p => ?_)
    rw [← projected, Simple.get_map]
    exact aligned t (reads.slots.get p)
  | bind i op refs fresh row reads tail ih =>
    let args := reads.slots.map fun _ p => store.get p
    have argEval := tupleTerm_eval m layout env store state aligned reads.slots
    have callEval : Isotope.LambdaSSA.Semantics.Tm.Eval (instruction m) env
        (.op (.call op) (tupleTerm layout reads.slots)) state
        (.atom ⟨.value (g.sort i), m.run op args⟩) state :=
      .op argEval ⟨args, rfl, rfl, rfl⟩
    have rest : tail.lower.runLoopFree m.toPEG (.cons (m.run op args) store) = some output := by
      simpa only [Schedule.lower, Simple.Stmt.runLoopFree, Simple.Expr.eval,
        Simple.Expr.evalLift, args_eval m reads store, TotalModel.toPEG, Option.elim,
        Option.map_some, Option.bind] using ran
    refine .let₁ callEval (ih layout.push finish _ (.cons (m.run op args) store) output ?_ rest finishEval)
    intro _ p
    cases p with
    | head => exact .var
    | tail p => exact (aligned _ p).rename (fun _ => rfl)
  | branch enabled => cases enabled

end Silmaril.SSA.PEG.Bridge.Theta.Region.LambdaSSA.Schedule.Proofs

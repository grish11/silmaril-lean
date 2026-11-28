module

public import Silmaril.SSA.PEG.Bridge.Theta.Region.LambdaSSA.Schedule.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Thms
import Silmaril.Proofs.SSA.PEG.Bridge.Theta.Region.LambdaSSA.Schedule.Correctness

public section

namespace Silmaril.SSA.PEG.Bridge.Theta.Region.LambdaSSA

open RVSDG (Port Tuple)
open Isotope (Value)
open Isotope.LambdaSSA (Tm Region)
open Isotope.LambdaSSA.Semantics (Env InstrDeterministic)
open Isotope.LambdaSSA.Semantics.Region (Eval)
open Simple.Revert.While.Region (Schedule)

universe u

variable {Data : Type} {P : InstructionSet.{0,0} Data} {σ : Type u}
variable {carried vars outs ins : List (Ty Data)} {t : Ty Data} {n : Nat}
variable {g : Graph P carried [t] n 1}
variable {Γ labels : List (Code Data)}
variable (m : TotalModel P)

theorem instruction_deterministic : InstrDeterministic (instruction m (σ := σ)) :=
  Schedule.Proofs.instruction_deterministic m

namespace Schedule

theorem field_hasType (p : Port vars t) {arg : Tm (Primitive P)}
    (typed : arg.HasType Γ (Packet vars)) :
    (field p arg).HasType Γ (.base (.value t)) :=
  Proofs.field_hasType p typed

theorem field_eval (p : Port vars t) {arg : Tm (Primitive P)} {env : Env (Atom m)}
    {state : σ} {store : Tuple m.toPEG.Value vars}
    (ran : Isotope.LambdaSSA.Semantics.Tm.Eval (instruction m) env arg state (pack m store) state) :
    Isotope.LambdaSSA.Semantics.Tm.Eval (instruction m) env (field p arg) state
      (.atom ⟨.value t, store.get p⟩) state :=
  Proofs.field_eval m p ran

theorem tupleTerm_hasType (layout : Layout P vars) (typed : layout.Typed Γ)
    (slots : Tuple (Port vars) ins) : (tupleTerm layout slots).HasType Γ (Packet ins) :=
  Proofs.tupleTerm_hasType layout typed slots

theorem tupleTerm_eval (layout : Layout P vars) (env : Env (Atom m))
    (store : Tuple m.toPEG.Value vars) (state : σ) (aligned : layout.Evaluates m env store state)
    (slots : Tuple (Port vars) ins) :
    Isotope.LambdaSSA.Semantics.Tm.Eval (instruction m) env (tupleTerm layout slots) state
      (pack m (slots.map fun _ p => store.get p)) state :=
  Proofs.tupleTerm_eval m layout env store state aligned slots

theorem emit_hasType {roots : Tuple (Ref g.sort) outs} {scope : Tuple (Ref g.sort) vars}
    (schedule : Schedule g false roots scope) (layout : Layout P vars) (finish : Layout P outs → Region (Primitive P))
    (typed : layout.Typed Γ)
    (finishTyped : ∀ Δ (outputs : Layout P outs), outputs.Typed Δ → (finish outputs).HasType Δ labels) :
    (emit schedule layout finish).HasType Γ labels :=
  Proofs.emit_hasType schedule layout finish typed finishTyped

/-- Checked bindings evaluate in emission order. The continuation receives
terms evaluating to the projected source slots in order. -/
theorem emit_eval {roots : Tuple (Ref g.sort) outs} {scope : Tuple (Ref g.sort) vars}
    (schedule : Schedule g false roots scope) (layout : Layout P vars) (finish : Layout P outs → Region (Primitive P))
    (env : Env (Atom m)) (store : Tuple m.toPEG.Value vars) (output : Tuple m.toPEG.Value outs)
    (state : σ) (label : Nat) (result : Value (Atom m)) (aligned : layout.Evaluates m env store state)
    (ran : schedule.lower.runLoopFree m.toPEG store = some output)
    (finishEval : ∀ (outputs : Layout P outs) localEnv, outputs.Evaluates m localEnv output state →
      Eval (instruction m) localEnv (finish outputs) state label result state) :
    Eval (instruction m) env (emit schedule layout finish) state label result state :=
  Proofs.emit_eval m schedule layout finish env store output state label result aligned ran finishEval

end Schedule

end Silmaril.SSA.PEG.Bridge.Theta.Region.LambdaSSA

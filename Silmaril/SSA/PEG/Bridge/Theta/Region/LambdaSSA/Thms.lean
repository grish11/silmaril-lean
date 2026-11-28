module

public import Silmaril.SSA.PEG.Bridge.Theta.Region.LambdaSSA.Defs
public import Silmaril.SSA.PEG.Bridge.Theta.Region.LambdaSSA.Schedule.Thms
public import Silmaril.SSA.PEG.Bridge.Theta.Region.Tuple.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.Theta.Operational.Thms
import Silmaril.Proofs.SSA.PEG.Bridge.Theta.Region.LambdaSSA.Correctness

public section

namespace Silmaril.SSA.PEG.Bridge.Theta.Region.LambdaSSA

open RVSDG (Port Tuple)
open Silmaril.SSA.PEG.Bridge.Theta.Region.Ordered (Bundle)
open RVSDG.LambdaSSA.Theta
open Isotope (Value)
open Isotope.LambdaSSA.Semantics (Env extend)
open Isotope.LambdaSSA.Semantics.Region (Eval)

universe u

variable {Data : Type} {P : InstructionSet.{0,0} Data} {σ : Type u}
variable {carried : List (Ty Data)} {result : Ty Data} {n : Nat}
variable {g : Graph P carried carried n 1} {slot : Port carried result} {allowInvariant : Bool}
variable (b : Bundle g slot allowInvariant) (m : TotalModel P)
variable (input : Tuple m.toPEG.Value carried)

theorem lower_hasType : (lower b).HasType [Packet carried] [Packet carried] :=
  Proofs.lower_hasType b

/-- One native header visit reproduces the selector and ordered payload of
one numbered θ body activation, preserving ambient state. -/
theorem header_eval (env : Env (Atom m))
    (input output : Tuple (Region.model m).Val (valuePorts carried)) (again : Bool)
    (body : b.compile.body.run (Region.model m) input = RVSDG.Theta.bodyResult (Region.model m) again output)
    (state : σ) :
    Eval (instruction m) (extend env (Operational.pack (Region.model m) input)) (header b)
      state (if again then 0 else 1) (Operational.pack (Region.model m) output) state :=
  Proofs.header_eval b m env input output again body state

/-- Compare every successful λSSA execution to a finite numbered θ return. -/
theorem lower_eval_iff_returns (start finish : σ) (label : Nat) (payload : Value (Atom m)) :
    Eval (instruction m) (Operational.inputEnv (Region.model m) (encode m input)) (lower b)
      start label payload finish ↔
      ∃ output, b.compile.Returns (Region.model m) (encode m input) output ∧
        label = 0 ∧ payload = Operational.pack (Region.model m) output ∧ finish = start :=
  Proofs.lower_eval_iff_returns b m input start finish label payload

/-- Every finite target execution has the same ordered defined PEG result,
with the unique external exit and unchanged ambient state, and conversely. -/
theorem lower_eval_iff
    (neg : ∀ flag : Bool, m.run b.scalar.descriptor.negate (.cons ⟨flag⟩ .nil) = ⟨!flag⟩)
    (idx : Index 1) (start finish : σ) (label : Nat) (payload : Value (Operational.Atom (Region.model m))) :
    Eval (instruction m)
      (Operational.inputEnv (Region.model m) (encode m input)) (lower b) start label payload finish ↔
      ∃ output : Tuple m.toPEG.Value carried,
        g.observe m.toPEG (g.denote m.toPEG input b.demandWellFounded) idx = output.map (fun _ => some) ∧
        label = 0 ∧ payload = Operational.pack (Region.model m) (encode m output) ∧ finish = start :=
  Proofs.lower_eval_iff b m input neg idx start finish label payload

/-- A finite CFG evaluation recovers the common PEG pass count and all
defined eval prefixes from the single checked loop trace. -/
theorem firstExit_of_eval
    (neg : ∀ flag : Bool, m.run b.scalar.descriptor.negate (.cons ⟨flag⟩ .nil) = ⟨!flag⟩)
    (idx : Index 1) (output : Tuple m.toPEG.Value carried) (state : σ)
    (ran : Eval (instruction m)
      (Operational.inputEnv (Region.model m) (encode m input)) (lower b)
      state 0 (Operational.pack (Region.model m) (encode m output)) state) :
    ∃ (k : Nat) (final : Tuple m.toPEG.Value (.bool :: carried)),
      carriedValues final = output ∧
      b.scalar.TraceObservation m.toPEG (g.denote m.toPEG input b.demandWellFounded) idx k final :=
  Proofs.firstExit_of_eval b m input neg idx output state ran

/-- The bounded runner finds the Figure 11 tuple exactly when a sufficiently
large finite bound exists. Fuel exhaustion is a bounded outcome. -/
theorem exists_runFuel_iff_observe
    (neg : ∀ flag : Bool, m.run b.scalar.descriptor.negate (.cons ⟨flag⟩ .nil) = ⟨!flag⟩)
    (idx : Index 1) (output : Tuple m.toPEG.Value carried) :
    (∃ fuel, runFuel b m fuel input = some output) ↔
      g.observe m.toPEG (g.denote m.toPEG input b.demandWellFounded) idx = output.map (fun _ => some) :=
  Proofs.exists_runFuel_iff_observe b m input neg idx output

end Silmaril.SSA.PEG.Bridge.Theta.Region.LambdaSSA

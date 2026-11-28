module

public import Silmaril.SSA.RVSDG.LambdaSSA.Theta.Operational.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Theta.Operational.Correctness

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Theta.Operational

open Isotope (Value)
open Isotope.LambdaSSA (Region)
open Isotope.LambdaSSA.Semantics (Env InstrDeterministic)
open Isotope.LambdaSSA.Semantics.Region (Eval)

universe u v w x y

variable {V S : Type u} {Op : Dialect.{u,v} V S} {σ : Type x}
variable {carried : List (PortType V S)} {sigs : List (List (PortType V S))}
variable (m : Model.{u,v,w} Op) (g : RVSDG.Theta.Graph Op carried sigs)

theorem lower_hasType : (lower g).HasType [Packed carried] [Packed carried] :=
  LambdaSSA.Theta.regionTyping (step g)

theorem pack_injective {ports : List (PortType V S)} :
    Function.Injective (pack m (ports := ports)) :=
  Proofs.pack_injective m

theorem split_bodyResult (again : Bool) (output : Tuple m.Val carried) :
    split m (RVSDG.Theta.bodyResult m again output) = (again, output) :=
  Proofs.split_bodyResult m again output

/-- The block's internal labels are zero for feedback and one for exit. -/
theorem block_eval (env : Env (Atom m)) (input output : Tuple m.Val carried)
    (again : Bool) (body : g.body.run m input = RVSDG.Theta.bodyResult m again output) (start : σ) :
    Eval (instruction m) (Isotope.LambdaSSA.Semantics.extend env (pack m input)) (LambdaSSA.Theta.block (step g).op)
      start (if again then 0 else 1) (pack m output) start :=
  Proofs.block_eval m g env input output again body start

/-- A deterministic λSSA header implementing one numbered θ activation
also implements its finite iteration when placed in the one-block CFG. -/
theorem loop_eval_iff {Φ : Type y} {header : Region Φ}
    {instr : Φ → Value (Atom m) → σ → Value (Atom m) → σ → Prop}
    (headerEval : ∀ (env : Env (Atom m)) (input output : Tuple m.Val carried) (again : Bool),
      g.body.run m input = RVSDG.Theta.bodyResult m again output → ∀ state : σ,
      Eval instr (Isotope.LambdaSSA.Semantics.extend env (pack m input)) header
        state (if again then 0 else 1) (pack m output) state)
    (deterministic : InstrDeterministic instr)
    (input : Tuple m.Val carried) (start finish : σ) (label : Nat) (payload : Value (Atom m)) :
    Eval instr (inputEnv m input) (loop header) start label payload finish ↔
      ∃ output, g.Returns m input output ∧ label = 0 ∧ payload = pack m output ∧ finish = start :=
  Proofs.loop_eval_iff m g headerEval deterministic input start finish label payload

/-- Compare every finite observation of the actual λSSA CFG with a
numbered θ return. Its sole external label is zero. -/
theorem lower_eval_iff (input : Tuple m.Val carried) (start finish : σ)
    (label : Nat) (payload : Value (Atom m)) :
    Eval (instruction m) (inputEnv m input) (lower g) start label payload finish ↔
      ∃ output, g.Returns m input output ∧ label = 0 ∧ payload = pack m output ∧ finish = start :=
  Proofs.lower_eval_iff m g input start finish label payload

theorem returns_iff_runFuel (input output : Tuple m.Val carried) :
    g.Returns m input output ↔ ∃ fuel, runFuel m g fuel input = some output :=
  Proofs.returns_iff_runFuel m g input output

/-- A finite result can be found with some finite bound in the typed packet
runner, and every successful bounded run gives an actual CFG evaluation. -/
theorem eval_iff_runFuel (input output : Tuple m.Val carried) (start : σ) :
    Eval (instruction m) (inputEnv m input) (lower g) start 0 (pack m output) start ↔
      ∃ fuel, runFuel m g fuel input = some output := by
  rw [lower_eval_iff, ← returns_iff_runFuel]
  exact ⟨fun ⟨_, ran, _, same, _⟩ => pack_injective m same ▸ ran,
    fun ran => ⟨output, ran, rfl, rfl, rfl⟩⟩

end Silmaril.SSA.RVSDG.LambdaSSA.Theta.Operational

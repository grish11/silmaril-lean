module

public import Silmaril.Wasm.Region.Operational.Defs
import Silmaril.Proofs.Wasm.Region.Operational

@[expose] public section
namespace Silmaril.Wasm.Region

/-- Actual block-machine steps, including oracle-answered calls, are covered.
The frame invariant and successful lookup are explicit. The existing CFG's
Core adequacy theorems retain their fragment/callee-adequacy assumptions. -/
theorem operational_step {H : Type} {P : Numerics.Profile} {host : Execution.Core.HostSemantics H}
    {C : Abstract.CallRel H} {body : Expr} {b : Cfg.BlockId} {s : Cfg.Segment}
    {st st' : Cfg.Machine.MState H}
    (lookup : Cfg.lookup body b = some s) (node : st.node = .block b)
    (inv : Cfg.Machine.MInv body st) (step : Cfg.Machine.MStepC P host C body st st') :
    (operationalTargets body b s).Allows st'.node := Proofs.operational_step lookup node inv step

/-- First-exit soundness for a proposed support, using the existing invariant
preservation theorem. Inventory coverage and outward allowances are explicit;
Top cannot discharge a finite closed region without further information. -/
theorem operational_sound {H : Type} {P : Numerics.Profile}
    {host : Execution.Core.HostSemantics H} {C : Abstract.CallRel H} {body : Expr}
    {A : Cfg.Machine.MState H → Prop} {U X : Cfg.Target → Prop}
    (admit : ∀ st, A st → Cfg.Machine.MInv body st)
    (covered : ∀ st : Cfg.Machine.MState H, Cfg.Machine.MInv body st → U st.node →
      ∃ b s, st.node = .block b ∧ Cfg.lookup body b = some s)
    (outward : ∀ b s, Cfg.lookup body b = some s → U (.block b) → ∀ t,
      (operationalTargets body b s).Allows t → ¬ U t → X t) :
    Silmaril.Semantics.Region.Sound (system P host C body) A U X :=
  Proofs.operational_sound admit covered outward

/-- Even a syntactically harmless root block permits operational traps without
a typing premise; an inner block does not guess its enclosing handler. -/
theorem root_return_allowance : operationalTargets [.return_] ⟨[], 0⟩ ⟨[], some .return_⟩ =
    .finite {.trap, .exit} := rfl

theorem nested_unknown (body : Expr) (k : Nat) (s : Cfg.Segment) :
    operationalTargets body ⟨[(k, 0)], 0⟩ s = .top := rfl

end Silmaril.Wasm.Region

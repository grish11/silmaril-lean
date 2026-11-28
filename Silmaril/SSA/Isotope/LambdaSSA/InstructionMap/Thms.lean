module

public import Silmaril.Raw.SSA.Isotope.LambdaSSA.InstructionMap
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.InstructionMap.Reflection

public section

namespace Silmaril.Isotope.LambdaSSA.Semantics

universe u v a s

variable {Φ : Type u} {Ψ : Type v} {α : Type a} {σ : Type s}
variable {instr : Φ → Value α → σ → Value α → σ → Prop}
variable {instr' : Ψ → Value α → σ → Value α → σ → Prop}

/-- Opcode relabelling preserves and reflects finite CFG evaluation when the
source instruction interpretation is the reduct. The map can identify opcodes. -/
theorem Region.Eval.mapInstr_iff (f : Φ → Ψ)
    (step : ∀ i input before output after,
      instr' (f i) input before output after ↔ instr i input before output after)
    {env : Env α} {r : LambdaSSA.Region Φ} {start finish : σ} {label : Nat} {value : Value α} :
    Eval instr' env (r.mapInstr f) start label value finish ↔ Eval instr env r start label value finish :=
  ⟨fun ran => InstructionMap.Proofs.region_reflect f (fun _ _ _ _ _ => (step ..).mp) ran r rfl,
    fun ran => ran.mapInstr f (fun _ _ _ _ _ => (step ..).mpr)⟩

end Silmaril.Isotope.LambdaSSA.Semantics

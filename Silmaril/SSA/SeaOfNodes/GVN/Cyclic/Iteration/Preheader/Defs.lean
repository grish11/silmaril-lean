module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Defs
public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader.Defs

/-! Repeat the preheader-seeded step on each restored native loop. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader

open Builder.Preheader (Native)
open Diamond (Ty ValueSort)
open Pure.SubZero (Opcode)

variable {inputs carried : List (ValueSort Unit)} {entrySigs headerSigs : List (List (Ty Unit))}
variable {out : ValueSort Unit}

/-- Each attempt prepares, builds, refines and checks restoration for the
current header using the existing preheader-seeded step. -/
def run (fuel : Nat) (loop : Native inputs carried entrySigs headerSigs out) :
    Result Opcode inputs carried entrySigs out :=
  runWith Builder.Preheader.optimize? fuel loop

/-- Expose one iteration over the current native loop. -/
theorem run_succ (fuel : Nat) (loop : Native inputs carried entrySigs headerSigs out) :
    run (fuel + 1) loop =
      match Builder.Preheader.optimize? loop with
      | none => ⟨⟨headerSigs, loop⟩, 0⟩
      | some next => ⟨(run fuel next.graph).rewrite, (run fuel next.graph).deletions + 1⟩ := by
  cases found : Builder.Preheader.optimize? loop <;> simp only [run, runWith, found]

/-- One unit of deletion fuel per binding in the original header. -/
def normalize (loop : Native inputs carried entrySigs headerSigs out) :
    Result Opcode inputs carried entrySigs out :=
  run headerSigs.length loop

end Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader

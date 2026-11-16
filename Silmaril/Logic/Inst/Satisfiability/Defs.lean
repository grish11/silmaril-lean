module

public import Silmaril.Logic.Institution.Room

/-! SAT and UNSAT for the existing model classes of institution rooms.
These definitions do not assume that a model exists, or that an external solver
is complete. A certificate contains a model and its proof, or a refutation. -/
@[expose] public section

namespace Silmaril.Logic.Institution.Room

universe w m₁ m₂
variable (R : Room.{w, m₁, m₂})

/-- One model satisfies every sentence of the theory at once. -/
def Satisfiable (Γ : Set R.Sen) : Prop := ∃ M, M ∈ R.modelsOf Γ

/-- No model satisfies every sentence of the theory. -/
def Unsatisfiable (Γ : Set R.Sen) : Prop := ¬ R.Satisfiable Γ

/-- Kernel-checkable evidence for either solver answer. No total decision
procedure is asserted; a producer may fail to supply either constructor. -/
inductive Certificate (Γ : Set R.Sen) where
  | sat (model : R.Mod) (holds : model ∈ R.modelsOf Γ)
  | unsat (refutes : R.Unsatisfiable Γ)

end Silmaril.Logic.Institution.Room

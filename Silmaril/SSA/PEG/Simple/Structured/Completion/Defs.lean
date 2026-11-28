module

public import Silmaril.SSA.PEG.Simple.Structured.Defs

/-! # Definedness along a compiled while prefix -/

@[expose] public section

namespace Silmaril.SSA.PEG.Simple.Structured

open RVSDG (Port Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data} {vars : List (Ty Data)} {t : Ty Data}

/-- Check that the complete body succeeds for exactly the requested number
of steps and that the guard is defined at each visited store, including the
last. The guard's Boolean value is left to the compiled first-pass proof. -/
def checkWhilePrefix (m : Interpretation.{u,v,w} P) (guard : Expr P vars .bool)
    (body : Stmt P false vars vars) : Nat → Tuple m.Value vars → Bool
  | 0, store => (guard.eval m store).isSome
  | k + 1, store =>
    (guard.eval m store).isSome &&
      match body.runLoopFree m store with
      | none => false
      | some next => checkWhilePrefix m guard body k next

/-- The shared pass row emitted for the top-level while. -/
def whilePass (guard : Expr P vars .bool) (body : Stmt P true vars vars)
    (ret : Port vars t) (neg : P [.bool] .bool) :
    Ref (translate (whileProgram guard body ret) neg).sort .count :=
  numberPort (passRef vars)

def readWhilePass (guard : Expr P vars .bool) (body : Stmt P true vars vars)
    (ret : Port vars t) (neg : P [.bool] .bool) (m : Interpretation.{u,v,w} P)
    (values : (translate (whileProgram guard body ret) neg).Valuation m)
    (i : Index (program (whileProgram guard body ret) neg).nodes.length) :
    Option (m.Value .count) :=
  let pass := whilePass guard body ret neg
  pass.read m.carrier (values (pass.id, i))

end Silmaril.SSA.PEG.Simple.Structured

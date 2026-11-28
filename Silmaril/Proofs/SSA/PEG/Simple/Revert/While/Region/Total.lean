module

public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Defs

public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Region.TotalProofs

open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params vars ins more : List (Ty Data)} {n l : Nat}
variable {m : Interpretation.{u,v,w} P}

private theorem args_defined {sort : Fin n → Ty Data} {scope : Tuple (Ref sort) vars}
    {refs : Tuple (Ref sort) ins} (reads : Reads scope refs) (store : Tuple m.Value vars) :
    ∃ args, reads.args.eval m store = some args := by
  induction reads with
  | nil => exact ⟨.nil, rfl⟩
  | cons p _ tail ih =>
    obtain ⟨args, ran⟩ := ih
    refine ⟨.cons (store.get p) args, ?_⟩
    simp only [Reads.args, Args.eval, Expr.evalLift, ran]

theorem primitive_schedule_total {result : Ty Data} {view : Graph P params [result] n l}
    {roots : Tuple (Ref view.sort) more} {scope : Tuple (Ref view.sort) vars}
    (code : Schedule view false roots scope)
    (total : ∀ {ins out} (op : P ins out) args, ∃ val, m.run op args = some val)
    (store : Tuple m.Value vars) : ∃ out, code.lower.runLoopFree m store = some out := by
  induction code with
  | done reads => exact ⟨_, rfl⟩
  | bind _ instr _ _ _ reads _ ih =>
    obtain ⟨args, ranArgs⟩ := args_defined reads store
    obtain ⟨val, ranOp⟩ := total instr args
    obtain ⟨out, ranTail⟩ := ih (.cons val store)
    refine ⟨out, ?_⟩
    simp only [Schedule.lower, Stmt.runLoopFree, Expr.eval, Expr.evalLift, ranArgs,
      Option.elim, ranOp, Option.map_some, Option.bind_some, ranTail]
  | branch enabled => contradiction

end Silmaril.SSA.PEG.Simple.Revert.While.Region.TotalProofs

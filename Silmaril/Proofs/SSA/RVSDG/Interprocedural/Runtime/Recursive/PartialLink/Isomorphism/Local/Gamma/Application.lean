module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Feedback
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Regions
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Environments

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Proofs

open Continuation.Partial
open Continuation.Descent (Pending)
open Isomorphism.Proofs (LocalsRelated read_same)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ids : GlobalRel}
variable {primitives : Primitives m σ} {mapping : Renaming}
variable {args outs captured : Ports (Ty V S)}
variable {sigsL sigsR : List (Ports (Ty V S))}
variable {fn : Function V S}

private theorem application_reaches {entry : Tuple m.Val args} {inputs : Wires args [] (fn.port :: fn.args)}
    {callee : m.Val fn.port} {arguments : Tuple m.Val fn.args} {store : σ}
    {target : Feedback.Restart m σ} {pending : Pending m target.carried fn.results}
    (selected : inputs.read entry PUnit.unit = .cons callee arguments)
    (ran : Feedback.Reaches primitives (.call callee arguments) store target pending) :
    Feedback.Reaches primitives (.node (applicationVertex fn inputs).kind (applicationVertex fn inputs).childSigs
      (fun i => i.elim0) (inputs.read entry PUnit.unit)) store target pending :=
  selected.symm ▸ Feedback.Reaches.apply (fn := fn) (cs := fun _ => []) (children := fun i => i.elim0) ran

theorem application
    {left : NestedTheta.Term (Instruction Op) (captured ++ fn.args) [] sigsL fn.results}
    {right : NestedTheta.Term (Instruction Op) (captured ++ fn.args) [] sigsR fn.results}
    (code : CodePair Op mapping left right) (respects : ActionsRespect primitives ids)
    (inputs : Wires args [] (fn.port :: fn.args)) (outputs : Wires args [fn.results] outs)
    {entryL entryR : Tuple m.Val args} (entries : TupleRelated m ids entryL entryR)
    {captL captR : Tuple m.Val captured} (captures : TupleRelated m ids captL captR)
    {argsL argsR : Tuple m.Val fn.args} (arguments : TupleRelated m ids argsL argsR)
    (selectL : inputs.read entryL PUnit.unit = .cons (.closure captL left.toGraph) argsL)
    (selectR : inputs.read entryR PUnit.unit = .cons (.closure captR right.toGraph) argsR) (store : σ) :
    RegionPair primitives ids mapping (applicationCode fn inputs outputs) (applicationCode fn inputs outputs)
      entryL entryR store := by
  have actualL := open_lambda left captL argsL
  have actualR := open_lambda right captR argsR
  cases regions code respects (prepend_related captures arguments) store with
  | @returned _ _ finalStore values ranL ranR =>
    have locals := LocalsRelated.empty.snoc (fun _ _ same => same) rfl values
    exact .returned (finalStore := finalStore) (read_same entries locals outputs)
      (.bind (node := applicationVertex fn inputs)
        (application_eval selectL (.call (actualL.symm ▸ ranL))) (.ret outputs _ _ _))
      (.bind (node := applicationVertex fn inputs)
        (application_eval selectR (.call (actualR.symm ▸ ranR))) (.ret outputs _ _ _))
  | blocked stopped =>
    exact .blocked (.application inputs outputs selectL selectR stopped)
  | productive run =>
    refine .productive (productive_map run ?_ ?_)
    · intro target pending reached
      exact ⟨.bind (past := []) (.ret outputs) entryL PUnit.unit pending,
        .inside (node := applicationVertex fn inputs)
          (application_reaches selectL (.call (actualL.symm ▸ reached)))⟩
    · intro target pending reached
      exact ⟨.bind (past := []) (.ret outputs) entryR PUnit.unit pending,
        .inside (node := applicationVertex fn inputs)
          (application_reaches selectR (.call (actualR.symm ▸ reached)))⟩

/-- A static caller reads its function from its first captured port. -/
theorem captured_application
    {left : NestedTheta.Term (Instruction Op) (captured ++ fn.args) [] sigsL fn.results}
    {right : NestedTheta.Term (Instruction Op) (captured ++ fn.args) [] sigsR fn.results}
    (code : CodePair Op mapping left right) (respects : ActionsRespect primitives ids)
    (arguments : Wires (fn.port :: args) [] fn.args) (outputs : Wires (fn.port :: args) [fn.results] outs)
    {tailL tailR : Tuple m.Val args} (tails : TupleRelated m ids tailL tailR)
    {captL captR : Tuple m.Val captured} (captures : TupleRelated m ids captL captR)
    (iso : NestedTheta.Graph.Isomorphic (Instruction Op) left.toGraph right.toGraph) (store : σ) :
    RegionPair primitives ids mapping (applicationCode fn (.cons (.arg .head) arguments) outputs)
      (applicationCode fn (.cons (.arg .head) arguments) outputs)
      (.cons (.closure captL left.toGraph) tailL) (.cons (.closure captR right.toGraph) tailR) store := by
  have entries := TupleRelated.cons (ValueRelated.closure captures iso) tails
  exact application code respects (.cons (.arg .head) arguments) outputs entries captures
    (read_same entries LocalsRelated.empty arguments) rfl rfl store

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Proofs

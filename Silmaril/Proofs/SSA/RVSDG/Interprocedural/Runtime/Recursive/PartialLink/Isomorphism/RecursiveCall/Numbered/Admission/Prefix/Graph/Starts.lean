module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Admission.Prefix.Graph.Defs

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Prefix.Proofs

open Continuation.Partial (Primitives)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {primitives : Primitives m σ} {ids : GlobalRel} {rename : Nat → Nat}
variable {exports : Ports (Ty V S)} {fn : Function V S}

theorem starts_of_outcomes {left right : Outcome m σ exports}
    (linked : OutcomesRelated m ids σ rename exports left right)
    (port : Port exports fn.port) {argsL argsR : Tuple m.Val fn.args}
    (arguments : TupleRelated m ids argsL argsR) (plain : ordinaryPorts fn.args = true)
    (certificate : Option (PLift (AdmittedExport primitives ids port left right))) :
    StartsRelated primitives ids rename exports (certificate.isSome = true)
      (match left with
      | .undefined failure => .error failure
      | .linked values store => .ok ⟨Continuation.start (.call (values.get port) argsL), store⟩)
      (match (generalizing := false) right with
      | .undefined failure => .error failure
      | .linked values store => .ok ⟨Continuation.start (.call (values.get port) argsR), store⟩) := by
  cases linked with
  | linked values store =>
    intro accepted
    exact (certificate.get accepted).down.atExport port (rename := rename) (.linked values store) arguments plain
  | undefined address identity site store =>
    exact .undefined address identity site store

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Prefix.Proofs

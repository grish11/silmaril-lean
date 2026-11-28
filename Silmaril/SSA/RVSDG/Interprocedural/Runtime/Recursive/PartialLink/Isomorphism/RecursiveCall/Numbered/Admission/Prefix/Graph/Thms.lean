module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Admission.Prefix.Graph.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Executable.Thms
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Admission.Prefix.Graph.Starts

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Prefix

open Continuation.Partial.Executable (Actions)
open NestedTheta.Equality (OpcodeCode)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ids : GlobalRel}
variable {imports exports : Ports (Ty V S)} {sigsL sigsR : List (Ports (Ty V S))}
variable {unitL unitR : Nat}

/-- Ordered partial linking supplies the related exports for checked
invocation, starting from related imports at a common store. If a δ
initializer fails, both starts report the corresponding error independently
of the admission check. Successful starts use their actual post-link values
and store. The typed renumbering and the initializer schedule are premises. -/
theorem admitGraph_starts [DecidableEq (Ty V S)] (keys : OpcodeCode (Instruction Op)) [DecidableEq keys.Key]
    (actions : Actions m σ) (respects : ActionsRespect actions.toPrimitives ids) (ordinary : OrdinaryOutputs Op)
    {left : Omega Op imports exports sigsL} {right : Omega Op imports exports sigsR}
    {positions : Fin sigsL.length ≃ Fin sigsR.length} (iso : left.RenumberedBy right positions)
    (schedule : Isomorphism.Ordered Op (renameVertex positions) imports exports left.toTerm.region right.toTerm.region)
    (identities : ∀ i, ids (unitL, i) (unitR, renameVertex positions i))
    {inputsL inputsR : Tuple m.Val imports} (inputs : TupleRelated m ids inputsL inputsR)
    (plan : GraphPlan left right) {fn : Function V S} (port : Port exports fn.port)
    {argsL argsR : Tuple m.Val fn.args} (arguments : TupleRelated m ids argsL argsR)
    (plain : ordinaryPorts fn.args = true) (store : σ)
    (captureCode : CaptureCode m := .controlOnly m)
    (exactValue : ExactValueCheck m := fun _ _ => none)
    (exactGroup : ExactGroupCheck m := ExactGroupCheck.ofCaptures keys exactValue) :
    StartsRelated actions.toPrimitives ids (renameVertex positions) exports
      ((admitGraph keys actions ids ordinary unitL unitR inputsL inputsR left right plan port
        store store captureCode exactValue exactGroup).isSome = true)
      (Executable.start actions unitL left inputsL port argsL store)
      (Executable.start actions unitR right inputsR port argsR store) := by
  have linked := link_related respects iso schedule identities inputs store
  simp only [← Executable.link_eq actions] at linked
  exact Proofs.starts_of_outcomes (primitives := actions.toPrimitives) linked port arguments plain _

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Prefix

module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Admission.Prefix.Defs
import Silmaril.SSA.RVSDG.Interprocedural.Terms.Thms

/-! Checked ordered prefix admission for typed numbered modules. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Prefix

open Continuation.Partial (Config Primitives)
open Continuation.Partial.Executable (Actions)
open NestedTheta.Equality (OpcodeCode)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {importsL importsR exports : Ports (Ty V S)}
variable {sigsL sigsR : List (Ports (Ty V S))}

/-- Binding selections for two numbered modules in their original table order. -/
abbrev GraphPlan (left : Omega Op importsL exports sigsL) (right : Omega Op importsR exports sigsR) :=
  Plan Op importsL importsR exports false left.toTerm.region right.toTerm.region

/-- Run the ordered prefix checker on the graph's exact linearization.
The certificate refers to the original graphs' executable link results.
The supplied plan selects bindings. Primitive compatibility and related
successful link outcomes are still required for paired invocation. -/
def admitGraph [DecidableEq (Ty V S)] (keys : OpcodeCode (Instruction Op)) [DecidableEq keys.Key]
    (actions : Actions m σ) (ids : GlobalRel) (ordinary : OrdinaryOutputs Op) (unitL unitR : Nat)
    (inputsL : Tuple m.Val importsL) (inputsR : Tuple m.Val importsR)
    (left : Omega Op importsL exports sigsL) (right : Omega Op importsR exports sigsR)
    (plan : GraphPlan left right) {fn : Function V S} (port : Port exports fn.port) (storeL storeR : σ)
    (captureCode : CaptureCode m := .controlOnly m)
    (exactValue : ExactValueCheck m := fun _ _ => none)
    (exactGroup : ExactGroupCheck m := ExactGroupCheck.ofCaptures keys exactValue) :
    Option (PLift (AdmittedExport actions.toPrimitives ids port
      (Executable.link actions unitL left inputsL storeL)
      (Executable.link actions unitR right inputsR storeR))) :=
  (admit keys actions ids ordinary unitL unitR inputsL inputsR left.toTerm right.toTerm
    plan port storeL storeR captureCode exactValue exactGroup).map fun checked =>
      ⟨by simpa only [Omega.toGraph_toTerm] using checked.down⟩

/-- Failed links carry corresponding diagnostics. At successful starts, an
accepted admission check supplies the closed family for the actual configurations. -/
def StartsRelated (primitives : Primitives m σ) (ids : GlobalRel) (rename : Nat → Nat)
    (exports : Ports (Ty V S)) (accepted : Prop) {results : Ports (Ty V S)} :
    Except (Failure m σ) (Config m σ results) → Except (Failure m σ) (Config m σ results) → Prop
  | .error left, .error right =>
    OutcomesRelated m ids σ rename exports (.undefined left) (.undefined right)
  | .ok left, .ok right =>
    accepted → ∃ familyL familyR, ClosedFamily primitives ids familyL familyR ∧
      Admitted m ids familyL familyR left right
  | _, _ => False

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Prefix

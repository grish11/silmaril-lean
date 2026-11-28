module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Admission.Prefix.Graph.Import.Allocation.Defs

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Prefix.AllocationProofs

open Continuation.Partial.Executable (Actions)
open NestedTheta.Equality (OpcodeCode)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {importsL importsR exports extra : Ports (Ty V S)}
variable {sigsL sigsR : List (Ports (Ty V S))}
variable {providerFn clientFn : Function V S} {value : ValueSort V S}

theorem link_body {imports : Ports (Ty V S)} {shifted : Bool}
    (client : AllocatingClient Op imports clientFn value shifted)
    (actions : Actions m σ) (unit : Nat) (inputs : Tuple m.Val imports) (store : σ) :
    let locals := AllocatingClient.initialLocals m shifted
    Executable.link actions unit client.toGraph inputs store =
      match Executable.linkVertex actions unit inputs locals (.delta client.initializer) store with
      | .undefined failure => .undefined failure
      | .linked values middle => .linked (.cons (linkedLambda client.body inputs (locals.snoc values)) .nil) middle := by
  cases shifted
  · cases client
    simp only [AllocatingClient.toGraph, Executable.link, AllocatingClient.sigs, Executable.linkTable, AllocatingClient.initialLocals]
    split
    · rename_i equation
      erw [equation]
      rfl
    · rename_i equation
      erw [equation]
  · obtain ⟨delta, body⟩ := client
    simp only [AllocatingClient.toGraph, Executable.link, AllocatingClient.sigs, Executable.linkTable, AllocatingClient.initialLocals]
    have empty : Executable.linkVertex actions unit inputs (past := []) PUnit.unit
        (.phi (members := []) ⟨[], .nil, fun i => i.elim0⟩) store = .linked .nil store := rfl
    erw [empty]
    dsimp only
    split
    · rename_i equation
      erw [equation]
      rfl
    · rename_i equation
      erw [equation]

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Prefix.AllocationProofs

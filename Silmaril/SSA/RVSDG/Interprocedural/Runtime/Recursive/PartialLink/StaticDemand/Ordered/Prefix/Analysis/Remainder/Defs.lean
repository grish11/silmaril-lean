module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Analysis.Delta.Defs

/-! Checked link prefixes with a source-indexed remainder. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix

open Continuation.Partial.Executable (Actions)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {imports outs : Ports (Ty V S)} {sigs : List (Ports (Ty V S))}

/-- A checked physical prefix with a common store and the exact original
link outcomes reindexed to the remaining source. -/
structure LinkedRemainder (actions : Actions m σ) (unitId : Nat)
    (inputsL inputsR : Tuple m.Val imports) (outL outR : Outcome m σ outs) (scope : Scope m)
    (tail : ModuleTerm Op imports scope.past sigs outs) where
  checked : scope.Checked actions
  store : σ
  linkL : outL = Isomorphism.RecursiveCall.Numbered.Prefix.linkTerm actions unitId inputsL scope.localsL tail store
  linkR : outR = Isomorphism.RecursiveCall.Numbered.Prefix.linkTerm actions unitId inputsR scope.localsR tail store

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix

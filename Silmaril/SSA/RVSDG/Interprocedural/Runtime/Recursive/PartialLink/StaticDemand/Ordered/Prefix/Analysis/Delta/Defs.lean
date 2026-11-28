module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Analysis.Thms

/-! A successful leading δ for numbered demand analysis. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix

open Continuation.Partial.Executable (Actions)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {imports : Ports (Ty V S)} {value : ValueSort V S}
variable {actions : Actions m σ} {unitId : Nat}
variable {inputsL inputsR : Tuple m.Val imports}
variable {init : DeltaTerm Op imports [] value} {initial : σ}

/-- Two actual link outcomes with a common successful store. The typed
rows are retained independently for the two runs. -/
structure LinkedRows {ports : Ports (Ty V S)} (outL outR : Outcome m σ ports) where
  left : Tuple m.Val ports
  right : Tuple m.Val ports
  store : σ
  linkedL : outL = .linked left store
  linkedR : outR = .linked right store

def LinkedRows.check {ports : Ports (Ty V S)} [DecidableEq σ] :
    (outL outR : Outcome m σ ports) → Option (LinkedRows outL outR)
  | .linked left storeL, .linked right storeR =>
    if same : storeR = storeL then
      some ⟨left, right, storeL, rfl, congrArg (Outcome.linked right) same⟩
    else none
  | _, _ => none

/-- Append actual initialized rows without changing any callable slot. -/
def Scope.addInitialized (scope : Scope m) {ports : Ports (Ty V S)}
    (left right : Tuple m.Val ports) : Scope m :=
  ⟨scope.past ++ [ports], scope.table, scope.localsL.snoc left, scope.localsR.snoc right,
    scope.guardL, scope.guardR⟩

def Scope.Checked.addInitialized {scope : Scope m} (checked : scope.Checked actions)
    {ports : Ports (Ty V S)} (left right : Tuple m.Val ports) :
    (scope.addInitialized left right).Checked actions :=
  ⟨⟨checked.state.dispatch, checked.state.left.snoc (fun _ => none), checked.state.right.snoc (fun _ => none)⟩,
    checked.left, checked.right⟩

/-- The actual typed results of a leading δ and the common store needed
to compare the subsequent invocations. The initialized values can differ. -/
structure DeltaPrefix (actions : Actions m σ) (unitId : Nat)
    (init : DeltaTerm Op imports [] value) (inputsL inputsR : Tuple m.Val imports) (initial : σ) where
  left : Tuple m.Val [.value (.global value)]
  right : Tuple m.Val [.value (.global value)]
  store : σ
  linkedL : Executable.linkVertex (past := []) actions unitId inputsL PUnit.unit (.delta init.toGraph) initial = .linked left store
  linkedR : Executable.linkVertex (past := []) actions unitId inputsR PUnit.unit (.delta init.toGraph) initial = .linked right store

/-- Run the ordinary partial linker for both imports and check the common
post-link store. A blocked initializer or a store mismatch rejects the receipt. -/
def DeltaPrefix.check [DecidableEq σ] (actions : Actions m σ) (unitId : Nat)
    (init : DeltaTerm Op imports [] value) (inputsL inputsR : Tuple m.Val imports) (initial : σ) :
    Option (DeltaPrefix actions unitId init inputsL inputsR initial) :=
  (LinkedRows.check
    (Executable.linkVertex (past := []) actions unitId inputsL PUnit.unit (.delta init.toGraph) initial)
    (Executable.linkVertex (past := []) actions unitId inputsR PUnit.unit (.delta init.toGraph) initial)).map
      fun rows => ⟨rows.left, rows.right, rows.store, rows.linkedL, rows.linkedR⟩

/-- Start the ordinary demand scope with the actual initialized row.
The δ contributes no checked callable slot. -/
def DeltaPrefix.scope (receipt : DeltaPrefix actions unitId init inputsL inputsR initial) : Scope m :=
  (Scope.ordinary m).addInitialized receipt.left receipt.right

/-- No callable membership is manufactured for the initialized row.
Ordinary data remains available through the existing typed capture check. -/
def DeltaPrefix.checked (receipt : DeltaPrefix actions unitId init inputsL inputsR initial) :
    receipt.scope.Checked actions :=
  (Scope.Checked.ordinary actions).addInitialized receipt.left receipt.right

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix

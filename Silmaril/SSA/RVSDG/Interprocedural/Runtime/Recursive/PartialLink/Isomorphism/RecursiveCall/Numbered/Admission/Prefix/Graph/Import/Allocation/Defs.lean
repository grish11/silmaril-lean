module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Admission.Prefix.Graph.Import.Defs

/-! Checked provider imports with one client allocation. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Prefix

open Continuation.Partial.Executable (Actions)
open NestedTheta.Equality (OpcodeCode)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {importsL importsR exports extra : Ports (Ty V S)}
variable {sigsL sigsR : List (Ports (Ty V S))}
variable {providerFn clientFn : Function V S} {value : ValueSort V S}

/-- The store trace of successful executable links, with their reserved
unit IDs in reverse link order. This trace records only the links it
witnesses. -/
inductive AllocationHistory (actions : Actions m σ) : List Nat → σ → σ → Prop where
  | empty (store : σ) : AllocationHistory actions [] store store
  | link {units : List Nat} {unit : Nat} {start before after : σ}
      {imports exports : Ports (Ty V S)} {sigs : List (Ports (Ty V S))}
      {graph : Omega Op imports exports sigs} {inputs : Tuple m.Val imports} {values : Tuple m.Val exports}
      (prior : AllocationHistory actions units start before)
      (ran : Executable.link actions unit graph inputs before = .linked values after) :
      AllocationHistory actions (unit :: units) start after

/-- A contiguous segment of a certified trace. The segment's own history
is supplied by its provider receipt. The surrounding histories fix its
position and both exact store boundaries. -/
def AllocationHistory.Segment (actions : Actions m σ) (whole units : List Nat)
    (initial final entered exited : σ) : Prop :=
  ∃ before after : List Nat,
    whole = after ++ units ++ before ∧
      AllocationHistory actions before initial entered ∧ AllocationHistory actions after exited final

/-- The client allocates one global and exports the following λ. An
optional empty φ before δ fixes the other supported numbering. -/
structure AllocatingClient (Op : Dialect.{u, v} (ValueSort V S) S)
    (imports : Ports (Ty V S)) (fn : Function V S) (value : ValueSort V S) (shifted : Bool) where
  initializer : Delta Op imports (if shifted then [[]] else []) value
  body : Lambda Op imports ((if shifted then [[]] else []) ++ [[.value (.global value)]]) fn

def AllocatingClient.sigs (fn : Function V S) (value : ValueSort V S) :
    Bool → List (Ports (Ty V S))
  | false => [[.value (.global value)], [fn.port]]
  | true => [[], [.value (.global value)], [fn.port]]

def AllocatingClient.toGraph {imports : Ports (Ty V S)} :
    {shifted : Bool} → AllocatingClient Op imports clientFn value shifted →
      Omega Op imports [clientFn.port] (AllocatingClient.sigs clientFn value shifted)
  | false, ⟨delta, body⟩ =>
    ⟨⟨Fin.cases (.delta delta) (Fin.cases (.lambda body) (fun i => i.elim0)),
      .cons (.output (1 : Fin 2) .head) .nil⟩⟩
  | true, ⟨delta, body⟩ =>
    ⟨⟨Fin.cases (.phi (members := []) ⟨[], .nil, fun i => i.elim0⟩)
      (Fin.cases (.delta delta) (Fin.cases (.lambda body) (fun i => i.elim0))),
      .cons (.output (2 : Fin 3) .head) .nil⟩⟩

def AllocatingClient.initialLocals (m : Machine.{u, v, w} Op) :
    (shifted : Bool) → Locals m.Val (if shifted then [[]] else [])
  | false => PUnit.unit
  | true => (.nil, PUnit.unit)

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Prefix

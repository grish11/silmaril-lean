module

public import Silmaril.Wasm.Execution.Core.Intrinsic.Call.Defs
public import Silmaril.Wasm.Equiv.Module

@[expose] public section

namespace Silmaril.Wasm.Execution.Core.Intrinsic

open Numerics

def invokeResult {results : List IntType} : Option (Values results) → Result
  | none => .trap
  | some values => .values values.erase.reverse

/-- A comparison of two actual Core entries, including agreement on which
arguments are accepted. Stores and addresses need not coincide. -/
structure EntryAgreement {H : Type} (R : Behaviour Val → Behaviour Val → Prop)
    (profile : Profile) (host : HostSemantics H) (left right : Store H) (first second : Nat) : Prop where
  accepts : ∀ vs, InvokeOk left first vs ↔ InvokeOk right second vs
  observes : ∀ vs, InvokeOk left first vs →
    Behaviours.Equiv R (behaviours profile host left first vs) (behaviours profile host right second vs)

end Silmaril.Wasm.Execution.Core.Intrinsic

module

public import Mathlib.Data.List.AList
public import Silmaril.Semantics.Operational.Environment

/-! # Finite presentations of partial environments

Mathlib's association lists carry unique keys. Lookup forgets entry order
and lands in the existing operational partial-map type. The supplied support
is an enumeration of possible keys, so repetitions and absent keys are allowed.
-/

@[expose] public section

namespace Silmaril.Semantics.Operational.Environment.Finite

variable {Key Value : Type*} [DecidableEq Key]

def view (rows : AList (fun _ : Key => Value)) : Environment Key Value :=
  fun key => rows.lookup key

/-- Materialize the bindings of the environment on the supplied keys. -/
def encode (env : Environment Key Value) : List Key → AList (fun _ : Key => Value)
  | [] => ∅
  | key :: rest =>
    match env key with
    | none => encode env rest
    | some value => (encode env rest).insert key value

end Silmaril.Semantics.Operational.Environment.Finite

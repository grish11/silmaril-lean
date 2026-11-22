module

public import Silmaril.Formats.Dasl.Lift.Defs
public import Silmaril.Formats.Dasl.Resolve.Thms
import Silmaril.Proofs.Formats.Dasl.Lift

public section

namespace Silmaril.Formats.Dasl.Lift

open Silmaril.Semantics.Naming (Binding Relation)

theorem name_binding {Name Item : Type} {store : Store Name} {decode : Relation Value Item}
    (bound : store.Binding) (functional : Binding decode) : Binding (name store decode).represents :=
  (valueNames_binding bound).push functional

theorem natI64_exact {number : Nat} (fits : number < 2^63) :
    (UInt64.ofNat number).toInt64.toInt = (number : Int) :=
  Proofs.Formats.Dasl.Lift.nat_i64_exact fits

theorem lengthI64_iff (ctx : Semantics.Naming.Lift.Coordinate) (length : ctx.Meaning → Nat)
    (root : ctx.Surface) (output : Value) :
    lengthI64 ctx length root output ↔ ∃ size, lengthNat ctx length root size ∧ natI64 output size :=
  Proofs.Formats.Dasl.Lift.length_i64_iff ctx length root output

end Silmaril.Formats.Dasl.Lift

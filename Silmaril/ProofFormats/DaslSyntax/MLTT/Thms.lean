module

public import Silmaril.ProofFormats.DaslSyntax.MLTT.Defs
public import Silmaril.ProofFormats.DaslSyntax.Thms

public section

namespace Silmaril.ProofFormats.DaslSyntax.MLTT

open Silmaril.Formats.Dasl

theorem lenI64_iff {Name : Type} (store : Store Name) (context : Name) (output : Value) :
    lenI64 store context output ↔ ∃ size, lenNat store context size ∧ Lift.natI64 output size :=
  Lift.lengthI64_iff _ _ _ _

end Silmaril.ProofFormats.DaslSyntax.MLTT

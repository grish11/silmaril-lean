module

public import Silmaril.Formats.Cbor.Drisl.Number.Defs
import Silmaril.Proofs.Formats.Cbor.Drisl.Number

@[expose] public section

namespace Silmaril.Formats.Cbor.Drisl

theorem int64_toInt (value : Int64) : int64? value.toInt = some value :=
  Proofs.Formats.Cbor.Drisl.Number.int64_toInt value

theorem Integer.toInt_ofInt64 (value : Int64) : (Integer.ofInt64 value).toInt = value.toInt :=
  Proofs.Formats.Cbor.Drisl.Number.toInt_ofInt64 value

theorem decimalI64_intDecimal (value : Int64) : decimalI64? (intDecimal value.toInt) = some value := by
  simp [decimalI64?, Proofs.Formats.Cbor.Drisl.Number.exactInt_intDecimal, int64_toInt]

theorem Number.readDecimal_toDecimal (value : Number) : readDecimal? value.toDecimal = some value :=
  Proofs.Formats.Cbor.Drisl.Number.number_inverse value

end Silmaril.Formats.Cbor.Drisl

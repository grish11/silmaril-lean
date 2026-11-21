module

public import Silmaril.Formats.Json.Ordered
public import Silmaril.Formats.JsonWire.Ast.Defs

/-! Simple in-memory JSON with bytes as an additional scalar. This is not a
chunk, token, or wire representation. Arrays retain order in every view. -/

@[expose] public section

namespace Silmaril.Formats.JsonWithBytes

inductive Scalar (Number : Type) where
  | null
  | bool (value : Bool)
  | string (value : String)
  | number (value : Number)
  | bytes (value : List UInt8)
  deriving DecidableEq, Repr

/-- Ordered syntax preserves input member order. At a semantic boundary use
`RawSyn.WellFormed` to reject duplicates, never silently discard them. -/
abbrev Ordered (Number : Type := JsonWire.Decimal) := RawJson (Scalar Number)

/-- Objects are finite maps; member order is not observable. -/
abbrev Unordered (Number : Type := JsonWire.Decimal) := Json (Scalar Number)

/-- Unique representative sorted by ordinary string order, not CBOR order. -/
abbrev Sorted (Number : Type := JsonWire.Decimal) := OrderedJson (Scalar Number)

abbrev OrderedI64 := Ordered Int64
abbrev UnorderedI64 := Unordered Int64

end Silmaril.Formats.JsonWithBytes

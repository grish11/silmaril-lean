module

public import Silmaril.Formats.Cbor.Drisl.Cid.Defs
public import Silmaril.Formats.JsonWithBytes.Defs

/-! Ordered, CID-parametric data models for DRISL and ATProto core.
Object order is retained in memory; the CBOR boundary checks canonical order.
CID profile checks belong at boundaries, not in the recursive tree. -/

@[expose] public section

namespace Silmaril.Formats.Cbor.Drisl

/-- The two CBOR integer argument spaces are disjoint, including at zero. -/
inductive Integer where
  | uint (argument : UInt64)
  | nint (argument : UInt64)
  deriving DecidableEq, Repr

abbrev Float64Bits := { bits : Nat // okFloat64 bits = true }

inductive Number where
  | integer (value : Integer)
  | float (bits : Float64Bits)
  deriving DecidableEq

inductive Scalar (Numeric Cid : Type) where
  | data (value : JsonWithBytes.Scalar Numeric)
  | link (value : Cid)
  deriving DecidableEq

/-- CID implementations supply their own representation. The default is
validated CIDv1 without the tag-42 leading zero. -/
abbrev Ordered (Link : Type := Cid .any) := RawJson (Scalar Number Link)

abbrev OrderedATProto (Link : Type := Cid .any) := RawJson (Scalar Int64 Link)

/-- A scalar-only embedding. It preserves member order and all byte strings. -/
def embedI64 {Cid : Type} (value : JsonWithBytes.OrderedI64) : OrderedATProto Cid :=
  value.mapScalar Scalar.data

/-- Links in document order, including through arrays and object values. -/
def links {Numeric Cid : Type} {index : JsonIx} (value : RawSyn String (Scalar Numeric Cid) index) :
    List Cid := value.scalars.filterMap fun | .link cid => some cid | .data _ => none

/-- Visit links in document order without first collecting the scalar leaves. -/
def foldLinks {Numeric Link State : Type} (visit : State → Link → State) :
    State → {index : JsonIx} → RawSyn String (Scalar Numeric Link) index → State
  | state, _, .scalar (.link cid) => visit state cid
  | state, _, .list items | state, _, .map items => foldLinks visit state items
  | state, _, .cons value tail | state, _, .objCons _ value tail =>
    foldLinks visit (foldLinks visit state value) tail
  | state, _, _ => state

end Silmaril.Formats.Cbor.Drisl

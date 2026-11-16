module

public import Silmaril.Formats.Cbor.Value.Defs
public import Silmaril.Formats.Utf8.Defs

/-!
# CBOR basic validity, relative to the `Cbor.Value` model

RFC 8949 §5.3.1 ("Basic Validity") asks that text strings be valid UTF-8 and that maps have no
duplicate keys. Duplicates are judged by equality in the *generic data model* (§2, §5.6). This
module defines a validity that is **relative to the representation-level model `Cbor.Value`**,
and is named so (`ModelValid`), because that model is finer than the generic data model:

* two keys are duplicates here exactly when they are equal `Value`s, which for encodable values
  is when their deterministic encodings are equal (`Value.encode` is injective);
* the generic data model identifies some keys this model keeps apart, for example a float key
  `1.5` at half and at double precision. So a map can be `ModelValid` while RFC 8949 calls it
  invalid. `ModelValid` is a *necessary* condition for RFC basic validity of definite items, not
  a sufficient one. This is a statement about the definitions, not a proved theorem: RFC 8949's
  generic data model is not formalized here.

Not checked: tag-content validity (§5.3.2) and any application-level validity.

`ModelValid.language` is the set of *shortest-head definite-length* encodings `v.encode` of
model-valid values. Well-formed items with non-shortest heads or indefinite lengths are not in
it, even when their values are valid. It is therefore not the language of all valid CBOR items.
-/

@[expose] public section

namespace Silmaril.Formats.Cbor.ModelValid

mutual

/-- Text is UTF-8 and every map's keys have pairwise distinct encodings. -/
def ok : Value → Bool
  | .text t => Utf8.isWellFormed t
  | .array xs => okList xs
  | .map kvs => okMap kvs && decide (kvs.map (fun kv => kv.1.encode)).Nodup
  | .tag _ v => ok v
  | _ => true

/-- Every item is model-valid. -/
def okList : List Value → Bool
  | [] => true
  | v :: vs => ok v && okList vs

/-- Every key and value is model-valid. -/
def okMap : List (Value × Value) → Bool
  | [] => true
  | (k, v) :: kvs => ok k && ok v && okMap kvs

end

mutual

/-- `Value.Encodable`, as a check (`Thms`: `encodableB_iff`). -/
def encodableB : Value → Bool
  | .uint n | .nint n => decide (n < 2 ^ 64)
  | .bytes b | .text b => decide (b.length < 2 ^ 64)
  | .array xs => decide (xs.length < 2 ^ 64) && encodableListB xs
  | .map kvs => decide (kvs.length < 2 ^ 64) && encodableMapB kvs
  | .tag n v => decide (n < 2 ^ 64) && encodableB v
  | .simple n => decide (n < 24 ∨ (32 ≤ n ∧ n < 256))
  | .float w bits => decide ((w = 2 ∨ w = 4 ∨ w = 8) ∧ bits < 256 ^ w)

/-- Every item is encodable. -/
def encodableListB : List Value → Bool
  | [] => true
  | v :: vs => encodableB v && encodableListB vs

/-- Every key and value is encodable. -/
def encodableMapB : List (Value × Value) → Bool
  | [] => true
  | (k, v) :: kvs => encodableB k && encodableB v && encodableMapB kvs

end

/-- Shortest-head definite-length encodings of encodable, model-valid values. -/
def language : Language UInt8 := {w | ∃ v, v.Encodable ∧ ok v = true ∧ v.encode = w}


/-- Decide membership: decode, check, re-encode. -/
def check (w : List UInt8) : Bool :=
  match decode w with
  | some v => encodableB v && ok v && v.encode == w
  | none => false

end Silmaril.Formats.Cbor.ModelValid

end

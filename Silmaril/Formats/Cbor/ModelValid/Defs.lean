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
  `1.5` at half and at double precision. So a value can pass `ModelValid.ok` while RFC 8949
  calls its map keys duplicates (an example in `Thms`).

`ModelValid.ok` is therefore **not** RFC basic validity, and no inclusion between it and RFC
validity is proved in either direction. RFC 8949's generic data model is not formalized here.

Not checked: tag-content validity (§5.3.2) and any application-level validity. Every statement
here is about values and bytes *without* any tag-validity condition.

`ModelValid.language` is the set of *shortest-head definite-length* encodings `v.encode` of
values passing `ModelValid.ok`. It is neither a subset nor a superset of the RFC-valid byte
strings, and no inclusion is claimed:

* it *excludes* valid encodings: items with non-shortest heads or indefinite lengths are never
  members, even when RFC 8949 calls them valid;
* it *includes* invalid ones: the duplicate float-key map above is a member.

What is proved is only `check_iff` (decidability) and `language_le_wellFormed` (every member is one
well-formed CBOR item).
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

module

public import Silmaril.Formats.Cbor.Drisl.Defs

/-!
# Deterministically encoded CBOR, relative to a float rule

RFC 8949 §4.2.1 ("Core Deterministic Encoding Requirements") asks for:

1. preferred serialization: shortest arguments, and floats in the shortest form that
   preserves the value (§4.1, §4.2.2 for the choices it leaves);
2. definite lengths only;
3. map keys sorted in the bytewise lexicographic order of their deterministic encodings.

Items 2 and 3, and the integer and length part of item 1, are checked exactly here: a member is
the shortest-head definite encoding `v.encode` of a value whose map keys are strictly sorted
(so no two keys have the same encoding).

**The float part of item 1 is a parameter, not a theorem.** Deciding whether a float is in its
shortest value-preserving width needs IEEE 754 width conversion, which is not implemented here.
So `DetProfile.floatOk` says which `(width, bits)` floats are allowed, and every statement is
about deterministic encoding *relative to that rule*. The intended reading is that `language`
is the RFC 8949 §4.2.1 core-deterministic language **under the assumption** that the supplied
rule is exactly "shortest value-preserving width". No such rule is defined here, so this module
is not a complete RFC deterministic checker. The correspondence of the other checks with §4.2.1
is by transcription; RFC 8949 is not formalized, so it is not a theorem. The concrete rules
provided:

* `FloatRule.none`: no floats are allowed, so the float rule plays no part. The language is
  meant to be the float-free core-deterministic items (by transcription, as above);
* `FloatRule.only64`: 64-bit floats only (the CBOR/c-42 and DRISL rule, which is *not* §4.2.1
  preferred serialization);
* `FloatRule.any`: any width. This is deterministic in everything but floats, and is not RFC
  deterministic.

`DetProfile.utf8Text` optionally also requires text strings to be UTF-8 (basic validity,
§5.3.1). Tags and simple values are otherwise unconstrained; tag-content validity (§5.3.2) is
not checked.
-/

@[expose] public section

namespace Silmaril.Formats.Cbor.Deterministic

/-- Which floats `(width in bytes, bits)` count as deterministically encoded. -/
abbrev FloatRule : Type := Nat → Nat → Bool

/-- No floats. -/
def FloatRule.none : FloatRule := fun _ _ => false
/-- Only 64-bit floats (CBOR/c-42, DRISL); not RFC 8949 preferred serialization. -/
def FloatRule.only64 : FloatRule := fun w _ => w == 8
/-- Any width (deterministic in everything but floats; not RFC deterministic). -/
def FloatRule.any : FloatRule := fun _ _ => true

/-- A deterministic-encoding profile: the float rule (an assumption, see the module doc) and
whether text must be UTF-8. -/
structure DetProfile where
  floatOk : FloatRule
  utf8Text : Bool

mutual

/-- The value is encodable and its maps have strictly sorted keys; floats meet the rule. -/
def detOk (P : DetProfile) : Value → Bool
  | .uint n | .nint n => decide (n < 2 ^ 64)
  | .bytes b => decide (b.length < 2 ^ 64)
  | .text t => decide (t.length < 2 ^ 64) && (!P.utf8Text || Utf8.isWellFormed t)
  | .array xs => decide (xs.length < 2 ^ 64) && detOkList P xs
  | .map kvs => decide (kvs.length < 2 ^ 64) && detOkMap P kvs &&
      Drisl.strictlySorted (kvs.map fun kv => kv.1.encode)
  | .tag n v => decide (n < 2 ^ 64) && detOk P v
  | .simple n => decide (n < 24 ∨ (32 ≤ n ∧ n < 256))
  | .float w bits => decide (w = 2 ∨ w = 4 ∨ w = 8) && decide (bits < 256 ^ w) && P.floatOk w bits

/-- Every item is allowed. -/
def detOkList (P : DetProfile) : List Value → Bool
  | [] => true
  | v :: vs => detOk P v && detOkList P vs

/-- Every key and value is allowed. -/
def detOkMap (P : DetProfile) : List (Value × Value) → Bool
  | [] => true
  | (k, v) :: kvs => detOk P k && detOk P v && detOkMap P kvs

end

/-- The deterministically encoded items, relative to the profile's float rule. -/
def language (P : DetProfile) : Language UInt8 := {w | ∃ v, detOk P v = true ∧ v.encode = w}

/-- Decide membership: decode, check, re-encode. -/
def check (P : DetProfile) (w : List UInt8) : Bool :=
  match decode w with
  | some v => detOk P v && v.encode == w
  | none => false

end Silmaril.Formats.Cbor.Deterministic

end

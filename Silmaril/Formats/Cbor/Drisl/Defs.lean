module

public import Silmaril.Formats.Cbor.Value.Defs
public import Silmaril.Formats.Utf8.Defs

/-!
# DRISL, and the ATProto core profile, as byte languages

**DRISL** ("Deterministic Representation for Interoperable Structures & Links", `drisl`,
https://dasl.ing/drisl.html, last updated 2026-10-22, pinned by SHA-256 in `references.bib`)
is a deterministic profile of CBOR. It "mostly subsets" CBOR/c-42 (`cborc42`, the tag-42
profile of CBOR Core) and adds its own constraints. The language `Drisl.language .drisl` is the
set of byte strings `v.encode` for values `v` with `ok .drisl v`:

* **One complete item, deterministic encoding.** Shortest heads, definite lengths only
  ("Indefinite-length arrays … are not allowed", and CBOR/c-42: "Indefinite length objects
  MUST be rejected"), and no trailing bytes ("appending extra bytes of any kind … breaks the
  DRISL-wide assumption that each CID refers to one complete, discrete, and valid CBOR
  object"). Being of the form `v.encode` is what enforces this.
* **Integers:** major types 0 and 1 with arguments below `2^64`. CBOR/c-42 would use `bigint`
  (tags 2 and 3) beyond that, but DRISL "must reject all other tags, including any of the tags
  listed in the section 3.4 of RFC 8949", so DRISL has no bignums. Where the two texts
  disagree we follow DRISL's explicit rule.
* **Strings:** byte strings, and text strings that are well-formed UTF-8 (CBOR/c-42 `tstr`).
* **Maps:** "reject map keys that are not strings", so keys are text strings. Keys are sorted
  strictly by the bytewise lexicographic order of their deterministic encodings, so duplicates
  are rejected (CBOR/c-42 §2.2, RFC 8949 §4.2.1).
* **Tags:** only tag 42, whose content is a byte string `00 ++ cid` ("the null byte 0x00 is
  prepended to the binary CID"). `cid` is a binary DASL CID (`dasl-cid`,
  https://dasl.ing/cid.html, 2025-10-02): version `01`, codec `55` (raw) or `71` (DRISL), hash
  type `12` (SHA-256), hash size `20` (32), and a 32-byte digest. These restrictions are the
  normative DASL CID decoding steps: version must be 1, codec must be `0x55` or `0x71`, hash
  type must be `0x12`, hash size must be 32, and 32 digest bytes must be present. CBOR/c-42
  Appendix A, which is non-normative, also lists `0x51`; DASL CID rejects it, and we follow
  DASL. All these fields are single bytes below `0x80`, so the multiformats unsigned-varint
  and the SDNV encodings of CBOR/c-42 coincide here.
* **CID boundary: an explicit assumption, not a DRISL fact.** The DASL CID decoding algorithm
  reads 36 bytes and is silent about any bytes after the digest. CBOR/c-42 Appendix A
  (non-normative) describes the digest as "all remaining bytes", which together with hash size
  32 implies none follow. So the boundary is a profile parameter, `CidBoundary`:
  `.exact` (the payload is exactly `00` and the 36-byte CID) or `.prefix` (the payload is
  `00`, a 36-byte CID, then any bytes, which is all the decoding algorithm checks). The named
  profiles carry the assumption in their names. `Drisl.Tag42Payload` (`00` then any bytes)
  is a third, weaker shape. It is *not* DRISL under either assumption, and is named
  separately.
* **Floats:** "always … encoded as a 64-bit IEEE 754 binary floating-point". Infinities, NaNs
  (of any payload) and negative zero "must not be encoded". Positive zero and subnormals are
  allowed.
* **Simple values:** only `false`, `true`, `null` (20, 21, 22).

**ATProto core** (`Profile.atprotoCoreExactCid`): the atproto data model (`atproto-data-model`,
https://atproto.com/specs/data-model, pinned by SHA-256) uses DRISL-CBOR with floats "not
allowed in atproto" and integers "signed, 64-bit". So this profile is DRISL without floats and
with integers in `[-2^63, 2^63 - 1]`. It is **not** full atproto validity, which also has the
`blob` structure, the reserved `$` field names, and Lexicon constraints that need a schema.
`Profile.drislNoFloatsExactCid` is DRISL without floats and without the integer range.
The atproto text "binary serialization within DRISL-CBOR cid-link fields" settles the CID
boundary no further, so the ATProto profile also states `.exact` as an assumption.

References (`references.bib`): `drisl`, `dasl-cid`, `cborc42`, `atproto-data-model`, `rfc8949`.

Decision procedure: `check P w` decodes `w` (`Cbor.decode`), checks the value, and re-encodes
it. `Thms`: `check_iff`, and `language_le_wellFormed`.
-/

@[expose] public section

namespace Silmaril.Formats.Cbor.Drisl

/-- The assumption about bytes after the CID in a tag-42 payload (see the module doc). -/
inductive CidBoundary where
  /-- The payload is exactly `00` and the 36-byte CID. -/
  | exact
  /-- The payload is `00`, a 36-byte CID, and then any bytes. -/
  | prefix
  deriving DecidableEq, Repr

/-- A DRISL profile: whether 64-bit floats are allowed, whether integers are limited to the
signed 64-bit range, and the CID-boundary assumption. -/
structure Profile where
  floats : Bool
  int64 : Bool
  cid : CidBoundary
  deriving DecidableEq, Repr

/-- DRISL (2026-10-22), with the assumption that a tag-42 payload is exactly `00` + CID. -/
def Profile.drislExactCid : Profile := ⟨true, false, .exact⟩
/-- DRISL (2026-10-22), with the assumption that bytes may follow the CID. -/
def Profile.drislCidPrefix : Profile := ⟨true, false, .prefix⟩
/-- DRISL without floats, exact CID boundary. -/
def Profile.drislNoFloatsExactCid : Profile := ⟨false, false, .exact⟩
/-- The CBOR-level core of the atproto data model (no floats, signed 64-bit integers), exact CID
boundary. -/
def Profile.atprotoCoreExactCid : Profile := ⟨false, true, .exact⟩

/-- A binary DASL CID: `01`, codec `55` or `71`, `12`, `20`, and a 32-byte SHA-256 digest. -/
def IsDaslCid (c : List UInt8) : Prop :=
  ∃ codec digest, c = 0x01 :: codec :: 0x12 :: 0x20 :: digest ∧
    (codec = 0x55 ∨ codec = 0x71) ∧ digest.length = 32

/-- `IsDaslCid`, as a check. -/
def isDaslCid : List UInt8 → Bool
  | 0x01 :: codec :: 0x12 :: 0x20 :: digest =>
    (codec == 0x55 || codec == 0x71) && digest.length == 32
  | _ => false

/-- The relaxed tag-42 payload shape: `00` and then any bytes. *Not* DRISL. -/
def Tag42Payload (b : List UInt8) : Prop := ∃ rest, b = 0x00 :: rest

/-- The DRISL tag-42 payload under a CID-boundary assumption: `00` and a binary DASL CID,
followed by nothing (`.exact`) or by any bytes (`.prefix`). -/
def isCidPayload : CidBoundary → List UInt8 → Bool
  | .exact, 0x00 :: cid => isDaslCid cid
  | .prefix, 0x00 :: cid => isDaslCid (cid.take 36)
  | _, _ => false

/-- Strict bytewise lexicographic order (a proper prefix comes first). -/
def lexLt : List UInt8 → List UInt8 → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: x, b :: y => a < b || (a == b && lexLt x y)

/-- A list strictly increasing in `lexLt`. -/
def strictlySorted : List (List UInt8) → Bool
  | a :: b :: rest => lexLt a b && strictlySorted (b :: rest)
  | _ => true

/-- A 64-bit float DRISL allows: not an infinity or NaN (exponent all ones), not `-0.0`. -/
def okFloat64 (bits : Nat) : Bool :=
  bits < 2 ^ 64 && bits / 2 ^ 52 % 2 ^ 11 != 2047 && bits != 2 ^ 63

/-- An integer argument the profile allows. -/
def okInt (P : Profile) (n : Nat) : Bool := n < 2 ^ 64 && (!P.int64 || n < 2 ^ 63)

/-- Whether a value is a text string. -/
def isText : Value → Bool
  | .text _ => true
  | _ => false

mutual

/-- A value the profile allows (the map-key order is checked on encodings). -/
def ok (P : Profile) : Value → Bool
  | .uint n | .nint n => okInt P n
  | .bytes b => decide (b.length < 2 ^ 64)
  | .text t => decide (t.length < 2 ^ 64) && Utf8.isWellFormed t
  | .array xs => decide (xs.length < 2 ^ 64) && okList P xs
  | .map kvs => decide (kvs.length < 2 ^ 64) && okMap P kvs &&
      strictlySorted (kvs.map fun kv => kv.1.encode)
  | .tag 42 (.bytes b) => decide (b.length < 2 ^ 64) && isCidPayload P.cid b
  | .tag _ _ => false
  | .simple n => n == 20 || n == 21 || n == 22
  | .float w bits => P.floats && w == 8 && okFloat64 bits

/-- Every item is allowed. -/
def okList (P : Profile) : List Value → Bool
  | [] => true
  | v :: vs => ok P v && okList P vs

/-- Every key is an allowed text string and every value is allowed. -/
def okMap (P : Profile) : List (Value × Value) → Bool
  | [] => true
  | (k, v) :: kvs => isText k && ok P k && ok P v && okMap P kvs

end

/-- The byte strings of the profile: deterministic encodings of allowed values. -/
def language (P : Profile) : Language UInt8 := {w | ∃ v, ok P v = true ∧ v.encode = w}

/-- Decide membership: decode, check the value, re-encode. -/
def check (P : Profile) (w : List UInt8) : Bool :=
  match decode w with
  | some v => ok P v && v.encode == w
  | none => false

end Silmaril.Formats.Cbor.Drisl

end

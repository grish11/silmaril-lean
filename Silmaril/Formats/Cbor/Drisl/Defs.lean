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
  prepended to the binary CID").
* **CIDs: an explicit link rule** (`LinkRule`), with two orthogonal parts.
  - **Codecs.** The allowed content codecs. DASL CID (`dasl-cid`, https://dasl.ing/cid.html,
    2025-10-02) allows `55` (raw) and `71` (DRISL). CBOR/c-42 Appendix A (non-normative) also
    lists `51`; DASL rejects it, and so do we.
  - **Hashes.** The allowed `(multihash code, digest length in bytes)` *pairs*. A CID is
    `01 codec code length digest` (DASL CID decoding steps). Its declared `length` must be one
    of the allowed pairs *together with its code*, and the digest must have exactly that many
    bytes. No hash function is assumed to have a single length: a profile that also allowed a
    truncated digest would list a second pair with the same code. The pinned DASL pair is
    `(12, 32)` (SHA-256, "hash size … any value other than 32 … throw an error"). BDASL
    (`bdasl`, https://dasl.ing/bdasl.html, last updated 2026-10-19, status Stabilising) parses
    "the same as for DASL CIDs with one modification": the hash type "may also be equal to
    `0x1e` (BLAKE3)". The 32-byte hash-size step is unchanged, so its pairs are `(12, 32)` and
    `(1E, 32)`. The empty pair set allows no CID at all, so it rejects *every* tag-42 value
    (`LinkRule.none`, DRISL without links), while values without links are unaffected.
  - Fields are parsed as single-byte varints: the code and length bytes must be below `0x80`.
    That is the case for every pair used here, and a pair with a larger code or length matches
    nothing.
* **CID boundary: an explicit assumption, not a DRISL fact.** The DASL CID decoding algorithm
  reads exactly the declared digest and is silent about any bytes after it. CBOR/c-42
  Appendix A (non-normative) describes the digest as "all remaining bytes". So the boundary is a
  profile parameter, `CidBoundary`, orthogonal to the link rule:
  - `.exact`: no bytes follow the digest, so the declared length equals the number of
    remaining bytes;
  - `.prefix`: the digest is the first `length` remaining bytes, and any further bytes are
    explicit *trailing* bytes, which this assumption allows.
  `CidPayload` states both parts (the digest consumed and the trailing bytes) separately. The
  named profiles carry the assumption in their names. `Drisl.Tag42Payload` (`00` then any
  bytes) is weaker still, is DRISL under no assumption, and is named separately.
* **Floats:** "always … encoded as a 64-bit IEEE 754 binary floating-point". Infinities, NaNs
  (of any payload) and negative zero "must not be encoded". Positive zero and subnormals are
  allowed.
* **Simple values:** only `false`, `true`, `null` (20, 21, 22).

**ATProto core** (`Profile.atprotoCoreExactCid`): the atproto data model (`atproto-data-model`,
https://atproto.com/specs/data-model, pinned by SHA-256) uses DRISL-CBOR with floats "not
allowed in atproto" and integers "signed, 64-bit". So this profile is DRISL without floats and
with integers in `[-2^63, 2^63 - 1]`. It is **not** full atproto validity, which also has the
`blob` structure, the reserved `$` field names, and Lexicon constraints that need a schema.
`Profile.drislNoFloatsExactCid` is DRISL without floats and without the integer range. The
ATProto profile keeps the DASL link rule: atproto's "blessed" CIDs are v1, codec `71` or `55`,
and "sha-256 (0x12) with size of 256 bits (0x20 bytes)".
The atproto text "binary serialization within DRISL-CBOR cid-link fields" settles the CID
boundary no further, so the ATProto profile also states `.exact` as an assumption.

References (`references.bib`): `drisl`, `dasl-cid`, `bdasl`, `cborc42`, `atproto-data-model`, `rfc8949`.

Decision procedure: `check P w` decodes `w` (`Cbor.decode`), checks the value, and re-encodes
it. `Thms`: `check_iff`, and `language_le_wellFormed`.
-/

@[expose] public section

namespace Silmaril.Formats.Cbor.Drisl

/-- The assumption about bytes after the digest of a CID in a tag-42 payload. -/
inductive CidBoundary where
  /-- No bytes follow the digest. -/
  | exact
  /-- Any bytes may follow the digest (they are trailing, not digest). -/
  | prefix
  deriving DecidableEq, Repr

/-- Which CIDs a profile allows in tag 42: content codecs and `(multihash code, digest length
in bytes)` pairs. -/
structure LinkRule where
  codecs : List UInt8
  hashes : List (UInt8 × Nat)
  deriving DecidableEq, Repr

/-- DASL CIDs: codecs raw and DRISL, SHA-256 with 32-byte digests. -/
def LinkRule.dasl : LinkRule := ⟨[0x55, 0x71], [(0x12, 32)]⟩
/-- BDASL CIDs: as DASL, and BLAKE3 with 32-byte digests. -/
def LinkRule.bdasl : LinkRule := ⟨[0x55, 0x71], [(0x12, 32), (0x1E, 32)]⟩
/-- No links: the empty pair set, so no tag-42 value is allowed. -/
def LinkRule.none : LinkRule := ⟨[0x55, 0x71], []⟩

/-- A DRISL profile: whether 64-bit floats are allowed, whether integers are limited to the
signed 64-bit range, the CID-boundary assumption, and the link rule. -/
structure Profile where
  floats : Bool
  int64 : Bool
  cid : CidBoundary
  links : LinkRule
  deriving DecidableEq, Repr

/-- DRISL (2026-10-22) with DASL CIDs, assuming nothing follows a CID's digest. -/
def Profile.drislExactCid : Profile := ⟨true, false, .exact, .dasl⟩
/-- DRISL (2026-10-22) with DASL CIDs, allowing bytes after a CID's digest. -/
def Profile.drislCidPrefix : Profile := ⟨true, false, .prefix, .dasl⟩
/-- DRISL with BDASL CIDs (SHA-256 or BLAKE3), exact CID boundary. -/
def Profile.drislBdaslExactCid : Profile := ⟨true, false, .exact, .bdasl⟩
/-- DRISL with BDASL CIDs, allowing bytes after a CID's digest. -/
def Profile.drislBdaslCidPrefix : Profile := ⟨true, false, .prefix, .bdasl⟩
/-- DRISL without links: no tag 42 at all (the boundary is then irrelevant). -/
def Profile.drislNoLinks : Profile := ⟨true, false, .exact, .none⟩
/-- DRISL without floats, DASL CIDs, exact CID boundary. -/
def Profile.drislNoFloatsExactCid : Profile := ⟨false, false, .exact, .dasl⟩
/-- The CBOR-level core of the atproto data model (no floats, signed 64-bit integers, DASL
CIDs), exact CID boundary. -/
def Profile.atprotoCoreExactCid : Profile := ⟨false, true, .exact, .dasl⟩

/-- A tag-42 payload the boundary and link rule allow, with its parts named: `00`, version
`01`, a codec, a multihash code and declared digest length, the digest, and the trailing bytes
(none under `.exact`). -/
def CidPayload (B : CidBoundary) (R : LinkRule) (b : List UInt8) : Prop :=
  ∃ codec code len digest trailing,
    b = 0x00 :: 0x01 :: codec :: code :: len :: (digest ++ trailing) ∧
    codec ∈ R.codecs ∧ code.toNat < 0x80 ∧ len.toNat < 0x80 ∧ (code, len.toNat) ∈ R.hashes ∧
    digest.length = len.toNat ∧ (B = .exact → trailing = [])

/-- `CidPayload`, as a check. -/
def cidOk (B : CidBoundary) (R : LinkRule) : List UInt8 → Bool
  | 0x00 :: 0x01 :: codec :: code :: len :: rest =>
    decide (codec ∈ R.codecs) && decide (code.toNat < 0x80) && decide (len.toNat < 0x80) &&
      decide ((code, len.toNat) ∈ R.hashes) &&
      match B with
      | .exact => rest.length == len.toNat
      | .prefix => decide (len.toNat ≤ rest.length)
  | _ => false

/-- The DASL CIDs of the earlier, fixed definition: `01`, codec `55` or `71`, `12`, `20`, and a
32-byte digest (`Thms`: `cidOk_dasl_exact_iff`). -/
def IsDaslCid (c : List UInt8) : Prop :=
  ∃ codec digest, c = 0x01 :: codec :: 0x12 :: 0x20 :: digest ∧
    (codec = 0x55 ∨ codec = 0x71) ∧ digest.length = 32

/-- The relaxed tag-42 payload shape: `00` and then any bytes. *Not* DRISL. -/
def Tag42Payload (b : List UInt8) : Prop := ∃ rest, b = 0x00 :: rest

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
  | .tag 42 (.bytes b) => decide (b.length < 2 ^ 64) && cidOk P.cid P.links b
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

module

public import Silmaril.Formats.Cbor.Value.Defs
public import Silmaril.Semantics.StreamBounds.Defs

/-!
# CBOR event streams

A CBOR data item as a stream of *events*, in the order a streaming reader meets them. This is
the semantic event interface for consumers, and for interface representations (WIT variants)
built on it. The events are at the level of heads, so the structure the bytes show is kept:

* `uint n`, `nint n` (`-1 - n`), `simple n`, `float width bits`: scalars, with their head
  argument, simple value, and float width and raw bits. Payloads are not normalized to the
  generic data model of RFC 8949 §2.
* `bytes b`, `text t`: definite-length strings; inside an indefinite-length string they are its
  chunks. Text is raw bytes; UTF-8 validity is a profile's business.
* `beginIndefBytes`, `beginIndefText`, `endIndefString`: an indefinite-length string (`5F`,
  `7F`) and the `break` that ends it.
* `beginArray len`, `endArray len`, `beginMap len`, `endMap len`: containers, with `len` the
  definite count of items or pairs, or `none` for indefinite length. The end event is
  *always* present. For definite containers it is synthetic and occupies no bytes; for
  indefinite ones it is the `break` byte `FF`. So every container is bracketed, as in JSON
  events (`Silmaril.Formats.JsonEvents`).
* `tag n`: a tag, followed by the events of its single content item. Tags are not brackets.

`ItemEv es` is the grammar of the event stream of one item, mirroring `Cbor.Item` (RFC 8949
§3), with arguments below `2^64`. `encodeEvents` writes each event with shortest heads.
`Thms` proves that the bytes of a valid event stream are one well-formed item and that
`decodeEvents` recovers the events from them (so `encodeEvents` is injective on event streams).
`Value.toEvents` gives the events of a definite-length value, and their bytes are `Value.encode`.

Not here: a bijection between event streams and *all* well-formed bytes. Bytes with
non-shortest heads (`18 00`) decode to the same events as their shortest form, so events
determine bytes only up to argument width.
-/

@[expose] public section

namespace Silmaril.Formats.Cbor

/-- The events of a streamed CBOR item. -/
inductive Event where
  | uint (n : Nat)
  | nint (n : Nat)
  | bytes (b : List UInt8)
  | text (t : List UInt8)
  | beginIndefBytes
  | beginIndefText
  | endIndefString
  | beginArray (len : Option Nat)
  | endArray (len : Option Nat)
  | beginMap (len : Option Nat)
  | endMap (len : Option Nat)
  | tag (n : Nat)
  | simple (n : Nat)
  | float (width bits : Nat)
  deriving DecidableEq, Repr

/-- How an event changes the container nesting depth. -/
def Event.kind : Event → Silmaril.Streams.BracketKind
  | .beginArray _ | .beginMap _ | .beginIndefBytes | .beginIndefText => .opening
  | .endArray _ | .endMap _ | .endIndefString => .closing
  | _ => .neutral

/-- The bytes of one event (shortest heads; synthetic ends of definite containers are empty). -/
def Event.encode : Event → List UInt8
  | .uint n => encodeHead 0 n
  | .nint n => encodeHead 1 n
  | .bytes b => encodeHead 2 b.length ++ b
  | .text t => encodeHead 3 t.length ++ t
  | .beginIndefBytes => [0x5F]
  | .beginIndefText => [0x7F]
  | .endIndefString => [0xFF]
  | .beginArray (some n) => encodeHead 4 n
  | .beginArray none => [0x9F]
  | .endArray (some _) => []
  | .endArray none => [0xFF]
  | .beginMap (some n) => encodeHead 5 n
  | .beginMap none => [0xBF]
  | .endMap (some _) => []
  | .endMap none => [0xFF]
  | .tag n => encodeHead 6 n
  | .simple n => if n < 24 then [UInt8.ofNat (0xE0 + n)] else [0xF8, UInt8.ofNat n]
  | .float w bits => UInt8.ofNat (0xE0 + floatAi w) :: beBytes w bits

/-- The bytes of an event stream. -/
def encodeEvents (es : List Event) : List UInt8 := es.flatMap Event.encode

mutual

/-- The event stream of one item. -/
inductive ItemEv : List Event → Prop
  | uint {n} : n < 2 ^ 64 → ItemEv [.uint n]
  | nint {n} : n < 2 ^ 64 → ItemEv [.nint n]
  | bytes {b : List UInt8} : b.length < 2 ^ 64 → ItemEv [.bytes b]
  | text {t : List UInt8} : t.length < 2 ^ 64 → ItemEv [.text t]
  | indefBytes {cs : List (List UInt8)} : (∀ c ∈ cs, c.length < 2 ^ 64) →
      ItemEv (.beginIndefBytes :: cs.map .bytes ++ [.endIndefString])
  | indefText {cs : List (List UInt8)} : (∀ c ∈ cs, c.length < 2 ^ 64) →
      ItemEv (.beginIndefText :: cs.map .text ++ [.endIndefString])
  | array {n es} : n < 2 ^ 64 → ItemsEv n es →
      ItemEv (.beginArray (some n) :: es ++ [.endArray (some n)])
  | indefArray {k es} : ItemsEv k es → ItemEv (.beginArray none :: es ++ [.endArray none])
  | map {n es} : n < 2 ^ 64 → ItemsEv (2 * n) es →
      ItemEv (.beginMap (some n) :: es ++ [.endMap (some n)])
  | indefMap {k es} : ItemsEv (2 * k) es → ItemEv (.beginMap none :: es ++ [.endMap none])
  | tag {n es} : n < 2 ^ 64 → ItemEv es → ItemEv (.tag n :: es)
  | simple {n} : n < 24 ∨ (32 ≤ n ∧ n < 256) → ItemEv [.simple n]
  | float {w bits} : (w = 2 ∨ w = 4 ∨ w = 8) → bits < 256 ^ w → ItemEv [.float w bits]

/-- `k` consecutive item event streams. -/
inductive ItemsEv : Nat → List Event → Prop
  | nil : ItemsEv 0 []
  | cons {k es fs} : ItemEv es → ItemsEv k fs → ItemsEv (k + 1) (es ++ fs)

end

/-- The event streams of single CBOR items. -/
def Events.language : Language Event := {es | ItemEv es}

mutual

/-- The events of a definite-length value. -/
def Value.toEvents : Value → List Event
  | .uint n => [.uint n]
  | .nint n => [.nint n]
  | .bytes b => [.bytes b]
  | .text t => [.text t]
  | .array xs => .beginArray (some xs.length) :: listEvents xs ++ [.endArray (some xs.length)]
  | .map kvs => .beginMap (some kvs.length) :: mapEvents kvs ++ [.endMap (some kvs.length)]
  | .tag n v => .tag n :: v.toEvents
  | .simple n => [.simple n]
  | .float w bits => [.float w bits]

/-- The events of a list of items. -/
def listEvents : List Value → List Event
  | [] => []
  | v :: vs => v.toEvents ++ listEvents vs

/-- The events of key-value pairs. -/
def mapEvents : List (Value × Value) → List Event
  | [] => []
  | (k, v) :: kvs => k.toEvents ++ v.toEvents ++ mapEvents kvs

end

/-! ## Decoding bytes to events -/

mutual

/-- Read the events of one item, with fuel. -/
def decodeEv : Nat → List UInt8 → Option (List Event × List UInt8)
  | 0, _ => none
  | _ + 1, [] => none
  | n + 1, b :: r =>
    let mt := b.toNat / 32
    let ai := b.toNat % 32
    if ai = 31 then
      if mt = 2 then (decodeChunks n 2 r).map fun p =>
        (.beginIndefBytes :: p.1.map .bytes ++ [.endIndefString], p.2)
      else if mt = 3 then (decodeChunks n 3 r).map fun p =>
        (.beginIndefText :: p.1.map .text ++ [.endIndefString], p.2)
      else if mt = 4 then (decodeEvUntilBreak n r).map fun p =>
        (.beginArray none :: p.1 ++ [.endArray none], p.2)
      else if mt = 5 then (decodeEvPairsUntilBreak n r).map fun p =>
        (.beginMap none :: p.1 ++ [.endMap none], p.2)
      else none
    else if 28 ≤ ai then none
    else if mt = 7 then
      if ai < 24 then some ([.simple ai], r)
      else (readArg ai r).bind fun ar =>
        if ai = 24 then (if 32 ≤ ar.1 then some ([.simple ar.1], ar.2) else none)
        else some ([.float (aiWidth ai) ar.1], ar.2)
    else (readArg ai r).bind fun ar =>
      if mt = 0 then some ([.uint ar.1], ar.2)
      else if mt = 1 then some ([.nint ar.1], ar.2)
      else if mt = 2 then
        (if ar.1 ≤ ar.2.length then some ([.bytes (ar.2.take ar.1)], ar.2.drop ar.1) else none)
      else if mt = 3 then
        (if ar.1 ≤ ar.2.length then some ([.text (ar.2.take ar.1)], ar.2.drop ar.1) else none)
      else if mt = 4 then (decodeEvN n ar.1 ar.2).map fun p =>
        (.beginArray (some ar.1) :: p.1 ++ [.endArray (some ar.1)], p.2)
      else if mt = 5 then (decodeEvN n (2 * ar.1) ar.2).map fun p =>
        (.beginMap (some ar.1) :: p.1 ++ [.endMap (some ar.1)], p.2)
      else (decodeEv n ar.2).map fun p => (.tag ar.1 :: p.1, p.2)

/-- Read the events of `k` items. -/
def decodeEvN : Nat → Nat → List UInt8 → Option (List Event × List UInt8)
  | _, 0, w => some ([], w)
  | 0, _ + 1, _ => none
  | f + 1, k + 1, w => (decodeEv f w).bind fun p =>
      (decodeEvN f k p.2).map fun q => (p.1 ++ q.1, q.2)

/-- Read item events up to and including `break` (the break itself is not returned). -/
def decodeEvUntilBreak : Nat → List UInt8 → Option (List Event × List UInt8)
  | 0, _ => none
  | _ + 1, [] => none
  | f + 1, b :: r =>
    if b = breakByte then some ([], r)
    else (decodeEv f (b :: r)).bind fun p =>
      (decodeEvUntilBreak f p.2).map fun q => (p.1 ++ q.1, q.2)

/-- Read key-value pair events up to and including `break`; a `break` in a value position
fails. -/
def decodeEvPairsUntilBreak : Nat → List UInt8 → Option (List Event × List UInt8)
  | 0, _ => none
  | _ + 1, [] => none
  | f + 1, b :: r =>
    if b = breakByte then some ([], r)
    else (decodeEv f (b :: r)).bind fun p => (decodeEv f p.2).bind fun q =>
      (decodeEvPairsUntilBreak f q.2).map fun s => (p.1 ++ q.1 ++ s.1, s.2)

/-- Read definite-length string chunks of major type `mt` up to and including `break`. -/
def decodeChunks : Nat → Nat → List UInt8 → Option (List (List UInt8) × List UInt8)
  | 0, _, _ => none
  | _ + 1, _, [] => none
  | f + 1, mt, b :: r =>
    if b = breakByte then some ([], r)
    else if b.toNat / 32 = mt ∧ b.toNat % 32 < 28 then
      (readArg (b.toNat % 32) r).bind fun ar =>
        if ar.1 ≤ ar.2.length then
          (decodeChunks f mt (ar.2.drop ar.1)).map fun q => (ar.2.take ar.1 :: q.1, q.2)
        else none
    else none

end

/-- Decode a whole input to the events of one item. -/
def decodeEvents (w : List UInt8) : Option (List Event) :=
  match decodeEv (2 * w.length + 2) w with
  | some (es, []) => some es
  | _ => none

end Silmaril.Formats.Cbor

end

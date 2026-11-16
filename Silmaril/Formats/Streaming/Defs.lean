module

public import Silmaril.Semantics.Acceptors.Defs
public import Silmaril.Semantics.StreamBounds.Defs
public import Silmaril.Formats.Utf8.Thms
public import Silmaril.Formats.JsonBytes.Depth.Thms
public import Silmaril.Formats.JsonLines.Thms
public import Silmaril.Formats.Cbor.WellFormed.Thms

/-!
# Incremental acceptors for the format languages

Instances of the incremental-acceptor API of `Silmaril.Semantics.Acceptors` (`process`,
`query`, `reset` over chunks with a `ChunkView`, for example `ByteArray`) for the byte
languages of `Silmaril.Formats`:

* `derivAcceptor r`: a genuinely incremental acceptor for a Mathlib regular expression over
  bytes. Its state is the Brzozowski derivative of `r` by the input so far, `process` takes
  derivatives byte by byte, and `query` asks whether the derivative accepts the empty word.
  It does not buffer the input. Its state is not size-bounded either: Mathlib's `deriv` does
  not simplify, so derivative terms can grow with the input.
* `utf8Acceptor := derivAcceptor Utf8.wellFormed`: streaming UTF-8 validation. A multi-byte
  sequence may be split across chunks.
* `jsonAcceptor p`, `jsonLinesAcceptor pol p`: the reference acceptors (`Acceptor.reference`)
  of the JSON and JSON Lines languages. They buffer the input and decide it with the proved
  deciders, so they are specifications, not efficient implementations.
* `cborAcceptor`: the reference acceptor of well-formed CBOR (`Cbor.wellFormed`, one item).
* `jsonDepthAcceptor p d`: `Acceptor.boundedReference` with the JSON language and the depth
  bound `JsonBytes.languageAt p d` (RFC 8259 §9). It is sound for the full language and
  complete only within the bound, the shape of a validator that rejects too-deep inputs.

`Thms` proves each one correct in the sense of `Silmaril.Semantics.Acceptors` /
`Silmaril.Semantics.StreamBounds`. None of this is a claim about a compiled component. It is the
specification a component's `accepted()` is to be checked against.
-/

@[expose] public section

namespace Silmaril.Formats.Streaming

open RegularExpression Silmaril

instance utf8Language.decidableMem (w : List UInt8) : Decidable (w ∈ Utf8.language) :=
  Utf8.IsWellFormed.decidable w

/-- The Brzozowski-derivative acceptor of a regular expression over bytes. -/
def derivAcceptor {χ : Type} [ChunkView χ UInt8] (r : RegularExpression UInt8) :
    Acceptor (RegularExpression UInt8) χ where
  init := r
  process s c := (ChunkView.toList c).foldl deriv s
  query s := (s.matchEpsilon, s)
  reset _ := r

/-- Streaming UTF-8 validation. -/
def utf8Acceptor {χ : Type} [ChunkView χ UInt8] : Acceptor (RegularExpression UInt8) χ :=
  derivAcceptor Utf8.wellFormed

/-- The reference acceptor of the JSON byte language. -/
def jsonAcceptor {χ : Type} [ChunkView χ UInt8] (p : JsonBytes.Profile) :
    Acceptor (List UInt8) χ :=
  Acceptor.reference (JsonBytes.language p)

/-- The reference acceptor of a JSON Lines language. -/
def jsonLinesAcceptor {χ : Type} [ChunkView χ UInt8] (pol : JsonLines.Policy)
    (p : JsonBytes.Profile) : Acceptor (List UInt8) χ :=
  Acceptor.reference (JsonLines.language pol p)

/-- The reference acceptor of well-formed single CBOR data items. -/
def cborAcceptor {χ : Type} [ChunkView χ UInt8] : Acceptor (List UInt8) χ :=
  Acceptor.reference Cbor.wellFormed

/-- The JSON acceptor that also rejects texts deeper than `d`. -/
def jsonDepthAcceptor {χ : Type} [ChunkView χ UInt8] (p : JsonBytes.Profile) (d : Nat) :
    Acceptor (List UInt8) χ :=
  Acceptor.boundedReference (JsonBytes.language p) (JsonBytes.languageAt p d)

end Silmaril.Formats.Streaming

end

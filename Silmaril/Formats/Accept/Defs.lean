module

public import Mathlib.Computability.Language
public import Cslib.Computability.Automata.Acceptors.Acceptor
public import Silmaril.Prelude.Bytes.Defs
public import Silmaril.Formats.Bytes

/-! # Accepted sets: byte languages, specifications, soundness and completeness

An *acceptor set* is the set of inputs some program accepts. This module fixes the vocabulary
that the Wasm and component acceptors (`Silmaril.Wasm.Game.Accept`,
`Silmaril.Wasi.Component.Accept`) share.

* `Lang α := Set α`: an acceptor set over any input type `α` (a language in the sense of
  `Silmaril.Semantics.Accept`, which supplies the Bool-checker and outcome-quantifier
  vocabulary; the set-level `Sound`/`Complete` below agree with its checker-level ones on
  `Silmaril.Accept.ofBool`, `Lang.sound_ofBool_iff`). A **specification** is another
  `Lang α`. An acceptor set `A` is **sound** for `S` when `A ⊆ S` (everything accepted is
  allowed), **complete** when `S ⊆ A` (everything allowed is accepted) and **exact** when
  `A = S`.
* `ByteLang := Language UInt8`: Mathlib's `Language` (`Set (List α)`) specialised to bytes. Its
  Kleene-algebra operations (`+`, `*`, `∗`, `map`) and every `Language`-valued construction
  (Mathlib's `DFA.accepts`, `NFA.accepts`, `RegularExpression.matches'`, CSLib's
  `Acceptor.language`) are byte languages without conversion.
* `BytesLike β`: a type whose values denote a finite byte string (`toBytes`), with instances
  for `List UInt8`, `Array UInt8`, `ByteArray`, `Silmaril.KBytes` (the kernel-readable byte
  tree) and `Silmaril.Formats.Bytes`. Membership of a bytes-like value in a byte language
  (`ByteLang.Accepts L b`, notation `b ∈ᴮ L`) is membership of its bytes. It is a predicate,
  not a `Membership` instance: Mathlib's `Membership (List UInt8) (Language UInt8)` fixes the
  element type (an `outParam`).
* `ByteLang.over L β`: the bytes-like values whose bytes `L` contains. `KBytes.toList` is not
  injective (one string has many trees), so this set is closed under equality of bytes
  rather than of terms.
* CSLib: `ByteLang` is a CSLib `Acceptor` over `UInt8`, and its `Acceptor.language` is itself.
  A CSLib acceptor `a` over bytes accepts the bytes-like `b` when `b ∈ᴮ Acceptor.language a`.

New definitions; `Language` is Mathlib's (`Mathlib.Computability.Language`), `Acceptor` is
CSLib's (`Cslib.Computability.Automata.Acceptors.Acceptor`).
-/

@[expose] public section

namespace Silmaril.Formats.Accept

universe u v

/-! ## Acceptor sets and specifications -/

/-- An acceptor set over the inputs `α`: the inputs some program accepts. -/
abbrev Lang (α : Type u) : Type u := Set α

namespace Lang

variable {α : Type u}

/-- **Soundness**: every accepted input satisfies the specification `S`. -/
def Sound (A S : Lang α) : Prop := A ⊆ S

/-- **Completeness**: every input satisfying the specification `S` is accepted. -/
def Complete (A S : Lang α) : Prop := S ⊆ A

/-- **Exactness**: the accepted inputs are exactly the specification's. -/
def Exact (A S : Lang α) : Prop := A = S

/-- Transport an acceptor set along an encoding `e : α → β` (the inputs `e x` for accepted
`x`). -/
def encode {β : Type v} (e : α → β) (A : Lang α) : Lang β := e '' A

/-- Pull an acceptor set back along a decoding `d : β → α` (the inputs whose decoding is
accepted). -/
def decode {β : Type v} (d : β → α) (A : Lang α) : Lang β := d ⁻¹' A

/-- Pull an acceptor set back along a partial decoding: the inputs that decode to an accepted
value (inputs that fail to decode are rejected). -/
def decode? {β : Type v} (d : β → Option α) (A : Lang α) : Lang β := {b | ∃ a ∈ A, d b = some a}

end Lang

/-! ## Byte languages -/

/-- A byte language: Mathlib's `Language` over the alphabet `UInt8`. -/
abbrev ByteLang : Type := Language UInt8

/-- A type whose values denote finite byte strings. -/
class BytesLike (β : Type u) where
  /-- The bytes, in order. -/
  toBytes : β → List UInt8

/-- A bytes-like type with a section: every byte string has a representative. -/
class LawfulBytesLike (β : Type u) extends BytesLike β where
  /-- A representative of the bytes. -/
  ofBytes : List UInt8 → β
  /-- The representative has exactly the given bytes. -/
  toBytes_ofBytes : ∀ bs, toBytes (ofBytes bs) = bs

export BytesLike (toBytes)

instance : LawfulBytesLike (List UInt8) where
  toBytes := id
  ofBytes := id
  toBytes_ofBytes _ := rfl

instance : LawfulBytesLike (Array UInt8) where
  toBytes := Array.toList
  ofBytes := List.toArray
  toBytes_ofBytes _ := rfl

instance : LawfulBytesLike ByteArray where
  toBytes b := b.data.toList
  ofBytes bs := ⟨bs.toArray⟩
  toBytes_ofBytes _ := rfl

instance : LawfulBytesLike Formats.Bytes where
  toBytes := Formats.Bytes.toList
  ofBytes := Formats.Bytes.ofList
  toBytes_ofBytes := Formats.Bytes.toList_ofList

/-- `KBytes` denote their `toList` (the specification of every `KBytes` operation). The
lawful instance (one leaf per string, `KBytes.ofList`) is in `Silmaril.Formats.Accept.Thms`. -/
instance : BytesLike KBytes := ⟨KBytes.toList⟩

namespace ByteLang

/-- The bytes-like value `b` is accepted by the byte language `L`: its bytes are in `L`. -/
def Accepts {β : Type u} [BytesLike β] (L : ByteLang) (b : β) : Prop := toBytes b ∈ L

/-- The bytes-like values of type `β` accepted by `L`. -/
def over (L : ByteLang) (β : Type u) [BytesLike β] : Lang β := {b | Accepts L b}

/-- The byte language of an acceptor set over a bytes-like type: the bytes of its members. -/
def ofLang {β : Type u} [BytesLike β] (A : Lang β) : ByteLang := toBytes '' A

/-- The byte language of an acceptor set of values under a byte encoding `e` (for instance a
canonical-ABI or wire encoding). -/
def ofEncoding {α : Type u} (e : α → List UInt8) (A : Lang α) : ByteLang := e '' A

/-- A byte language is a CSLib acceptor over bytes: it accepts its own strings. -/
instance : Cslib.Automata.Acceptor ByteLang UInt8 := ⟨fun L xs => xs ∈ L⟩

end ByteLang

/-- `b ∈ᴮ L`: the bytes of the bytes-like value `b` are in the byte language `L`. -/
scoped notation:50 b:51 " ∈ᴮ " L:51 => ByteLang.Accepts L b

end Silmaril.Formats.Accept

namespace Silmaril.KBytes

/-- One leaf holding the bytes `bs` (`leVal`, little-endian): a `KBytes` with exactly the bytes
`bs` (`Silmaril.Formats.Accept.toList_ofList`). -/
def ofList (bs : List UInt8) : KBytes := leaf bs.length (leVal bs)

end Silmaril.KBytes

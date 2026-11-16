module

public import Silmaril.Formats.Streaming.Defs
public import Silmaril.Semantics.Acceptors.Thms
public import Silmaril.Semantics.StreamBounds.Thms
import Silmaril.Proofs.Formats.Streaming.Basic

/-!
# Incremental acceptors for the format languages: correctness

* `derivAcceptor_correctInterleaved`: the derivative acceptor of `r` answers every query of
  every client trace (any interleaving of `process`, `query`, `reset`) with membership in
  `r.matches'` of the input since the last reset (`Acceptor.CorrectInterleaved`);
* `utf8Acceptor_correctInterleaved`: hence streaming UTF-8 validation is correct for
  `Utf8.language`;
* `jsonAcceptor_correctInterleaved`, `jsonLinesAcceptor_correctInterleaved`,
  `cborAcceptor_correctInterleaved`;
* `jsonDepthAcceptor_soundFold`, `jsonDepthAcceptor_completeFoldOn`: sound for the JSON
  language, complete on the depth bound; `jsonDepthAcceptor_not_completeFoldOn_univ`: not
  complete beyond it;
* examples on `ByteArray` chunks, including a UTF-8 sequence split across chunks.
-/

@[expose] public section

namespace Silmaril.Formats.Streaming

open Silmaril

theorem derivAcceptor_correctInterleaved {χ : Type} [ChunkView χ UInt8]
    (r : RegularExpression UInt8) [DecidablePred (· ∈ r.matches')] :
    (derivAcceptor (χ := χ) r).CorrectInterleaved r.matches' :=
  Silmaril.Proofs.Formats.Streaming.derivAcceptor_correctInterleaved r

theorem utf8Acceptor_correctInterleaved {χ : Type} [ChunkView χ UInt8] :
    (utf8Acceptor (χ := χ)).CorrectInterleaved Utf8.language :=
  derivAcceptor_correctInterleaved Utf8.wellFormed

theorem jsonAcceptor_correctInterleaved {χ : Type} [ChunkView χ UInt8] (p : JsonBytes.Profile) :
    (jsonAcceptor (χ := χ) p).CorrectInterleaved (JsonBytes.language p) :=
  Acceptor.reference_correctInterleaved

theorem jsonLinesAcceptor_correctInterleaved {χ : Type} [ChunkView χ UInt8]
    (pol : JsonLines.Policy) (p : JsonBytes.Profile) :
    (jsonLinesAcceptor (χ := χ) pol p).CorrectInterleaved (JsonLines.language pol p) :=
  Acceptor.reference_correctInterleaved

theorem cborAcceptor_correctInterleaved {χ : Type} [ChunkView χ UInt8] :
    (cborAcceptor (χ := χ)).CorrectInterleaved Cbor.wellFormed :=
  Acceptor.reference_correctInterleaved

theorem jsonDepthAcceptor_soundFold {χ : Type} [ChunkView χ UInt8] (p : JsonBytes.Profile)
    (d : Nat) : (jsonDepthAcceptor (χ := χ) p d).SoundFold (JsonBytes.language p) :=
  Acceptor.boundedReference_soundFold _ _

theorem jsonDepthAcceptor_completeFoldOn {χ : Type} [ChunkView χ UInt8] (p : JsonBytes.Profile)
    (d : Nat) : (jsonDepthAcceptor (χ := χ) p d).CompleteFoldOn (JsonBytes.language p)
      (JsonBytes.languageAt p d) :=
  Acceptor.boundedReference_completeFoldOn _ _

/-- `[]` is a JSON text of depth 1, so the depth-0 acceptor is not complete. -/
theorem jsonDepthAcceptor_not_completeFoldOn_univ :
    ¬ (jsonDepthAcceptor (χ := List UInt8) .rfc8259 0).CompleteFoldOn
      (JsonBytes.language .rfc8259) Set.univ := by
  intro h
  have := h [[0x5B, 0x5D]] (by decide +kernel) trivial
  revert this
  decide +kernel

/-! ## Examples on `ByteArray` chunks -/

section Examples

open Acceptor in
-- `é` = `C3 A9` split across two chunks: rejected after the first, accepted after both;
-- after a reset the empty input is accepted again.
example : ((utf8Acceptor (χ := ByteArray)).run (utf8Acceptor (χ := ByteArray)).init
    [.process [0xC3].toByteArray, .query, .process [0xA9].toByteArray, .query, .reset, .query]).1 =
    [false, true, true] := by decide +kernel

open Acceptor in
-- An encoded surrogate `ED A0 80` is rejected however it is chunked.
example : ((utf8Acceptor (χ := ByteArray)).run (utf8Acceptor (χ := ByteArray)).init
    [.process [0xED].toByteArray, .process [0xA0, 0x80].toByteArray, .query]).1 = [false] := by
  decide +kernel

open Acceptor in
-- JSON `[1]` fed as `[`, `1]`: not a text after the first chunk, a text after the second.
example : ((jsonAcceptor (χ := ByteArray) .rfc8259).run (jsonAcceptor (χ := ByteArray) .rfc8259).init
    [.process [0x5B].toByteArray, .query, .process [0x31, 0x5D].toByteArray, .query]).1 =
    [false, true] := by decide +kernel

open Acceptor in
-- CBOR `[_ 1]` (`9F 01 FF`) fed byte by byte: well-formed only once the break arrives.
example : ((cborAcceptor (χ := ByteArray)).run (cborAcceptor (χ := ByteArray)).init
    [.process [0x9F].toByteArray, .query, .process [0x01].toByteArray, .query,
      .process [0xFF].toByteArray, .query]).1 = [false, false, true] := by decide +kernel

end Examples

end Silmaril.Formats.Streaming

end

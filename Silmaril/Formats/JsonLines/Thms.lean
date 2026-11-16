module

public import Silmaril.Formats.JsonLines.Defs
public import Silmaril.Formats.JsonBytes.Depth.Thms
public import Silmaril.Formats.Utf8.Thms
public import Silmaril.Semantics.StreamBounds.Thms
import Silmaril.Proofs.Formats.JsonLines.Basic

/-!
# JSON Lines over bytes: lemmas

* `not_mem_lf_of_mem_lineOf`: no allowed line contains `0A`;
* `frameB_iff`: splitting at `0A` decides `frameLang pol L` whenever `L` is decided, hence
  the `Decidable` instances for `frameLang`, `language` and `languageAt`;
* `terminated_eq_frameItems`, `terminated_mem_itemBound_iff`: with a final newline the framing
  is `Silmaril.Streams.frameItems`, and the generic per-item bound on bytes is the per-line
  length bound `Silmaril.Accept.itemsWithin`;
* `lineOf_mono`, `frameLang_mono`, `iUnion_languageAt`: bounds on lines give bounds on files,
  and the depth-bounded files exhaust the language;
* `language_isWellFormed`: every JSON Lines file is UTF-8;
* examples for both dialects.
-/

@[expose] public section

namespace Silmaril.Formats.JsonLines

theorem not_mem_lf_of_mem_lineOf {pol : Policy} {L : Language UInt8} {w : List UInt8}
    (h : w ∈ lineOf pol L) : lf ∉ w :=
  Silmaril.Proofs.Formats.JsonLines.not_mem_lf_of_mem_lineOf h

theorem lineOf_mono {pol : Policy} {L L' : Language UInt8} (h : L ≤ L') :
    lineOf pol L ≤ lineOf pol L' :=
  Silmaril.Proofs.Formats.JsonLines.lineOf_mono h

theorem frameLang_mono {pol : Policy} {L L' : Language UInt8} (h : L ≤ L') :
    frameLang pol L ≤ frameLang pol L' :=
  Silmaril.Proofs.Formats.JsonLines.frameLang_mono h

theorem lineOfB_iff {pol : Policy} {ok : List UInt8 → Bool} {L : Language UInt8}
    (hok : ∀ w, ok w = true ↔ w ∈ L) {w : List UInt8} :
    lineOfB pol ok w = true ↔ w ∈ lineOf pol L :=
  Silmaril.Proofs.Formats.JsonLines.lineOfB_iff hok

/-- Splitting at line feeds decides the file language whenever the line contents are decided. -/
theorem frameB_iff {pol : Policy} {ok : List UInt8 → Bool} {L : Language UInt8}
    (hok : ∀ w, ok w = true ↔ w ∈ L) {w : List UInt8} :
    frameB pol ok w = true ↔ w ∈ frameLang pol L :=
  Silmaril.Proofs.Formats.JsonLines.frameB_iff hok

instance frameLang.decidableMem (pol : Policy) (L : Language UInt8)
    [∀ w, Decidable (w ∈ L)] (w : List UInt8) : Decidable (w ∈ frameLang pol L) :=
  decidable_of_iff _ (frameB_iff (ok := fun w => decide (w ∈ L)) (fun _ => decide_eq_true_iff))

instance language.decidableMem (pol : Policy) (p : JsonBytes.Profile) (w : List UInt8) :
    Decidable (w ∈ language pol p) :=
  frameLang.decidableMem pol _ w

instance languageAt.decidableMem (pol : Policy) (p : JsonBytes.Profile) (d : Nat)
    (w : List UInt8) : Decidable (w ∈ languageAt pol p d) :=
  frameLang.decidableMem pol _ w

theorem terminated_eq_frameItems (lines : List (List UInt8)) :
    terminated lines = Silmaril.Streams.frameItems lf lines :=
  Silmaril.Proofs.Formats.JsonLines.terminated_eq_frameItems lines

/-- With terminated lines, the generic byte-level per-item bound is the per-line length bound. -/
theorem terminated_mem_itemBound_iff {pol : Policy} {L : Language UInt8}
    {lines : List (List UInt8)} (hl : ∀ l ∈ lines, l ∈ lineOf pol L) (n : ℕ) :
    terminated lines ∈ Silmaril.Streams.ItemBound (· == lf) n ↔
      lines ∈ Silmaril.Accept.itemsWithin List.length n :=
  Silmaril.Proofs.Formats.JsonLines.terminated_mem_itemBound_iff hl n

theorem iUnion_languageAt (pol : Policy) (p : JsonBytes.Profile) :
    (⋃ d, (languageAt pol p d : Set (List UInt8))) = language pol p :=
  Silmaril.Proofs.Formats.JsonLines.iUnion_languageAt pol p

theorem languageAt_le_language (pol : Policy) (p : JsonBytes.Profile) (d : Nat) :
    languageAt pol p d ≤ language pol p :=
  frameLang_mono (JsonBytes.languageAt_le_language p d)

/-- Every JSON Lines file is well-formed UTF-8. -/
theorem language_isWellFormed {pol : Policy} {p : JsonBytes.Profile} {w : List UInt8}
    (h : w ∈ language pol p) : Utf8.IsWellFormed w :=
  Silmaril.Proofs.Formats.JsonLines.language_isWellFormed h

/-! ## Examples -/

section Examples

-- `1⏎2⏎`: both dialects. `1⏎2`: JSON Lines only (NDJSON requires the final newline).
example : [0x31, 0x0A, 0x32, 0x0A] ∈ language .jsonLines .rfc8259 := by decide +kernel
example : [0x31, 0x0A, 0x32, 0x0A] ∈ language .ndjson .rfc8259 := by decide +kernel
example : [0x31, 0x0A, 0x32] ∈ language .jsonLines .rfc8259 := by decide +kernel
example : [0x31, 0x0A, 0x32] ∉ language .ndjson .rfc8259 := by decide +kernel
-- `1␍⏎2␍⏎`: CRLF line ends, in both dialects.
example : [0x31, 0x0D, 0x0A, 0x32, 0x0D, 0x0A] ∈ language .jsonLines .rfc8259 := by
  decide +kernel
example : [0x31, 0x0D, 0x0A, 0x32, 0x0D, 0x0A] ∈ language .ndjson .rfc8259 := by
  decide +kernel
-- `[1,␍2]⏎`: a `0D` inside the text is JSON whitespace (JSON Lines), not NDJSON.
example : [0x5B, 0x31, 0x2C, 0x0D, 0x32, 0x5D, 0x0A] ∈ language .jsonLines .rfc8259 := by
  decide +kernel
example : [0x5B, 0x31, 0x2C, 0x0D, 0x32, 0x5D, 0x0A] ∉ language .ndjson .rfc8259 := by
  decide +kernel
-- `[1,⏎2]`: valid JSON, but it spans two lines.
example : [0x5B, 0x31, 0x2C, 0x0A, 0x32, 0x5D] ∈ JsonBytes.language .rfc8259 := by
  decide +kernel
example : [0x5B, 0x31, 0x2C, 0x0A, 0x32, 0x5D] ∉ language .jsonLines .rfc8259 := by
  decide +kernel
-- Blank lines: `1⏎⏎2⏎` and `1⏎⏎` are rejected; a lenient NDJSON reader accepts them.
example : [0x31, 0x0A, 0x0A, 0x32, 0x0A] ∉ language .jsonLines .rfc8259 := by decide +kernel
example : [0x31, 0x0A, 0x0A] ∉ language .jsonLines .rfc8259 := by decide +kernel
example : [0x31, 0x0A, 0x0A, 0x32, 0x0A] ∈
    language { Policy.ndjson with blankLines := true } .rfc8259 := by decide +kernel
-- The empty file is zero lines; a lone `⏎` is one blank line.
example : ([] : List UInt8) ∈ language .jsonLines .rfc8259 := by decide +kernel
example : [0x0A] ∉ language .jsonLines .rfc8259 := by decide +kernel
-- Two values on one line, a BOM, and ill-formed UTF-8 in a string.
example : [0x31, 0x20, 0x32, 0x0A] ∉ language .jsonLines .rfc8259 := by decide +kernel
example : [0xEF, 0xBB, 0xBF, 0x31, 0x0A] ∉ language .jsonLines .rfc8259 := by decide +kernel
example : [0x22, 0xC0, 0x80, 0x22, 0x0A] ∉ language .jsonLines .rfc8259 := by decide +kernel
-- Per-line depth: `[[1]]⏎2⏎` has lines of depth 2 and 0.
example : [0x5B, 0x5B, 0x31, 0x5D, 0x5D, 0x0A, 0x32, 0x0A] ∈
    languageAt .jsonLines .rfc8259 2 := by decide +kernel
example : [0x5B, 0x5B, 0x31, 0x5D, 0x5D, 0x0A, 0x32, 0x0A] ∉
    languageAt .jsonLines .rfc8259 1 := by decide +kernel

end Examples

end Silmaril.Formats.JsonLines

end

module

public import Silmaril.Formats.SExp.Reader.Defs
import Silmaril.Proofs.Formats.SExp.Reader.Basic

/-!
# The shared Lisp-family reader: laws

For every dialect lexer `L`:

* **sound and complete**: `readPrefix L s = some (e, s')` exactly when the lexer emits, from `s`
  to `s'`, a token string that the phrase grammar `Gram` derives as `e` (`readPrefix_iff`);
  `read` additionally requires that only atmosphere follows (`read_iff`). The fuel is never the
  reason for a failure;
* **unambiguous and prefix-free**: a token string derives at most one datum, and no proper
  prefix of a datum's tokens is a datum (`gram_unique`, `gram_prefix_free`);
* **the encoding is closed**: when the lexer respects the dialect's `Notation` (markers occur only
  as the heads of their own opening or prefix tokens), every datum read is `wf`
  (`wf_of_read`, `wf_of_readPrefix`);
* **roundtrip**: when the dialect discharges `PrintLaws` (each printed token lexes back),
  every well-formed datum is read back from its printed text, alone or followed by a delimiter
  (`read_print`, `readPrefix_print`).
-/

@[expose] public section

namespace Silmaril.Formats.SExpReader

open Silmaril.Proofs.Formats.SExp.Reader

universe u v
variable {A : Type u} {C : Type} {σ : Type v} [DecidableEq C]

theorem readPrefix_iff (L : Lexer A C σ) {s s' : σ} {e : SExp2 A} :
    readPrefix L s = some (e, s') ↔ ∃ ts, L.Emits s ts s' ∧ Gram .datum ts e :=
  Silmaril.Proofs.Formats.SExp.Reader.readPrefix_iff L

theorem read_iff (L : Lexer A C σ) {s : σ} {e : SExp2 A} :
    read L s = some e ↔
      ∃ ts r, L.Emits s ts r ∧ (L.next r).isEof = true ∧ Gram .datum ts e :=
  Silmaril.Proofs.Formats.SExp.Reader.read_iff L

theorem gram_prefix_free {ts us : List (Token A C)} {e e' : SExp2 A}
    (h : Gram .datum ts e) (h' : Gram .datum (ts ++ us) e') : us = [] ∧ e' = e :=
  Silmaril.Proofs.Formats.SExp.Reader.gram_prefix_free h h'

theorem gram_unique {ts : List (Token A C)} {e e' : SExp2 A}
    (h : Gram .datum ts e) (h' : Gram .datum ts e') : e' = e :=
  Silmaril.Proofs.Formats.SExp.Reader.gram_unique h h'

theorem wf_of_readPrefix (N : Notation A C) {L : Lexer A C σ}
    (hok : ∀ s t s', L.step s = .token t s' → N.TokenOK t)
    {s s' : σ} {e : SExp2 A} (h : readPrefix L s = some (e, s')) : N.wf e = true :=
  Silmaril.Proofs.Formats.SExp.Reader.wf_of_readPrefix hok h

theorem wf_of_read (N : Notation A C) {L : Lexer A C σ}
    (hok : ∀ s t s', L.step s = .token t s' → N.TokenOK t)
    {s : σ} {e : SExp2 A} (h : read L s = some e) : N.wf e = true :=
  Silmaril.Proofs.Formats.SExp.Reader.wf_of_read hok h

/-- **Generic roundtrip.** -/
theorem read_print {N : Notation A C} {L : Lexer A C (List Char)}
    {text : Token A C → List Char} (hl : PrintLaws N L text) {e : SExp2 A}
    (he : N.wf e = true) : read L (print N text e) = some e :=
  Silmaril.Proofs.Formats.SExp.Reader.read_print hl he

/-- **Generic prefix roundtrip**: the reader stops exactly after a printed datum. -/
theorem readPrefix_print {N : Notation A C} {L : Lexer A C (List Char)}
    {text : Token A C → List Char} (hl : PrintLaws N L text) {e : SExp2 A}
    (he : N.wf e = true) {rest : List Char} (hrest : Follows text rest) :
    readPrefix L (print N text e ++ rest) = some (e, rest) :=
  Silmaril.Proofs.Formats.SExp.Reader.readPrefix_print hl he hrest

omit [DecidableEq C] in
/-- The printed tokens of a well-formed datum derive it. -/
theorem gram_tokens (N : Notation A C) {e : SExp2 A} (he : N.wf e = true) :
    Gram .datum (N.tokens e) e :=
  (Silmaril.Proofs.Formats.SExp.Reader.tokens_gram N e).1 he

end Silmaril.Formats.SExpReader

module

public import Silmaril.Formats.SExp.Dotted.Defs
public import Silmaril.Formats.SExp.Reader.Thms
public import Silmaril.Formats.Category.Thms
import Silmaril.Proofs.Formats.SExp.Dotted.Basic
import Silmaril.Proofs.Formats.SExp.Dotted.Legacy
import Silmaril.Proofs.Formats.SExp.Dotted.Lexical
public import Silmaril.Formats.SExp.Printer
public import Silmaril.Formats.Utf8.Thms

/-!
# Dotted S-expression text: laws

* **roundtrip**: every datum, proper or improper, is read back exactly from its printed text
  (`parse?_print`), also as a prefix followed by a delimiter (`parsePrefix?_print`); hence
  printing is injective (`print_injective`), so no symbol/string distinction is lost;
* **declarative grammar**: `parse? s = some e` exactly when `s` is atmosphere and lexemes
  (`Tokenizes`, `Lexeme`, `Gap`, `Trailing`, `Body`: inductive definitions with no executable
  function) whose tokens derive `e` in the phrase grammar `Gram` (`parse?_iff_tokenizes`);
* **grammar (executable lexer)**: `parse?` accepts exactly the texts whose token string (as lexed) derives a datum in
  the shared phrase grammar, followed only by atmosphere (`parse?_iff`); a derivation is unique
  (`SExpReader.gram_unique`);
* **bytes**: `decode` inverts `encode` for every datum, non-ASCII and control characters included
  (`decode_encode`); `decode` accepts only well-formed UTF-8 (`isUtf8_of_decode`), and on
  well-formed bytes it is `parse?` of the decoded text (`decode_iff`); the format relates
  `encode e` to `e` (`format_rel_encode`) and is unambiguous (`format_unambiguous`);
* **the older printer and parser**: strings are printed exactly as `SExpPrinter.printSExp2`
  prints them (`print_map_string`), so `parse?` reads all of its output, as strings
  (`parse?_printSExp2`); on every text the older checked printer produces, the older parser and
  `parse?` agree up to forgetting the symbol/string distinction (`agrees_on_printSExp2?`).
-/

@[expose] public section

namespace Silmaril.Formats.DottedSExp

open SExpReader

theorem printLaws : PrintLaws syntaxNotation lexer text :=
  Silmaril.Proofs.Formats.SExp.Dotted.printLaws

/-- Every datum has a written form. -/
theorem wf (e : Datum) : syntaxNotation.wf e = true :=
  (Silmaril.Proofs.Formats.SExp.Dotted.wf_all e).1

/-- **Roundtrip** for all dotted S-expressions. -/
theorem parse?_print (e : Datum) : parse? (print e) = some e := by
  simpa [parse?, print] using read_print printLaws (wf e)

/-- **Prefix roundtrip**: reading stops exactly after a printed datum. -/
theorem parsePrefix?_print (e : Datum) {rest : String}
    (h : rest.toList = [] ∨ (∃ r, rest.toList = ' ' :: r) ∨ ∃ r, rest.toList = ')' :: r) :
    parsePrefix? (print e ++ rest) = some (e, rest) := by
  have hf : Follows text rest.toList := by
    rcases h with h | ⟨r, h⟩ | ⟨r, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨r, h⟩)
    · exact Or.inr (Or.inr ⟨(), r, h⟩)
  have := readPrefix_print printLaws (wf e) hf
  simp [parsePrefix?, print, String.toList_append, this]

theorem print_injective : Function.Injective print := by
  intro a b h
  have := congrArg parse? h
  rwa [parse?_print, parse?_print, Option.some.injEq] at this

/-- **Grammar characterization** of `parse?`. -/
theorem parse?_iff (s : String) (e : Datum) :
    parse? s = some e ↔
      ∃ ts r, lexer.Emits s.toList ts r ∧ (lexer.next r).isEof = true ∧ Gram .datum ts e :=
  read_iff lexer

/-- The lexer implements the declarative lexical grammar. -/
theorem emits_iff_tokenizes (s : List Char) (ts : List (Token Atom Unit)) :
    (∃ r, lexer.Emits s ts r ∧ (lexer.next r).isEof = true) ↔ Tokenizes s ts :=
  Silmaril.Proofs.Formats.SExp.Dotted.emits_iff_tokenizes s ts

/-- **Declarative characterization** of the dotted text syntax. -/
theorem parse?_iff_tokenizes (s : String) (e : Datum) :
    parse? s = some e ↔ ∃ ts, Tokenizes s.toList ts ∧ Gram .datum ts e := by
  rw [parse?_iff]
  constructor
  · rintro ⟨ts, r, he, heof, hg⟩; exact ⟨ts, (emits_iff_tokenizes _ _).1 ⟨r, he, heof⟩, hg⟩
  · rintro ⟨ts, ht, hg⟩
    obtain ⟨r, he, heof⟩ := (emits_iff_tokenizes _ _).2 ht
    exact ⟨ts, r, he, heof, hg⟩

theorem format_unambiguous : format.Unambiguous := Format.ofDecoder_unambiguous _

/-! ## UTF-8 bytes -/

theorem fromUTF8?_toByteArray (s : String) : String.fromUTF8? s.toByteArray = some s := by
  simp [String.fromUTF8?, s.isValidUTF8]

/-- **Byte-level roundtrip.** -/
theorem decode_encode (e : Datum) : decode (encode e) = some e := by
  simp only [decode, encode, String.toUTF8_eq_toByteArray, fromUTF8?_toByteArray,
    Option.bind_some, parse?_print]

theorem decode_iff {b : Bytes} {e : Datum} :
    decode b = some e ↔ ∃ s, String.fromUTF8? b.data = some s ∧ parse? s = some e := by
  simp [decode, Option.bind_eq_some_iff]

/-- **Ill-formed UTF-8 is rejected.** -/
theorem isUtf8_of_decode {b : Bytes} {e : Datum} (h : decode b = some e) : b.IsUtf8 := by
  obtain ⟨s, hs, -⟩ := decode_iff.1 h
  have : (String.fromUTF8? b.data).isSome := by simp [hs]
  exact (Bytes.isUtf8_iff_isValidUTF8 b).2 (by
    unfold String.fromUTF8? at hs; split at hs <;> simp_all)

theorem decode_eq_none_of_not_utf8 {b : Bytes} (h : ¬ b.IsUtf8) : decode b = none := by
  cases hd : decode b with
  | none => rfl
  | some e => exact absurd (isUtf8_of_decode hd) h

theorem format_rel_encode (e : Datum) : format.rel (encode e) e :=
  (Format.ofDecoder_rel decode _ _).2 (decode_encode e)

/-! ## The older printer and parser (`SExpPrinter`, `SExpParser`) -/

/-- The dotted printer writes string atoms exactly as `SExpPrinter.printSExp2` does. -/
theorem print_map_string (v : SExp2 String) :
    print (v.map .string) = SExpPrinter.printSExp2 v :=
  Silmaril.Proofs.Formats.SExp.Dotted.print_map_string v

/-- `parse?` reads everything the older printer writes. -/
theorem parse?_printSExp2 (v : SExp2 String) :
    parse? (SExpPrinter.printSExp2 v) = some (v.map .string) := by
  rw [← print_map_string, parse?_print]

/-- On every text produced by the older checked printer, the older parser and `parse?` agree
after forgetting the symbol/string distinction. -/
theorem agrees_on_printSExp2? {v : SExp2 String} {t : String}
    (h : SExpPrinter.printSExp2? v = some t) :
    SExpParser.parseSExp2? t = some v ∧
      (parse? t).map (SExp2.map SExpParser.Lexeme.value) = some v := by
  refine ⟨SExpPrinter.printSExp2?_sound h, ?_⟩
  have ht : t = SExpPrinter.printSExp2 v := by
    simp only [SExpPrinter.printSExp2?] at h; split at h <;> simp_all
  subst ht
  rw [parse?_printSExp2]
  simp only [Option.map_some, Option.some.injEq]
  clear h
  induction v with
  | nil => rfl
  | atom => rfl
  | cons a d iha ihd => simp [SExp2.map, iha, ihd]

end Silmaril.Formats.DottedSExp

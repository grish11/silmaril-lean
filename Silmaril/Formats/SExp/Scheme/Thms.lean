module

public import Silmaril.Formats.SExp.Scheme.Defs
public import Silmaril.Formats.SExp.SchemeFamily.Thms
import Silmaril.Proofs.Formats.SExp.Scheme.Basic

/-!
# Scheme (R7RS-small) data: laws

* **roundtrip**: every well-formed, valid datum (proper or improper; vectors and bytevectors
  included) is read back from its printed text (`parse?_print`), also as a prefix
  (`parsePrefix?_print`); so `print` is injective on such data;
* **closure**: every datum read is well formed and valid (`wf_of_parse?`);
* **grammar**: `parse?` accepts exactly the texts whose lexed tokens derive a datum in the shared
  phrase grammar, followed only by atmosphere, and whose datum is valid (`parse?_iff`).
-/

@[expose] public section

namespace Silmaril.Formats.Scheme

open SExpReader

theorem laws : dialect.Laws := Silmaril.Proofs.Formats.SExp.Scheme.laws

theorem printLaws : PrintLaws syntaxNotation lexer text := SchemeFamily.printLaws laws

theorem parse?_print {e : Datum} (hwf : syntaxNotation.wf e = true) (hv : Valid e = true) :
    parse? (print e) = some e := by
  have := SchemeFamily.read_print laws hwf
  simp only [parse?, print, String.toList_ofList]
  rw [this]
  simp [hv]

theorem parsePrefix?_print {e : Datum} (hwf : syntaxNotation.wf e = true) (hv : Valid e = true)
    {rest : String} (hrest : Follows text rest.toList) :
    parsePrefix? (print e ++ rest) = some (e, rest) := by
  have := readPrefix_print printLaws hwf hrest
  simp only [parsePrefix?, print, String.toList_append, String.toList_ofList]
  rw [this]
  simp [hv]

theorem wf_of_parse? {s : String} {e : Datum} (h : parse? s = some e) :
    syntaxNotation.wf e = true ∧ Valid e = true := by
  simp only [parse?] at h
  split at h
  · rename_i e' hr
    split at h
    · cases h; exact ⟨SchemeFamily.wf_of_read laws hr, by assumption⟩
    · cases h
  · cases h

theorem parse?_iff (s : String) (e : Datum) :
    parse? s = some e ↔
      (∃ ts r, lexer.Emits s.toList ts r ∧ (lexer.next r).isEof = true ∧ Gram .datum ts e) ∧
        Valid e = true := by
  rw [← read_iff]
  simp only [parse?]
  constructor
  · intro h
    split at h
    · split at h
      · cases h; exact ⟨by assumption, by assumption⟩
      · cases h
    · cases h
  · rintro ⟨h, hv⟩
    rw [h]; simp [hv]

theorem print_injective {a b : Datum} (ha : syntaxNotation.wf a = true) (hav : Valid a = true)
    (hb : syntaxNotation.wf b = true) (hbv : Valid b = true) (h : print a = print b) : a = b := by
  have := congrArg parse? h
  rwa [parse?_print ha hav, parse?_print hb hbv, Option.some.injEq] at this

end Silmaril.Formats.Scheme

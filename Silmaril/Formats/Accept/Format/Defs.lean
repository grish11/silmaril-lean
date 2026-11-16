module

public import Silmaril.Formats.Accept.Defs
public import Silmaril.Formats.Category.Defs

/-! # Byte languages of formats

A format of `Silmaril.Formats` (`Format`: a span `Bytes ← Derivation → Ast`, the proof-relevant
parsing relation) determines a byte language. Its **valid inputs** are the byte strings that some
derivation produces (`Format.lang`), so `w ∈ F.lang` iff `w` parses to some AST
(`Format.mem_lang_iff`). Validity forgets the AST and the derivation. For a parser presented by
`Format.ofDecoder decode`, the language is the set of inputs on which `decode` succeeds
(`Format.lang_ofDecoder`).

`Format.ofLanguage L` is the converse: the format whose derivations are the members of a byte
language and whose AST is trivial. Its language is `L` (`Format.lang_ofLanguage`). With it, the
JSON byte language of `Silmaril.Formats.JsonBytes` is a format.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Formats.Format

open Silmaril.Formats.Accept

/-- **The valid inputs of a format**: the byte strings some derivation produces. -/
def lang (F : Format) : ByteLang := {w | ∃ d, (F.bytes d).toList = w}

/-- The format of a byte language: derivations are its members, the AST is trivial. -/
def ofLanguage (L : ByteLang) : Format :=
  ofRelation (A := Unit) fun b _ => b.toList ∈ L

end Silmaril.Formats.Format

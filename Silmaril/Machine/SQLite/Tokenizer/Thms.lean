module

public import Silmaril.Machine.SQLite.Tokenizer.Defs
import Silmaril.Proofs.Machine.SQLite.Tokenizer.Correctness

public section

namespace Silmaril.Machine.SQLite.Tokenizer

theorem scan_iff (input : State) (tokens : List Token) :
    scan input = .ok tokens ↔ Lexes input tokens :=
  ⟨Proofs.Machine.SQLite.Tokenizer.scan_sound, Proofs.Machine.SQLite.Tokenizer.scan_complete⟩

theorem tokenize_iff (text : String) (tokens : List Token) :
    tokenize text = .ok tokens ↔ Lexes text.toList tokens :=
  scan_iff text.toList tokens

theorem lexes_render {tokens : List Token} (h : ∀ token ∈ tokens, Token.Canonical token) :
    Lexes (render tokens) tokens :=
  Proofs.Machine.SQLite.Tokenizer.lexes_render h

end Silmaril.Machine.SQLite.Tokenizer

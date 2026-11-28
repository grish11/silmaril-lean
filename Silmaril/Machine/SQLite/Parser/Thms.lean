module

public import Silmaril.Machine.SQLite.Parser.Defs
public import Silmaril.Machine.SQLite.Tokenizer.Thms
import Silmaril.Proofs.Machine.SQLite.Parser.Correctness

public section

namespace Silmaril.Machine.SQLite.Parser

theorem parse_iff (tokens : State) (stmt : Statement) :
    parse tokens = some stmt ↔ Grammar tokens stmt :=
  ⟨Proofs.Machine.SQLite.Parser.parse_sound, Proofs.Machine.SQLite.Parser.parse_complete⟩

theorem parse_printTokens {stmt : Statement} (h : stmt.WellFormed) :
    parse (printTokens stmt) = some stmt :=
  (parse_iff _ _).2 ⟨h, Or.inl rfl⟩

theorem represents_print {stmt : Statement} (h : stmt.WellFormed) :
    Represents (print stmt) stmt :=
  Proofs.Machine.SQLite.Parser.represents_print h

end Silmaril.Machine.SQLite.Parser

module

public import Silmaril.Machine.SQLite.CommandProcessor.Defs
public import Silmaril.Machine.SQLite.CodeGenerator.Thms
public import Silmaril.Machine.SQLite.Parser.Thms
import Silmaril.Proofs.Machine.SQLite.CommandProcessor.Prepare

public section

namespace Silmaril.Machine.SQLite.CommandProcessor

open Silmaril.SQLite.Relational (TableSemantics SqlValue Affinity)

theorem parse_iff (text : String) (stmt : Parser.Statement) :
    parse text = .ok stmt ↔ Parser.Represents text stmt :=
  Proofs.Machine.SQLite.CommandProcessor.parse_iff text stmt

theorem parse_print {stmt : Parser.Statement} (h : stmt.WellFormed) :
    parse (Parser.print stmt) = .ok stmt :=
  (parse_iff _ _).2 (Parser.represents_print h)

theorem prepare_iff {Expr : Type} {sem : TableSemantics SqlValue Affinity Expr}
    (db : State sem) (text : String) (prepared : CodeGenerator.Prepared sem) :
    prepare db text = .ok prepared ↔ Prepares db text prepared :=
  Proofs.Machine.SQLite.CommandProcessor.prepare_iff db text prepared

end Silmaril.Machine.SQLite.CommandProcessor

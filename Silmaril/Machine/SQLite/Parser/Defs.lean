module

public import Silmaril.Machine.SQLite.Tokenizer.Defs

@[expose] public section

namespace Silmaril.Machine.SQLite.Parser

open Tokenizer (Token CanonicalWord)

/-- The grammar has one predicate and one bind slot. Only its two names vary. -/
structure Statement where
  table : String
  column : String
  deriving DecidableEq, Repr

/-- Names in this grammar use the D3 catalog's normalized spelling. Only the
three structural keywords are reserved by this grammar. -/
def IsName (word : String) : Prop :=
  CanonicalWord word ∧ word ≠ "select" ∧ word ≠ "from" ∧ word ≠ "where"

instance (word : String) : Decidable (IsName word) := inferInstanceAs (Decidable (_ ∧ _))

def Statement.WellFormed (stmt : Statement) : Prop :=
  IsName stmt.table ∧ IsName stmt.column

instance (stmt : Statement) : Decidable stmt.WellFormed := inferInstanceAs (Decidable (_ ∧ _))

/-- Concrete parser state. The entire token stream must be consumed by one statement. -/
abbrev State := List Token

def printTokens (stmt : Statement) : State :=
  [.word "select", .word stmt.column, .word "from", .word stmt.table,
    .word "where", .word "rowid", .equals, .parameterOne]

def print (stmt : Statement) : String :=
  String.ofList (Tokenizer.render (printTokens stmt))

/-- The abstract grammar admits the printed statement and its semicolon-terminated form. -/
def Grammar (tokens : State) (stmt : Statement) : Prop :=
  stmt.WellFormed ∧ (tokens = printTokens stmt ∨ tokens = printTokens stmt ++ [.semicolon])

/-- Recognize the shape, then check the words and optional single terminator. -/
def parse : State → Option Statement
  | .word select :: .word column :: .word fromWord :: .word table :: .word whereWord ::
      .word rowid :: .equals :: .parameterOne :: tail =>
    let stmt : Statement := ⟨table, column⟩
    if select = "select" ∧ fromWord = "from" ∧ whereWord = "where" ∧ rowid = "rowid" ∧
        stmt.WellFormed ∧ (tail = [] ∨ tail = [.semicolon]) then
      some stmt
    else none
  | _ => none

/-- Text represents a statement when its lexical stream belongs to the grammar. -/
def Represents (text : String) (stmt : Statement) : Prop :=
  ∃ tokens, Tokenizer.Lexes text.toList tokens ∧ Grammar tokens stmt

end Silmaril.Machine.SQLite.Parser

module

public import Silmaril.Machine.SQLite.Parser.Defs
public import Silmaril.Machine.SQLite.CodeGenerator.Defs

@[expose] public section

namespace Silmaril.Machine.SQLite.CommandProcessor

open Silmaril.SQLite.Relational
open CatalogExecutor (Names)

variable {Expr : Type} {sem : TableSemantics SqlValue Affinity Expr}

abbrev State (sem : TableSemantics SqlValue Affinity Expr) := CodeGenerator.State sem

inductive TextError where
  | lexical (error : Tokenizer.Error)
  | outsideGrammar
  deriving DecidableEq, Repr

inductive PrepareError where
  | text (error : TextError)
  | planner (error : CodeGenerator.PrepareError)
  deriving DecidableEq, Repr

/-- No statement tail is returned. Successful recognition consumes all the input. -/
def parse (text : String) : Except TextError Parser.Statement := do
  let tokens ← (Tokenizer.tokenize text).mapError .lexical
  match Parser.parse tokens with
  | some stmt => .ok stmt
  | none => .error .outsideGrammar

/-- Map the two names into D3's existing typed point-read invocation. -/
def invocation (stmt : Parser.Statement) (binding : Option (Int32 × Int64) := none) :
    Invocation Names :=
  ⟨⟨⟨stmt.table, stmt.column⟩⟩, binding⟩

/-- The catalog decides scope before name resolution. -/
def request (db : State sem) (stmt : Parser.Statement) (binding : Option (Int32 × Int64) := none) :
    CheckedRequest Names :=
  CatalogExecutor.classify db.catalog (invocation stmt binding)

/-- Prepare from text against a pure catalog snapshot. The returned D3 plan
carries the resolved column label and target and can be bound with `Prepared.bindInt64`. -/
def prepare (db : State sem) (text : String) :
    Except PrepareError (CodeGenerator.Prepared sem) := do
  let stmt ← (parse text).mapError .text
  (CodeGenerator.prepare db (request db stmt)).mapError .planner

/-- Text preparation relates the lexical and grammar judgment to the D3-backed
planning judgment. Fragment rejection occurs before a plan can be produced. -/
def Prepares (db : State sem) (text : String) (prepared : CodeGenerator.Prepared sem) : Prop :=
  ∃ stmt, Parser.Represents text stmt ∧ CodeGenerator.Prepares db (request db stmt) (.ok prepared)

end Silmaril.Machine.SQLite.CommandProcessor

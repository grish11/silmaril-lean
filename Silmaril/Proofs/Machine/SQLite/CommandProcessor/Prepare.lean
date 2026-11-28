module

public import Silmaril.Machine.SQLite.CommandProcessor.Defs
import Silmaril.Machine.SQLite.CodeGenerator.Thms
import Silmaril.Machine.SQLite.Parser.Thms

public section

namespace Silmaril.Proofs.Machine.SQLite.CommandProcessor

open Silmaril.Machine.SQLite.CommandProcessor
open Silmaril.Machine.SQLite
open Silmaril.SQLite.Relational (TableSemantics SqlValue Affinity)

theorem parse_iff (text : String) (stmt : Parser.Statement) :
    parse text = .ok stmt ↔ Parser.Represents text stmt := by
  constructor
  · intro h
    cases ht : Tokenizer.tokenize text with
    | error error => simp [parse, ht, Except.mapError, bind, Except.bind] at h
    | ok tokens =>
      have lexical := (Tokenizer.tokenize_iff _ _).1 ht
      cases hp : Parser.parse tokens with
      | none => simp [parse, ht, hp, Except.mapError, bind, Except.bind] at h
      | some parsed =>
        have eq : parsed = stmt := by
          simpa [parse, ht, hp, Except.mapError, bind, Except.bind] using h
        exact ⟨tokens, lexical, (Parser.parse_iff _ _).1 (eq ▸ hp)⟩
  · rintro ⟨tokens, lexical, grammar⟩
    have ht := (Tokenizer.tokenize_iff _ _).2 lexical
    have hp := (Parser.parse_iff _ _).2 grammar
    simp [parse, ht, hp, Except.mapError, bind, Except.bind]

variable {Expr : Type} {sem : TableSemantics SqlValue Affinity Expr}

theorem prepare_iff (db : State sem) (text : String) (prepared : CodeGenerator.Prepared sem) :
    prepare db text = .ok prepared ↔ Prepares db text prepared := by
  constructor
  · intro h
    cases hp : parse text with
    | error error => simp [prepare, hp, Except.mapError, bind, Except.bind] at h
    | ok stmt =>
      have planned : CodeGenerator.prepare db (request db stmt) = .ok prepared := by
        cases hc : CodeGenerator.prepare db (request db stmt) <;>
          simp_all [prepare, Except.mapError, bind, Except.bind]
      exact ⟨stmt, (parse_iff _ _).1 hp, (CodeGenerator.prepare_iff _ _ _).1 planned⟩
  · rintro ⟨stmt, parsed, planned⟩
    have hp := (parse_iff _ _).2 parsed
    have hc := (CodeGenerator.prepare_iff _ _ _).2 planned
    simp [prepare, hp, hc, Except.mapError, bind, Except.bind]

end Silmaril.Proofs.Machine.SQLite.CommandProcessor

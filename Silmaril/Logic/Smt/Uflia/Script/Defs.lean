module

public import Silmaril.Logic.Smt.Uflia.Packaged.Thms

/-!
# A strict single-query typed UF/LIA script frontend

This frontend reads ASCII SMT S-expressions, an optional initial
`(set-logic QF_UFLIA)` or `(set-logic QF_LIA)`, a declaration prefix, zero or more assertions and one
terminal `(check-sat)`, optionally followed by `(exit)`. Other logic names and
commands reject. Terms use the existing restricted sorted UF/LIA decoder.
The output retains actual executable declaration and assertion decoder evidence.
Arbitrary-term integer scaling is the existing mathematical linear extension,
not a validated exact QF_LIA surface-grammar restriction. This supported dialect
does not claim the full SMT-LIB standard.
-/

@[expose] public section

namespace Silmaril.Logic.Smt.Uflia.Script

open CategoryTheory Silmaril.Inst
open Silmaril.Logic.Institution (Room)
open SExpr

/-- A declaration keyword belongs to the initial prefix even if its arguments
are malformed; the declaration decoder then rejects the malformed command. -/
def isDeclaration : Expr → Bool
  | .list (.atom "declare-sort" :: _) => true
  | .list (.atom "declare-const" :: _) => true
  | .list (.atom "declare-fun" :: _) => true
  | _ => false

/-- Extract assertion expressions only when the single terminal query is
present. Recursion stops at the query; no later assertion or second query passes. -/
def assertionCommands? : List Expr → Option (List Expr)
  | [.list [.atom "check-sat"]] => some []
  | [.list [.atom "check-sat"], .list [.atom "exit"]] => some []
  | .list [.atom "assert", e] :: rest =>
      (assertionCommands? rest).map (e :: ·)
  | _ => none

structure Layout where
  declarations : List Expr
  assertions : List Expr

/-- Parse command order independently of typed term decoding. -/
def commandBody? (forms : List Expr) : Option Layout := do
  let assertions ← assertionCommands? (forms.dropWhile isDeclaration)
  pure ⟨forms.takeWhile isDeclaration, assertions⟩

/-- The LIA-tagged dialect permits only built-in nullary declarations. -/
def liaDeclaration : Expr → Bool
  | .list [.atom "declare-const", .atom _, .atom "Bool"] => true
  | .list [.atom "declare-const", .atom _, .atom "Int"] => true
  | .list [.atom "declare-fun", .atom _, .list [], .atom "Bool"] => true
  | .list [.atom "declare-fun", .atom _, .list [], .atom "Int"] => true
  | _ => false

/-- Both tags select the existing typed term decoder. QF_LIA restricts declarations
but is not a claim of exact membership in the official coefficient syntax. -/
def layout? : List Expr → Option Layout
  | .list [.atom "set-logic", .atom "QF_UFLIA"] :: rest => commandBody? rest
  | .list [.atom "set-logic", .atom "QF_LIA"] :: rest => do
      let body ← commandBody? rest
      if body.declarations.all liaDeclaration then some body else none
  | forms => commandBody? forms

/-- Successful executable declaration decoding supplies its own equality. -/
def checkedPrefix? (forms : List Expr) : Option DeclarationPrefix :=
  match h : declarations? forms with
  | none => none
  | some E => some ⟨forms, E, h⟩

/-- Successful executable formula decoding supplies its own equality. -/
def checkedAssertion? (E : Environment) (e : Expr) : Option (Assertion E) :=
  match h : decodeFormula? E e with
  | none => none
  | some φ => some ⟨e, φ, h⟩

def decodeLayout? (layout : Layout) : Option Packaged.ConcreteSentence := do
  let checked ← checkedPrefix? layout.declarations
  let assertions ← layout.assertions.mapM (checkedAssertion? checked.environment)
  pure ⟨checked, assertions⟩

/-- Declarations must precede all assertions. Symbols, profiles and formula
sorts are checked by the actual typed decoder, not by a supplied certificate. -/
def decodeForms? (forms : List Expr) : Option Packaged.ConcreteSentence :=
  layout? forms >>= decodeLayout?

/-- Exact input bytes enter the existing ASCII S-expression reader. None means
unsupported or malformed syntax, command order, declarations or assertion terms. -/
def parse? (text : String) : Option Packaged.ConcreteSentence :=
  readForms text.toUTF8.data.toList >>= decodeForms?

/-- Only successfully parsed source texts are sentences of the script room.
Rejected input is a parser error, rather than an unsatisfiable script sentence. -/
structure Accepted where
  text : String
  sentence : Packaged.ConcreteSentence
  parsed : parse? text = some sentence

/-- The parser itself can construct an accepted sentence, including its proof. -/
def accept? (text : String) : Option Accepted :=
  match h : parse? text with
  | none => none
  | some s => some ⟨text, s, h⟩

noncomputable def TextHolds (text : String) (M : Packaged.GlobalModel) : Prop :=
  ∃ s, parse? text = some s ∧ s.Holds M

noncomputable def Accepted.Holds (s : Accepted) (M : Packaged.GlobalModel) : Prop :=
  TextHolds s.text M

noncomputable def Accepted.Sat (s : Accepted) : Prop := ∃ M, s.Holds M

noncomputable def Accepted.Unsat (s : Accepted) : Prop := ¬ s.Sat

/-- The source presentation has one signature, with declarations in each script.
Its models are the same coherent typed-name models as packaged concrete problems. -/
noncomputable def plain : Plain (Disc Unit) where
  Sen _ := Accepted
  map _ := id
  map_id _ _ := rfl
  map_comp _ _ _ := rfl
  Mod _ := Packaged.GlobalModel
  reduct _ := id
  reduct_id _ _ := rfl
  reduct_comp _ _ _ := rfl
  Sat M s := s.Holds M
  sat_map _ _ _ := Iff.rfl

noncomputable abbrev institution := plain.toInst
noncomputable abbrev room := plain.room ()

end Silmaril.Logic.Smt.Uflia.Script

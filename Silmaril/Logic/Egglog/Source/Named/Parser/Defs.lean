module

public import Silmaril.Logic.Egglog.Source.Named.Resolution.Thms
public import Silmaril.Logic.Smt.SExpr.Writer.Thms

@[expose] public section
namespace Silmaril.Logic.Egglog.Source.Named.Parser
open Silmaril.Logic.Smt

/-- Authored normalized grammar: variables and total applications have distinct
tags. The budget is supplied from the complete input tree size, not a constant. -/
def term : Nat → SE → Option RawTerm
  | 0, _ => none
  | _ + 1, .list [.atom "var", .atom name] => some (.var name)
  | fuel + 1, .list (.atom "app" :: .atom name :: arguments) =>
      (arguments.mapM (term fuel)).map (RawTerm.ofArgs name)
  | _, _ => none

mutual
/-- Executable structural node count; avoids relying on generated SizeOf code
for the nested shared reader AST. -/
def nodes : SE → Nat
  | .atom _ => 1
  | .list expressions => nodesList expressions + 1

def nodesList : List SE → Nat
  | [] => 0
  | expression :: rest => nodes expression + nodesList rest
end

def term? (expression : SE) : Option RawTerm := term (nodes expression + 1) expression

def atom : SE → Option RawAtom
  | .list [.atom "equal", left, right] => do
      pure (.equal (← term? left) (← term? right))
  | .list [.atom "relation", .atom name, .list arguments] => do
      let arguments ← arguments.mapM term?
      pure (.relation name arguments.length arguments.get)
  | .list [.atom "row", .atom name, .list arguments, value] => do
      let arguments ← arguments.mapM term?
      pure (.row name arguments.length arguments.get (← term? value))
  | _ => none

def binding : SE → Option Binding
  | .list [.atom name, .atom sort] => some ⟨name, sort⟩
  | _ => none

def sentence : SE → Option RawSentence
  | .list [.atom "rule", .list context, .list body, head] => do
      pure (.rule (← context.mapM binding) (← body.mapM atom) (← atom head))
  | .list [.atom "query", .list context, .list goals] => do
      pure (.query (← context.mapM binding) (← goals.mapM atom))
  | _ => none

def sortName : SE → Option String
  | .atom name => some name
  | _ => none

def declaration : SE → Option RawDeclaration
  | .list [.atom "sort", .atom name] => some (.sort name)
  | .list [.atom "constructor", .atom name, .list inputs, .atom output] => do
      pure (.constructor ⟨name, ← inputs.mapM sortName, output⟩)
  | .list [.atom "relation", .atom name, .list inputs] => do
      pure (.relation ⟨name, ← inputs.mapM sortName⟩)
  | .list [.atom "function", .atom name, .list inputs, .atom output] => do
      pure (.function ⟨name, ← inputs.mapM sortName, output⟩)
  | _ => none

/-- Declarations form a prefix. Once a sentence is seen, every remaining form
must be a sentence; unsupported or trailing declarations reject the whole file. -/
def program : List SE → Option RawProgram
  | [] => some ⟨[], []⟩
  | expression :: rest =>
      match declaration expression with
      | some d => do
          let tail ← program rest
          pure ⟨d :: tail.declarations, tail.sentences⟩
      | none => do
          let sentences ← (expression :: rest).mapM sentence
          pure ⟨[], sentences⟩

def readProgram (bytes : List UInt8) : Option RawProgram := do
  let forms ← readForms bytes
  program forms

/-- A supplied-view body contains precisely one whole sentence form. -/
def readSentence (bytes : List UInt8) : Option RawSentence := do
  let forms ← readForms bytes
  match forms with
  | [form] => sentence form
  | _ => none

/-- Complete checking retains every sentence of a declaration-carrying file. -/
def compileProgram (bytes : List UInt8) :
    Option (Σ D : Declarations, List (Core.Sentence D.signature)) := do
  let raw ← readProgram bytes
  resolveProgram? raw

def encodeTerm : RawTerm → SE
  | .var name => .list [.atom "var", .atom name]
  | .app name n arguments =>
      .list (.atom "app" :: .atom name :: List.ofFn (fun i : Fin n => encodeTerm (arguments i)))

def encodeAtom : RawAtom → SE
  | .equal left right => .list [.atom "equal", encodeTerm left, encodeTerm right]
  | .relation name n arguments => .list [.atom "relation", .atom name,
      .list (List.ofFn (fun i : Fin n => encodeTerm (arguments i)))]
  | .row name n arguments value => .list [.atom "row", .atom name,
      .list (List.ofFn (fun i : Fin n => encodeTerm (arguments i))), encodeTerm value]

def encodeBinding (binding : Binding) : SE :=
  .list [.atom binding.name, .atom binding.sort]

def encodeSentence : RawSentence → SE
  | .rule context body head => .list [.atom "rule", .list (context.map encodeBinding),
      .list (body.map encodeAtom), encodeAtom head]
  | .query context goals => .list [.atom "query", .list (context.map encodeBinding),
      .list (goals.map encodeAtom)]

def encodeDeclaration : RawDeclaration → SE
  | .sort name => .list [.atom "sort", .atom name]
  | .constructor d => .list [.atom "constructor", .atom d.name,
      .list (d.inputs.map SE.atom), .atom d.output]
  | .relation d => .list [.atom "relation", .atom d.name, .list (d.inputs.map SE.atom)]
  | .function d => .list [.atom "function", .atom d.name,
      .list (d.inputs.map SE.atom), .atom d.output]

def encodeProgram (program : RawProgram) : List SE :=
  program.declarations.map encodeDeclaration ++ program.sentences.map encodeSentence

/-- The shared writer, rather than a second low-level byte printer. Actual
read/render receipts require its LegalExpr premise and structural roundtrip. -/
def writeProgram (program : RawProgram) : List UInt8 :=
  SExpr.Writer.renderForms (encodeProgram program)

def writeSentence (sentence : RawSentence) : List UInt8 :=
  SExpr.Writer.render (encodeSentence sentence)

namespace Task
/-- Size-derived budget and all-constructor structural parser roundtrip;
`termRoundtrip_task` proves this proposition in the theorem header. -/
def termRoundtrip : Prop := ∀ term : RawTerm, term? (encodeTerm term) = some term

def sentenceRoundtrip : Prop :=
  ∀ s : RawSentence, sentence (encodeSentence s) = some s

def programRoundtrip : Prop :=
  ∀ p : RawProgram, program (encodeProgram p) = some p
end Task

end Silmaril.Logic.Egglog.Source.Named.Parser

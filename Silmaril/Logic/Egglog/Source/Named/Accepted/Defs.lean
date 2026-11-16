module

public import Silmaril.Logic.Egglog.Source.Named.Parser.Defs

@[expose] public section
namespace Silmaril.Logic.Egglog.Source.Named

/-- Supplied-declaration mode retains complete original body bytes and both
actual executable boundaries. Truth is independent named denotation. -/
structure AcceptedSentence (D : Declarations) where
  bytes : List UInt8
  raw : RawSentence
  read_eq : Parser.readSentence bytes = some raw
  resolved : Core.Sentence D.signature
  resolve_eq : resolveSentence? D raw = some resolved

def AcceptedSentence.Holds {D : Declarations} (sentence : AcceptedSentence D)
    (M : Core.Model D.signature) : Prop := sentence.raw.Holds M

def acceptSentence? (D : Declarations) (bytes : List UInt8) : Option (AcceptedSentence D) :=
  match hr : Parser.readSentence bytes with
  | none => none
  | some raw =>
      match hc : resolveSentence? D raw with
      | none => none
      | some resolved => some ⟨bytes, raw, hr, resolved, hc⟩

/-- Declaration-carrying single-sentence mode retains the actual complete header
and file, rather than claiming its bytes are rewritten by an ambient map. -/
structure AcceptedUnit where
  bytes : List UInt8
  header : List RawDeclaration
  declarations : Declarations
  header_eq : checkDeclarations header = some declarations
  raw : RawSentence
  read_eq : Parser.readProgram bytes = some ⟨header, [raw]⟩
  resolved : Core.Sentence declarations.signature
  resolve_eq : resolveSentence? declarations raw = some resolved

/-- Execute the complete declaration-carrying single-sentence admission path. -/
def acceptUnit? (bytes : List UInt8) : Option AcceptedUnit :=
  match hr : Parser.readProgram bytes with
  | some ⟨header, [raw]⟩ =>
      match hd : checkDeclarations header with
      | none => none
      | some D =>
          match hc : resolveSentence? D raw with
          | none => none
          | some resolved => some ⟨bytes, header, D, hd, raw, hr, resolved, hc⟩
  | _ => none

/-- Whole-program receipts retain all ordered rules and queries. -/
structure AcceptedProgram where
  bytes : List UInt8
  raw : RawProgram
  read_eq : Parser.readProgram bytes = some raw
  declarations : Declarations
  header_eq : checkDeclarations raw.declarations = some declarations
  resolved : List (Core.Sentence declarations.signature)
  resolve_eq : raw.sentences.mapM (resolveSentence? declarations) = some resolved

def AcceptedProgram.Holds (program : AcceptedProgram)
    (M : Core.Model program.declarations.signature) : Prop :=
  ProgramHolds M program.raw.sentences

def acceptProgram? (bytes : List UInt8) : Option AcceptedProgram :=
  match hr : Parser.readProgram bytes with
  | none => none
  | some raw =>
      match hd : checkDeclarations raw.declarations with
      | none => none
      | some D =>
          match hc : raw.sentences.mapM (resolveSentence? D) with
          | none => none
          | some sentences => some ⟨bytes, raw, hr, D, hd, sentences, hc⟩

/-- A selected entry carries its original whole-program receipt and position. -/
structure ProgramEntry where
  program : AcceptedProgram
  index : Fin program.raw.sentences.length

def ProgramEntry.raw (entry : ProgramEntry) : RawSentence :=
  entry.program.raw.sentences.get entry.index

end Silmaril.Logic.Egglog.Source.Named

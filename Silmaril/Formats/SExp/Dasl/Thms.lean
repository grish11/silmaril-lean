module
public import Silmaril.Formats.SExp.Dasl.Defs
public import Silmaril.Formats.Dasl.Presentation.Thms
import Silmaril.Proofs.Formats.SExp.Dasl.Basic

@[expose] public section
namespace Silmaril.Formats.SExpDasl
open Dasl Dasl.Encode

theorem roundtrip {Atom : Type} (atom : TotalCodec Atom Value) (expr : SExp Atom) :
    decode? atom (encode atom expr) = some expr := Proofs.Formats.SExp.Dasl.roundtrip atom expr

def codec {Atom : Type} (atom : TotalCodec Atom Value) : TotalCodec (SExp Atom) Value :=
  ⟨encode atom, decode? atom, roundtrip atom⟩

abbrev symbols := codec text
abbrev rivest := codec rawBytes

def parseRivestAbstract? : Bytes → Option rivest.Abstract := rivest.parseAbstract? RivestSExp.parseCanonical?
def parseSymbolsAbstract? : String → Option symbols.Abstract := symbols.parseAbstract? SExpParser.parseSExp?

theorem rivest_per : syntaxPER parseRivestAbstract? = syntaxPER RivestSExp.parseCanonical? :=
  rivest.parseAbstract_per RivestSExp.parseCanonical?

theorem symbols_per : syntaxPER parseSymbolsAbstract? = syntaxPER SExpParser.parseSExp? :=
  symbols.parseAbstract_per SExpParser.parseSExp?

end Silmaril.Formats.SExpDasl

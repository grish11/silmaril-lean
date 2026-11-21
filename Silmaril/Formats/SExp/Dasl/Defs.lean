module
public import Silmaril.Formats.Dasl.Presentation.Defs
public import Silmaril.Formats.SExp.Parser
public import Silmaril.Formats.SExp.Rivest

@[expose] public section
namespace Silmaril.Formats.SExpDasl
open Dasl Dasl.Encode

def astPER (Atom : Type) : PER (SExp Atom) := PER.equality _

def syntaxPER {Wire Ast : Type} (parse : Wire → Option Ast) : PER Wire := PER.ofDecoder parse

/-- A one-key dict tags atoms; native, indexed DASL lists preserve child order. -/
def encode {Atom : Type} (atom : TotalCodec Atom Value) : SExp Atom → Value
  | .atom value => .dict {"sexp:atom"} (fun _ => atom.encode value)
  | .list len children => .list len fun pos => encode atom (children pos)

def decode? {Atom : Type} (atom : TotalCodec Atom Value) (tree : Value) : Option (SExp Atom) :=
  match tree with
  | .dict keys children =>
    if tag : keys = {"sexp:atom"} then
      (atom.decode? (children ⟨"sexp:atom", tag.symm ▸ Finset.mem_singleton_self _⟩)).map .atom
    else none
  | .list _ items => (List.ofFn (fun pos => decode? atom (items pos))).mapM id |>.map SExp.ofList
  | _ => none
termination_by structural tree

def rawBytes : TotalCodec Bytes Value :=
  ⟨fun input => .bytes input.data, (fun | .bytes payload => some ⟨payload⟩ | _ => none), fun ⟨_⟩ => rfl⟩

end Silmaril.Formats.SExpDasl

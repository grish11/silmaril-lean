module
public import Silmaril.Formats.Dasl.Encode.Thms
public import Silmaril.Formats.PER.Thms

@[expose] public section
namespace Silmaril.Formats.Dasl.Encode.TotalCodec
variable {Ast Wire : Type}

/-- The exact encoder image, not the possibly larger domain of its decoder. -/
def Abstract (codec : TotalCodec Ast Value) := { value : Value // ∃ ast, codec.encode ast = value }

def intoAbstract (codec : TotalCodec Ast Value) (ast : Ast) : codec.Abstract :=
  ⟨codec.encode ast, ⟨ast, rfl⟩⟩

def fromAbstract? (codec : TotalCodec Ast Value) (value : codec.Abstract) : Option Ast :=
  codec.decode? value.val

def parseAbstract? (codec : TotalCodec Ast Value) (parse : Wire → Option Ast) (input : Wire) :
    Option codec.Abstract := (parse input).map codec.intoAbstract

end Silmaril.Formats.Dasl.Encode.TotalCodec

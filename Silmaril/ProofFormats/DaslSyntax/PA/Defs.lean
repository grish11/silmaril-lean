module

public import Silmaril.ProofFormats.DaslSyntax.Defs
public import Silmaril.Logic.Arithmetic.Peano
public import Silmaril.Logic.Arithmetic.SExp.Thms

@[expose] public section

namespace Silmaril.ProofFormats.DaslSyntax.PA

open Silmaril.Formats.Dasl
open Silmaril.Logic.Arithmetic

def slots : InlinePrefix := fun _ tag => if tag = "var" then 2 else 1

def term (depth : Nat) : Syntax (Term depth) :=
  ⟨⟨SExp.encodeTerm, SExp.readTerm? depth, SExp.readTerm?_encodeTerm⟩, slots⟩

def formula (depth : Nat) : Syntax (Formula depth) := ⟨ofSExpCodec (SExp.codec depth), slots⟩

variable {Name : Type} (store : Store Name)

def sentences : Set Name := (formula 0).namesWhere store (fun _ => True)

def theorems : Set Name := (formula 0).namesWhere store (fun sentence => Nonempty (PAProof [] sentence))

/-- Truth under the standard natural-number interpretation, not a PA completeness assertion. -/
def standardTruth : Set Name := (formula 0).namesWhere store Valid

end Silmaril.ProofFormats.DaslSyntax.PA

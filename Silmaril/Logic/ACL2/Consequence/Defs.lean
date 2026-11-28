module

public import Silmaril.Logic.ACL2.Books.Examples
public import Silmaril.Logic.Consequence.Institution.Defs

@[expose] public section

namespace Silmaril.Logic.ACL2.Consequence

open Silmaril.Consequence Silmaril.Logic.Institution

/-- The room of a definition-bearing signature, suitable for a graph room declaration. -/
def presentationRoom (P : Presentation) : Room.{0, 0, 1} := presentedInst.I.obj P

/-- The syntactic π-consequence relation at a definition-bearing signature, with list premises. -/
def presentationDerives (P : Presentation) : System (List (Sentence P.signature)) (Sentence P.signature) :=
  ER.listSys (pi.I.obj P)

/-- Semantic consequence over models satisfying the signature's definitions. -/
def presentationEntails (P : Presentation) : System (List (Sentence P.signature)) (Sentence P.signature) :=
  roomSeq (presentationRoom P)

/-- Derivability at the example book's output signature. -/
def exampleDerives := presentationDerives Examples.exampleWorld.presentation

/-- Semantic consequence at the example book's output signature. -/
def exampleEntails := presentationEntails Examples.exampleWorld.presentation

end Silmaril.Logic.ACL2.Consequence

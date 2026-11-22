module

public import Silmaril.ProofFormats.DaslSExp.Defs
public import Silmaril.Formats.Dasl.SExp.Thms
import Silmaril.Proofs.ProofFormats.DaslSExp

@[expose] public section

namespace Silmaril.ProofFormats.DaslSExp

open Silmaril.Formats (SExp)
open Silmaril.Formats.Dasl
open Silmaril.Formats.Dasl.SExp
open Silmaril.Logic.Concrete (SExpCodec)
open Silmaril.Logic.Smt (SE)

theorem toLogic_ofLogic (form : SE) : toLogic (ofLogic form) = form :=
  Proofs.ProofFormats.DaslSExp.to_of form

/-- Reuse a logic's existing decoder and grammar law; no tags or constructors of
the logic are reimplemented here. -/
def syntaxCodec {Item : Type} (grammar : SExpCodec Item) : Encode.TotalCodec Item (SExp String) where
  encode item := ofLogic (grammar.encode item)
  decode? tree := grammar.decode (toLogic tree)
  recovers item := by
    rw [toLogic_ofLogic]
    exact (grammar.decode_eq_some_iff _ item).2 rfl

def codec {Item Ref Name : Type} (grammar : SExpCodec Item) (put : Placement (SExp String) Name) :
    Encode.TotalCodec Item (Tree Ref Name) := (syntaxCodec grammar).then (Proper.codec Payload.utf8 put)

end Silmaril.ProofFormats.DaslSExp

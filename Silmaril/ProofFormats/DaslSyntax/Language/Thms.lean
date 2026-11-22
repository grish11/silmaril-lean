module

public import Silmaril.Formats.Dasl.Language.Defs
public import Silmaril.ProofFormats.DaslSyntax.Thms

public section

namespace Silmaril.ProofFormats.DaslSyntax

open Silmaril.Formats.Dasl

/-- Unary syntax lifting is recognition of the corresponding expanded DASL language. -/
theorem Syntax.namesWhere_eq_recognized {Item Name : Type} (grammar : Syntax Item) (store : Store Name)
    (predicate : Item → Prop) :
    grammar.namesWhere store predicate = Recognized store (fun value => value ∈ grammar.language predicate) :=
  Set.ext fun _ => Syntax.mem_namesWhere_language

end Silmaril.ProofFormats.DaslSyntax

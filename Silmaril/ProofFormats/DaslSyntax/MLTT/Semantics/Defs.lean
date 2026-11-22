module

public import Silmaril.ProofFormats.DaslSyntax.MLTT.Defs
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.SetSemantics

@[expose] public section

namespace Silmaril.ProofFormats.DaslSyntax.MLTT

open Silmaril.Formats.Dasl
open Silmaril.Logic.TypeTheory.ExtensionalMLTT

universe u

/-- Nonemptiness in every environment of a well-formed context, in one supplied hierarchy.
The semantic witnesses are sets; they are not required to be denotations of a common term. -/
def inhabitsIn (model : SetHierarchy.{u}) (context : ECtx) (type : ETm 0) : Prop :=
  wellFormed context ∧ ∀ env, context.Sat model env → ∃ member, member ∈ type.denote model env Fin.elim0

def semanticInhabitance {Name : Type} (store : Store Name) (model : SetHierarchy.{u}) :
    Consequence.System Name Name := system (ctx.named store) (ty.named store) (inhabitsIn model)

def nonemptyTypes {Name : Type} (store : Store Name) (model : SetHierarchy.{u}) (context : ECtx) : Set Name :=
  ty.namesWhere store (inhabitsIn model context)

end Silmaril.ProofFormats.DaslSyntax.MLTT

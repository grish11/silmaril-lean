module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.Defs

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Program

open CategoryTheory
open Silmaril.Elgot.ITree (Tree TraceSignature HasTrace)
open Silmaril.Logic.ITree
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction (region)
open Silmaril.Isotope.Bridge.NamedFlat.Capture (packEnv)

variable {F : Type} {signature : PrimitiveSignature F} {a b : Nat}
  {inputs : Fin a → PacketType} {outputs : Fin b → PacketType}
  {left right : Program signature inputs outputs} {input : Fin a} {Target : TraceSignature.{0}}

/-- Run the checked packed dispatcher with primitives translated to the
target event signature. Inputs, compiled code, and ordered exits are shared. -/
noncomputable def PackedEntry.observeMapped {target : Silmaril.Elgot.ITree.Signature.{0}} (entry : PackedEntry left input)
    (f : signature.traceSignature.toSignature ⟶ target) (ambient record : Semantics.Env Atom) :
    Tree target.Event (Nat × Silmaril.Isotope.Value Atom) :=
  letI := signature.typing
  region (fun op value => f.tree id (signature.primitive op value))
    (Semantics.extend ambient (packEnv entry.count record))
    ((FiniteCFG.packedExecutionRegion entry.typed).packInputsDestructure entry.context.toList)

/-- Run the same dispatcher along an arrow of the trace institution. -/
noncomputable def PackedEntry.observeReindexed (entry : PackedEntry left input)
    (f : signature.traceSignature ⟶ Target) (ambient record : Semantics.Env Atom) :
    Tree Target.toSignature.Event (Nat × Silmaril.Isotope.Value Atom) :=
  entry.observeMapped f.hom ambient record

/-- The existing trace sentence comparing two reindexed packed executions. -/
noncomputable def PackedEntry.refinementSentenceReindexed
    (leftEntry : PackedEntry left input) (rightEntry : PackedEntry right input)
    (f : signature.traceSignature ⟶ Target) (direction : MismatchDirection)
    (leftAmbient rightAmbient leftRecord rightRecord : Semantics.Env Atom) :
    TraceInstitution.Sentence.{0, 1} Target :=
  let l := leftEntry.observeReindexed f leftAmbient leftRecord
  let r := rightEntry.observeReindexed f rightAmbient rightRecord
  match direction with
  | .leftToRight => ⟨_, l, HasTrace r⟩
  | .rightToLeft => ⟨_, r, HasTrace l⟩

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Program

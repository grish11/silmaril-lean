module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Capture.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.FlatDispatcher.Execution.Defs

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Program

open Silmaril.Elgot.ITree (Tree)
open Silmaril.Elgot.ITree.Finite (Event)
open Silmaril.Isotope (BoundCtx)
open Silmaril.Isotope.Bridge.NamedFlat (elaborate)
open Silmaril.Isotope.Bridge.NamedFlat.Capture (packEnv)
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction (region)

variable {F : Type} {signature : PrimitiveSignature F} {a b : Nat}
  {inputs : Fin a → PacketType} {outputs : Fin b → PacketType}

/-- The checked packed dispatcher for a single public entry. The capture
layout and typing may vary across entries and between programs. -/
structure PackedEntry (program : Program signature inputs outputs) (input : Fin a) where
  count : Nat
  captures : Fin count → Register
  context : BoundCtx PacketType count
  blocks : Fin (program.compile input).blocks.length → PacketType
  exits : Fin program.exits.length → PacketType
  target : FiniteCFG F (program.compile input).blocks.length program.exits.length count
  accepted : elaborate (program.compile input) program.exits captures = some target
  typed : letI := signature.typing; target.HasType context blocks exits

variable {program : Program signature inputs outputs} {input : Fin a}

/-- Captured values come from the named entry store for this packet.
Varying data must be represented in the entry packet. -/
def PackedEntry.recordAgrees (entry : PackedEntry program input) (packet : Denote (inputs input))
    (original : Semantics.Env Atom) : Prop :=
  ∀ i, original i.val = Program.store (inputs := inputs) input packet (entry.captures i)

noncomputable def PackedEntry.observe (entry : PackedEntry program input) (ambient original : Semantics.Env Atom) :
    Tree (Event signature.Request signature.Reply) (Nat × Silmaril.Isotope.Value Atom) :=
  letI := signature.typing
  region signature.primitive (Semantics.extend ambient (packEnv entry.count original))
    ((FiniteCFG.packedExecutionRegion entry.typed).packInputsDestructure entry.context.toList)

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Program

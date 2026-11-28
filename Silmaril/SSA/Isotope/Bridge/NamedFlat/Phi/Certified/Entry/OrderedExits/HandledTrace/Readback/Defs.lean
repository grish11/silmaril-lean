module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Defs

/-! # Local alignment of the actual flat dispatchers -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback

open LambdaSSA (Flat FiniteCFG)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (BlockInput Primitive Transfer region splitTransfer)
open Silmaril.Elgot.ITree (Tree)

universe u v w
variable {Events : Type w → Type w} {F : Type v} {α β : Type u}
  {blocks publicBlocks exits publicExits captures publicCaptures : Nat}

/-- Change atomic carriers while keeping the entire product and sum shape,
including the encoded ordered exit index. -/
def valueCodec (atom : α → β) : Value α → Value β
  | .atom a => .atom (atom a)
  | .unit => .unit
  | .pair x y => .pair (valueCodec atom x) (valueCodec atom y)
  | .inl x => .inl (valueCodec atom x)
  | .inr x => .inr (valueCodec atom x)

def resultCodec (atom : α → β) (result : Transfer α) : Transfer β :=
  (result.1, valueCodec atom result.2)

/-- Read one local flat region under its actual capture environment,
splitting its numbered transfer into an exit or a next block packet. -/
noncomputable def transfer (instr : Primitive Events F α) (env : Env α)
    (blocks : Nat) {labels n : Nat} (body : Flat F labels n) :
    Tree Events (Transfer α ⊕ BlockInput α blocks) :=
  splitTransfer blocks <$> region instr env body.erase

noncomputable def blockStep (instr : Primitive Events F α)
    (graph : FiniteCFG F blocks exits captures) (env : Env α) (state : BlockInput α blocks) :
    Tree Events (Transfer α ⊕ BlockInput α blocks) :=
  transfer instr (extend env state.2) blocks (graph.block state.1)

/-- Alignment is checked at the entry and at each local continuation,
including all primitive replies. The environments contain only the
decoded capture records. The state codec can change private packets
and labels while the result codec preserves the ordered outward tag. -/
structure Alignment (source : FiniteCFG F blocks exits captures)
    (target : FiniteCFG F publicBlocks publicExits publicCaptures)
    (left : Primitive Events F α) (right : Primitive Events F β)
    (leftEnv : Env α) (rightEnv : Env β) (atom : α → β) where
  state : BlockInput α blocks → BlockInput β publicBlocks
  entry : Sum.map (resultCodec atom) state <$> transfer left leftEnv blocks source.entry =
    transfer right rightEnv publicBlocks target.entry
  step : ∀ pending, Sum.map (resultCodec atom) state <$> blockStep left source leftEnv pending =
    blockStep right target rightEnv (state pending)

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback

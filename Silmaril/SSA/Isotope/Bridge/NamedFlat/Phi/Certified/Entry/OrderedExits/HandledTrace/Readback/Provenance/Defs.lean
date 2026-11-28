module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Defs

/-! # Exact row provenance for a packet-only public dispatcher -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback

open LambdaSSA (Flat FiniteCFG Tm)
open LambdaSSA.Semantics (Env)
open LambdaSSA.Semantics.Interaction (BlockInput Primitive)
open Silmaril.SSA.LambdaRTL (Val)

universe u v w

/-- The structural expression carried by a pure entry jump. Every
positional read comes from a checked capture slot. -/
def packetTerm {F : Type v} {n : Nat} : Val (Fin n) → Tm F
  | .var i => .var i.val
  | .unit => .unit
  | .pair left right => .pair (packetTerm left) (packetTerm right)

/-- Evaluate the structural packet at the source capture slots. -/
def packetValue {α : Type u} {n : Nat} (env : Env α) : Val (Fin n) → Value α
  | .var i => env i.val
  | .unit => .unit
  | .pair left right => .pair (packetValue env left) (packetValue env right)

def stateCodec {α β : Type u} {blocks publicBlocks : Nat} (count : blocks = publicBlocks)
    (atom : α → β) (state : BlockInput α blocks) : BlockInput β publicBlocks :=
  (state.1.cast count, valueCodec atom state.2)

/-- Exact erased rows in common block and exit order. Each row is scoped
to its packet alone. The source entry constructs the packet from captures,
while the public entry reads the encoded packet at its checked slot. -/
structure Provenance {F : Type v} {blocks publicBlocks exits publicExits captures publicCaptures : Nat}
    (source : FiniteCFG F blocks exits captures) (target : FiniteCFG F publicBlocks publicExits publicCaptures) where
  count : blocks = publicBlocks
  exitCount : exits = publicExits
  start : Fin blocks
  seed : Val (Fin captures)
  slot : Fin publicCaptures
  sourceEntry : source.entry.erase = .br start.val (packetTerm seed)
  publicEntry : target.entry.erase = .br start.val (.var slot.val)
  row : Fin blocks → Flat F (blocks + exits) 1
  sourceRow : ∀ i, (source.block i).erase = (row i).erase
  publicRow : ∀ i, (target.block (i.cast count)).erase = (row i).erase

/-- The two erased primitive runners expose the same requests and encoded
replies at each argument, including the behavior on malformed raw values. -/
def PrimitivesAgree {Events : Type w → Type w} {F : Type v} {α β : Type u}
    (left : Primitive Events F α) (right : Primitive Events F β) (atom : α → β) : Prop :=
  ∀ op value, valueCodec atom <$> left op value = right op (valueCodec atom value)

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback

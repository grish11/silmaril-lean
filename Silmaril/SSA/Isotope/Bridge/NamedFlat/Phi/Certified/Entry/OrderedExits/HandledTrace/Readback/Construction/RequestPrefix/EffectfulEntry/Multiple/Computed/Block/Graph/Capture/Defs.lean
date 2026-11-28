module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.EffectfulEntry.Multiple.Computed.Block.Graph.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Capture.Carry.Infer.Defs

/-! # Carry immutable ambient inputs before scheduling computed transfers -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple.Computed.Block.Graph.Capture

open LambdaSSA (FiniteCFG Flat)
open LambdaSSA.Semantics (Env)
open LetCase.LocallyNameless (Tm)
open Silmaril.SSA.LambdaRTL (Val)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible (Atom PacketType PrimitiveSignature)
open NamedFlat.Capture.Carry (graphList inferSlots packValue packetTypesList)

variable {F : Type} {blocks exits labels captures : Nat}

/-- Move exactly the inserted decoder prefix into a direct transfer's
operand. Other row shapes still go through the existing public grammar. -/
def transferOperand : (decoders : Nat) → {n : Nat} → Flat F labels n →
    Option (Fin labels × Tm Empty F n)
  | 0, _, .br label arg => some (label, arg)
  | k + 1, _, .let₂ pair rest =>
    (transferOperand k rest).map fun (label, arg) => (label, .let₂ pair arg)
  | _, _, _ => none

def foldDecoders {n : Nat} (decoders : Nat) (row : Flat F labels n) : Flat F labels n :=
  match transferOperand decoders row with
  | some (label, arg) => .br label arg
  | none => row

/-- The carry pass changes internal packets only. This adapter retains its
entry and folds the generated row decoders into direct transfer operands. -/
def prepared (source : FiniteCFG F blocks exits captures) : FiniteCFG F blocks exits captures :=
  let slots := inferSlots source
  let carried := graphList source slots
  ⟨carried.entry, fun i => foldDecoders slots.length (carried.block i)⟩

structure Compiled (sig : PrimitiveSignature F) (context : BoundCtx PacketType captures)
    (packets : Fin blocks → PacketType) (outputs : Fin exits → PacketType)
    (source : FiniteCFG F blocks exits captures) where
  start : Fin blocks
  seed : Val (Fin captures)
  entry_eq : source.entry.erase = .br start.val (packetTerm seed)
  sourceTyped : letI := sig.typing; source.HasType context packets outputs
  checked : Graph.Compiled sig context (packetTypesList packets context (inferSlots source)) outputs (prepared source)

/-- The shared layout is inferred from written ambient reads. Check the
carried and scheduled table with one admission and the original exit types. -/
def compile [DecidableEq F] (sig : PrimitiveSignature F) (context : BoundCtx PacketType captures)
    (packets : Fin blocks → PacketType) (outputs : Fin exits → PacketType)
    (source : FiniteCFG F blocks exits captures) : Option (Compiled sig context packets outputs source) :=
  letI := sig.typing
  if typed : NamedFlat.check source context packets outputs = true then
    match readEntry source with
    | none => none
    | some ⟨⟨start, seed⟩, entryEq⟩ =>
      (Graph.compile sig context (packetTypesList packets context (inferSlots source)) outputs (prepared source)).map
        fun checked => ⟨start, seed, entryEq, NamedFlat.check_sound _ _ _ _ typed, checked⟩
  else none

/-- The public input is the original entry packet followed by the
inferred immutable fields in the same order as the carried packet. -/
def Compiled.inputRecord {A : Type 1} {sig : PrimitiveSignature F} {context : BoundCtx PacketType captures}
    {packets : Fin blocks → PacketType} {outputs : Fin exits → PacketType}
    {source : FiniteCFG F blocks exits captures} (built : Compiled sig context packets outputs source)
    (atom : A → Atom) (env : Env A) : Env Atom :=
  fun _ => valueCodec atom (packValue env (inferSlots source) (packetValue env built.seed))

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple.Computed.Block.Graph.Capture

module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Payload.Ordered.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Payload.State.Thms
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Model.Ranked.Thms

/-! # One ranked entry for the ordered live-out packet profile -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut

open Silmaril.SSA.LambdaRTL (CFG)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open LambdaSSA.UB.Overlay
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent (Packet)
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native (Typed)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
  (ReplyEnumeration ConfigurationEnumeration)
open LambdaSSA.UB.Overlay.Shape.TwoRequest (Tag)
open Recognize (Bit interface requestTypes)
open PayloadRecognition (Incoming)

attribute [local instance] requestTypes

universe v

def isSet : Value Unit → Bool
  | .inr _ => true
  | _ => false

def readBits : Value Unit → Bool × Bool
  | .pair .unit (.pair a (.pair b .unit)) => (isSet a, isSet b)
  | _ => (false, false)

def outputDecode (i : Fin 8) : Packet Outputs :=
  outputPacket ⟨i.val / 4, by omega⟩ (i.val / 2 % 2 == 1) (i.val % 2 == 1)

def outputEncode (p : Packet Outputs) : Fin 8 :=
    let bits := readBits p.2.val
    ⟨p.1.val * 4 + (if bits.1 then 2 else 0) + (if bits.2 then 1 else 0), by
      have bound := p.1.isLt
      change p.1.val < 2 at bound
      split <;> split <;> omega⟩

variable {V K : Type 1} [DecidableEq V] [DecidableEq K]

/-- Interpret the original mutable run under a typed deterministic handler
on an arbitrary store carrier, then decorate the decoded original exit. -/
noncomputable def observeNamedOn {Φ : Type} {σ : Type v}
    (source : CFG V K Φ) (names : Fin 5 ≃ K) (first second : V) (store : V → Value Runtime)
    (literals : Φ → Option Bool) (prim : Syntax.StatePrimitives Φ σ) (s : σ)
    (selected : Tag → Bool) : Behaviour 2 Unit σ :=
  decorateOn prim selected (observeOn prim
    (LiveOut.observeRaw (LiveBit.rawWithLiterals literals) [names 3, names 4]
      (fun _ => [first, second]) source store) s (constructorDecoder PayloadType)) PayloadType

variable {κ : Type 1} {P : FlatInstitution.Signature.{0, 0} κ}
  {seed first second : V} {names : Fin 5 ≃ K} {source target : CFG V K P.Instr}

/-- Compare complete ordered records at the existing one-ranked carrier.
If both entries are unranked, or a named or native readback fails, there
is no verdict. -/
def compareRanked? [DecidableEq P.Instr]
    {a : Admission P (interface seed names) (fields first second) source}
    {b : Admission P (interface seed names) (fields first second) target}
    {op op' : P.Instr} {literals : P.Instr → Option Bool} {results : Nat}
    (left : Option (Checked a op literals)) (right : Option (Checked b op' literals))
    (raw raw' : Typed P.Instr [Bit] Outputs) (selected selected' : Tag → Bool)
    (codec : Fin results ≃ Packet Outputs) (caller : Syntax.Payload Bit)
    (replies : ReplyEnumeration (Recognize.signature P.Instr))
    (configs : ConfigurationEnumeration Incoming) : Option Bool := do
  let l ← left
  let r ← right
  let g := l.profile.endpoint op selected
  let h := r.profile.endpoint op' selected'
  if g.control.entryCheck || h.control.entryCheck then
    g.checkAllInterpreters? h raw raw' codec caller caller replies configs configs (g.control.rankedStores h.control)
  else none

end Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut

module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Thms

/-! # A single assigned constructor bit at each ordinary exit -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.LiveBit

open Silmaril.SSA.LambdaRTL (CFG)
open LambdaSSA.Semantics.Interaction (Primitive Transfer)
open LambdaSSA.UB.Overlay
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native (Typed jump withExitUB)
open LambdaSSA.UB.Overlay.Shape.TwoRequest (Exits Tag)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
  (ConfigurationEnumeration ReplyEnumeration)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.ScheduleSearch (StateInventory)
open Recognize (Bit Packets bitValue)

attribute [local instance] Recognize.requestTypes

/-- One typed field of the final named store is read at either ordered exit. -/
def fields {κ V K : Type 1} (reg : V) : K → List (V × Ty κ) :=
  fun _ => [(reg, .coprod .unit .unit)]

abbrev PayloadType : Syntax.Ty := .product .unit (.product Bit .unit)
abbrev LiveExits : List Syntax.Ty := List.replicate 2 PayloadType

def payloadExpr {Γ : List Syntax.Ty} (bit : Bool) : Syntax.Expr Γ PayloadType :=
  .pair .unit (.pair (if bit then .inr .unit else .inl .unit) .unit)

/-- Read the actual register field in the packed named return. -/
def decodeBitAtExit : Transfer Runtime → Option (Tag × Bool)
  | (0, .inl (.pair .unit (.pair bit .unit))) => (decodeBit bit).map fun b => (0, b)
  | (0, .inr (.inl (.pair .unit (.pair bit .unit)))) => (decodeBit bit).map fun b => (1, b)
  | _ => none
where
  decodeBit : Value Runtime → Option Bool
    | .inl .unit => some false
    | .inr .unit => some true
    | _ => none

/-- Decode the old unit and one typed constructor bit at the original tag. -/
def decodeTyped (out : Transfer Runtime) : Option (Tag × Syntax.Payload PayloadType) :=
  (decodeBitAtExit out).map fun (i, bit) => (i, (payloadExpr bit).eval Syntax.emptyBindings)

def decode : ExitDecoder :=
  fun out => (decodeTyped out).map fun (i, payload) => (i, payload.val)

/-- Terminal unit-to-bit instructions are interpreted by this pure table.
Guarded bit queries still use the original request and typed reply. -/
def rawWithLiterals {Φ : Type} (literals : Φ → Option Bool) : Primitive (Request Φ) Φ Runtime
  | op, .unit => match literals op with
    | some bit => pure (bitValue bit)
    | none => Silmaril.Elgot.ITree.diverge
  | op, value => raw op value

abbrev profile {Φ : Type} (exitOp : Tag → Φ) (bits : Tag → Bool) : Recognize.LiveProfile Φ :=
  fun i => some (exitOp i, bits i)

/-- Reuse the original mutable run and its checked singleton store projection.
The exit decoder reads the value returned by that run. -/
noncomputable def observeNamed {Φ : Type} {states : Nat} {V K : Type 1}
    [DecidableEq V] [DecidableEq K] (source : CFG V K Φ) (names : Fin 5 ≃ K) (reg : V)
    (input : V → Value Runtime) (literals : Φ → Option Bool) (prim : Syntax.Primitives Φ states) (s : Fin states)
    (selected : Tag → Bool := fun _ => false) : Behaviour LiveExits.length Unit (Fin states) :=
  decorate prim selected
    (FixedCarrier.observe prim (LiveOut.observeRaw (rawWithLiterals literals) [names 3, names 4] (fun _ => [reg]) source input) s decode) PayloadType

def nativeExit {Φ : Type} (bits : Tag → Bool) (i : Tag) :
    Typed Φ (Exits.get i :: [Bit]) LiveExits :=
  jump i (List.getElem_replicate i.isLt) (payloadExpr (bits i))

/-- Use the exact guarded native control and the existing exit selection.
The typed continuation emits the singleton record at the original tag. -/
def nativeEndpoint {Φ : Type} (raw : Typed Φ [Bit] Exits)
    (bits : Tag → Bool) (selected : Tag → Bool) : Region Φ [Bit] LiveExits :=
  .lsubst (withExitUB raw selected) fun i => .native (nativeExit bits i)

/-- Result codes still represent ordered tags. In this fragment the bit is
fixed by the checked terminal assignment at that tag. -/
def compare {states : Nat} (bits other : Tag → Bool) (r t : Result 2 states) : Bool :=
  decide (r.refines t) &&
    match r, t with
    | .ret i _, .ret j _ => bits i == other j
    | _, _ => true

def check? {Φ : Type} [DecidableEq Φ] {states : Nat}
    (op other : Φ) (routes routes' : Recognize.Routes)
    (native native' : Typed Φ [Bit] Exits) (bits bits' selected selected' : Tag → Bool)
    (caller : Syntax.Payload Bit) (replies : ReplyEnumeration (Recognize.signature Φ))
    (configs : ConfigurationEnumeration Packets) (stores : StateInventory states) : Option Bool :=
  let g := withSelectedExits op routes selected
  let h := withSelectedExits other routes' selected'
  if g.checkNative native && h.checkNative native' then
    some (g.checkAllInterpretersBy h caller caller replies configs configs stores (compare bits bits'))
  else none

end Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.LiveBit

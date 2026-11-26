module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.Defs

/-! # Structural reply frames with bit and unit fields -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay

open Silmaril
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload

local instance framesDefsHasTy : HasTy signature.Instr (Ty Empty) := signature.hasTy

/-- The structural product carried by the selected compiler. A retained-bit
guard adds a unit field, then its request adds a bit field. -/
inductive ReplyFrame : Ty Empty → Type where
  | base : ReplyFrame unit
  | unit {X : Ty Empty} (older : ReplyFrame X) : ReplyFrame (product X Silmaril.unit)
  | bit {X : Ty Empty} (older : ReplyFrame X) : ReplyFrame (product X Bit)

/-- The standard reply packet has only bit fields above its base unit. -/
def ReplyFrame.standard : (n : Nat) → ReplyFrame (replyContext n)
  | 0 => .base
  | n + 1 => .bit (standard n)

/-- A bit projection through the actual product frames. -/
inductive ReplyFrame.Slot : {X : Ty Empty} → ReplyFrame X → Type where
  | newest {X : Ty Empty} (older : ReplyFrame X) : Slot (.bit older)
  | retainUnit {X : Ty Empty} {older : ReplyFrame X} (slot : Slot older) : Slot (.unit older)
  | retainBit {X : Ty Empty} {older : ReplyFrame X} (slot : Slot older) : Slot (.bit older)

def ReplyFrame.Slot.term : {X : Ty Empty} → {frame : ReplyFrame X} → Slot frame → Term signature.Instr X Bit
  | _, _, .newest _ => .snd _ Bit
  | _, _, .retainUnit slot => retainSlot (A := Silmaril.unit) slot.term
  | _, _, .retainBit slot => retainSlot (A := Bit) slot.term

def ReplyFrame.bindSlots {X : Ty Empty} {frame : ReplyFrame X} {n : Nat}
    (slots : Fin n → Slot frame) : Fin (n + 1) → Slot (.bit frame) :=
  Fin.cases (.newest frame) (fun i => .retainBit (slots i))

def ReplyFrame.standardSlots : (n : Nat) → Fin n → Slot (standard n)
  | 0, i => i.elim0
  | n + 1, i => bindSlots (standardSlots n) i

/-- Remove the tested logical slot, retain the other projections under the
unit field, and add the new reply. -/
def ReplyFrame.guardSlots {X : Ty Empty} {frame : ReplyFrame X} {n : Nat}
    (slots : Fin (n + 1) → Slot frame) (test : Fin (n + 1)) : Fin (n + 1) → Slot (.bit (.unit frame)) :=
  bindSlots (fun i => .retainUnit (slots (test.succAbove i)))

/-- The exact constructor packets used by case extensionality. Unit fields
are kept as typed lexical values, including the original base unit. -/
abbrev ReplyFrame.UnitValue (Γ : List (Ty Empty)) :=
  {a : Tm signature.Instr // Tm.BranchValue Γ a Silmaril.unit}

inductive ReplyFrame.Value (Γ : List (Ty Empty)) : {X : Ty Empty} → ReplyFrame X → Type where
  | base (value : UnitValue Γ) : Value Γ .base
  | unit {X : Ty Empty} {older : ReplyFrame X} (value : Value Γ older)
      (payload : UnitValue Γ) : Value Γ (.unit older)
  | bit {X : Ty Empty} {older : ReplyFrame X} (value : Value Γ older)
      (tag : Bool) (payload : UnitValue Γ) : Value Γ (.bit older)

/-- The type of the actual rebuilt packet is determined by its frame. -/
def ReplyFrame.Value.elaborate {Γ : List (Ty Empty)} : {X : Ty Empty} → {frame : ReplyFrame X} →
    Value Γ frame → {a : Tm signature.Instr // Tm.BranchValue Γ a X}
  | _, _, .base u => u
  | _, _, .unit older u => ⟨_, .pair older.elaborate.property u.property⟩
  | _, _, .bit older false u => ⟨_, .pair older.elaborate.property (.inl u.property)⟩
  | _, _, .bit older true u => ⟨_, .pair older.elaborate.property (.inr u.property)⟩

/-- Read a projected tag and its constructor payload from a case packet. -/
def ReplyFrame.Slot.read {Γ : List (Ty Empty)} : {X : Ty Empty} → {frame : ReplyFrame X} →
    Slot frame → Value Γ frame → Bool × UnitValue Γ
  | _, _, .newest _, .bit _ b u => (b, u)
  | _, _, .retainUnit slot, .unit older _ => slot.read older
  | _, _, .retainBit slot, .bit older _ _ => slot.read older

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay

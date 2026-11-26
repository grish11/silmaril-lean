module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Defs

/-! # Feed a typed predecessor-indexed φ admission to checked RTL lowering -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry

open LambdaSSA.Semantics.Interaction.Typed.Ordered (FlatInstitution.Signature)
open NamedFlat.Entry (Interface)

universe u v

variable {κ V K Reg Label : Type (u + 1)} {n : Nat} {β : BoundCtx (Ty κ) n}

/-- Names for the same supplied input slots and a single ordered return.
The φ return carries the old payload paired with this ordered live-out record. -/
structure ReverseInterface (κ Reg Label : Type (u + 1)) (n : Nat) where
  inputs : Fin n → Reg
  distinct : Function.Injective inputs
  exit : Label
  payload : Ty κ
  liveOut : List (Reg × Ty κ)

/-- Only the reverse runner's register and exit names are chosen here. The
input slot types and order come from the admitted φ context. -/
def ReverseInterface.named (I : ReverseInterface κ Reg Label n) (β : BoundCtx (Ty κ) n) :
    Interface κ Reg Label :=
  ⟨n, β, I.inputs, I.distinct, [I.exit], fun _ => I.payload⟩

def ReverseInterface.external (I : ReverseInterface κ Reg Label n) : Fin 1 → Ty κ :=
  fun _ => .product I.payload (NamedFlat.Entry.LiveOut.recordType I.liveOut)

variable [DecidableEq V] [DecidableEq K] [DecidableEq Reg] [DecidableEq Label]
  {P : FlatInstitution.Signature.{u, v} κ} {C : Captures V β}

/-- The checked lowerer reads back to the actual positional table from φ
admission. Its sole numbered exit carries the same record as the φ return. -/
abbrev ReverseLowered (I : ReverseInterface κ Reg Label n) (a : Admitted P C K I.external) :=
  NamedFlat.Entry.Reverse.Lowered (I.named β) (fun _ => I.liveOut) a.toSSA.table.code

/-- Run the existing packet-local reverse checker on the admitted φ table. -/
def Admitted.reverseChecked (I : ReverseInterface κ Reg Label n) (a : Admitted P C K I.external)
    [DecidableEq P.Instr] (registers : NamedFlat.Entry.Reverse.Registers Reg)
    (internal : Fin a.toSSA.table.blocks → Label) : Option (ReverseLowered I a) :=
  NamedFlat.Entry.Reverse.lowerChecked (I.named β) (fun _ => I.liveOut)
    registers internal a.toSSA.table.code

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry

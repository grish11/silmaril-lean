module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Saved.Prefix.Defs

/-! # Typed insertion into an existing saved preheader prefix -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Saved.Prefix

open Silmaril.MLIR.Arith (Var Width)
open Silmaril.MLIR.Pure (Operands)
open Silmaril.MLIR.SCF (For)
open Loop.MLIR.CF (TargetOp)

variable {Input Γ args : List Width} {w : Width}

/-- The physical scope after inserting a let. Header packets still put the
    new value first and keep all previous logical slots in order. -/
structure Insertion (Input Γ : List Width) (w : Width) where
  physical : List Width
  leading : Prefix Input physical
  previous : Rename Γ physical
  inserted : Var physical w

def Insertion.toPhysical (edit : Insertion Input Γ w) : Rename (w :: Γ) edit.physical :=
  replaceBinding edit.previous edit.inserted

/-- Discard a binding from the operand scope only when no operand reads it. -/
def beforeBinding {later : Width} : Origins Γ (later :: Γ) :=
  afterBinding (fun ref => .inl ref) 0

/-- Insert before exactly `trailing` old lets, keeping their original order.
    Each crossed let must be absent from the incoming operand tuple. -/
def insert? (op : TargetOp args w) : (trailing : Nat) → {Γ : List Width} →
    Prefix Input Γ → Operands Γ args → Option (Insertion Input Γ w)
  | 0, _, leading, operands =>
    some ⟨_, .snoc leading op operands, Var.there, .here⟩
  | _ + 1, _, .nil, _ => none
  | trailing + 1, _, .snoc prior later operands, inputs => do
    let earlier ← captureOrigins? beforeBinding inputs
    let edit ← insert? op trailing prior earlier
    pure ⟨_, .snoc edit.leading later (For.renameOperands edit.previous operands),
      under edit.previous, .there edit.inserted⟩

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Saved.Prefix

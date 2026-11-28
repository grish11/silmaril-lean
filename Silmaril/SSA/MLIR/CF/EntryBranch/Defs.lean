module

public import Silmaril.SSA.MLIR.CF.Basic.Defs

/-! Link two typed CFGs behind one entry branch. -/

@[expose] public section

namespace Silmaril.MLIR.CF.EntryBranch

open Arith (Width)
open Silmaril.MLIR.Pure (OpSignature)

variable {Op : OpSignature} {Arms : Bool → List Width → Type} {Input Result Γ : List Width}

/-- Each arm has its own labels and an entry with no new arguments.
The original typed external input is already in scope at both entries. -/
inductive Label (Arms : Bool → List Width → Type) : List Width → Type where
  | entry (side : Bool) : Label Arms []
  | body (side : Bool) {args : List Width} : Arms side args → Label Arms args

def edge (side : Bool) (dest : Edge (Arms side) Γ) : Edge (Label Arms) Γ :=
  ⟨.body side dest.label, dest.args⟩

def terminator (side : Bool) : Terminator (Arms side) Result Γ → Terminator (Label Arms) Result Γ
  | .br dest => .br (edge side dest)
  | .condBr test yes no => .condBr test (edge side yes) (edge side no)
  | .ret values => .ret values

/-- The two fragments' operation bindings and operands are reused.
Only branch labels are renamed. -/
def link (guard : Block Op (Label Arms) Input Result) (arms : ∀ side, Cfg Op (Arms side) Input Result) :
    Cfg Op (Label Arms) Input Result where
  entry := guard
  block
    | .entry side => (arms side).entry.mapTerm (terminator side)
    | .body side label => ((arms side).block label).mapTerm (terminator side)

end Silmaril.MLIR.CF.EntryBranch

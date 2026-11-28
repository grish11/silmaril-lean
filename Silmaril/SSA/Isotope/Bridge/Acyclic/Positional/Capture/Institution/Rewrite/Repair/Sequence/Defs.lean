module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Thms

/-! # Closed ordered effect sequences with optional effectful empty elimination -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Sequence

open LambdaSSA.Acyclic (Operand)
open Isotope.LetCase.LocallyNameless (AbortCongr)

abbrev Sorts := Ty Empty

inductive Op where
  | emit (bit : Bool)
  | stop (bit : Bool)

def signature : InstrSig Sorts Bool where
  Instr := Op
  hasTy := ⟨fun _ => .unit, fun op => match op with
    | .emit _ => .unit
    | .stop _ => .empty⟩
  hasEff := ⟨fun _ => true⟩

/-- An ordered list of effectful unit calls, ending in a return or a call
to an empty-producing primitive. The latter has two written forms. -/
inductive Body where
  | returnUnit
  | emit (bit : Bool) (next : Body)
  | stop (bit : Bool) (sequenced : Bool)

/-- An independent normal form retaining the occurrence order and the
terminal primitive, when there is one. -/
abbrev Normal := List Bool × Option Bool

def Body.normal : Body → Normal
  | .returnUnit => ([], none)
  | .emit bit next => (bit :: next.normal.1, next.normal.2)
  | .stop bit _ => ([], some bit)

/-- Render a normal form with direct empty elimination. -/
def Normal.body : List Bool → Option Bool → Body
  | [], none => .returnUnit
  | [], some bit => .stop bit false
  | bit :: rest, last => .emit bit (Normal.body rest last)

def Body.canonical (p : Body) : Body :=
  Normal.body p.normal.1 p.normal.2

/-- All operation arguments are literals. An emit evaluates once and the
continuation leaves its packet unused. -/
def Body.operand {n : Nat} (β : BoundCtx Sorts n) : Body → Operand signature.Instr β Ty.unit
  | .returnUnit => ⟨.unit, .unit⟩
  | .emit bit next =>
    let b := next.operand (β.snoc Ty.unit)
    ⟨.let₁ (.op (.emit bit) .unit) b.1, .let₁ (.op .unit) b.2⟩
  | .stop bit false => ⟨.abort (.op (.stop bit) .unit), .abort (.op .unit)⟩
  | .stop bit true =>
    ⟨.let₁ (.op (.stop bit) .unit) (.abort (.bv 0)), .let₁ (.op .unit) (.abort .bv)⟩

/-- The actual witnessed equation on a common ordered interface. The
selected position is zero and the tail payload types are arbitrary. -/
def equation (tail : List Sorts) (p q : Body) : GrammarEquation signature :=
  ⟨⟨0, .nil, Ty.unit :: tail⟩, Rewrite.returnUnit tail (p.operand .nil),
    Rewrite.returnUnit tail (q.operand .nil)⟩

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Sequence

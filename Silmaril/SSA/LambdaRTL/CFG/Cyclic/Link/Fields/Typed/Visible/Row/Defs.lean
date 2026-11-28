module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Defs

/-! # Elaborate positional rows into the existing typed public dispatcher -/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

open Silmaril.Isotope.LambdaSSA (Tm)

variable {F : Type} {blocks exits : Nat}

/-- Look up the newest-first positional slot together with its exact type. -/
def slotAt : (context : List PacketType) → Nat → Option (Σ ty, Slot context ty)
  | [], _ => none
  | ty :: _, 0 => some ⟨ty, .here⟩
  | _ :: rest, i + 1 => (slotAt rest i).map fun ⟨ty, old⟩ => ⟨ty, .there old⟩

def elaborateExpr (context : List PacketType) : Tm F → Option (Σ ty, Expr context ty)
  | .var i => (slotAt context i).map fun ⟨ty, slot⟩ => ⟨ty, .var slot⟩
  | .unit => some ⟨.unit, .unit⟩
  | .pair left right => do
    let ⟨a, x⟩ ← elaborateExpr context left
    let ⟨b, y⟩ ← elaborateExpr context right
    pure ⟨.product a b, .pair x y⟩
  | _ => none

def elaborateArg (context : List PacketType) (ty : PacketType) (arg : Tm F) : Option (Expr context ty) := do
  let ⟨found, expr⟩ ← elaborateExpr context arg
  if h : found = ty then some (h ▸ expr) else none

/-- Positional readback puts internal blocks before ordered exits. -/
def readLabel (blocks exits : Nat) (label : Nat) : Option (Link.Label blocks exits) :=
  if h : label < blocks + exits then some (finSumFinEquiv.symm ⟨label, h⟩) else none

variable (types : Link.Label blocks exits → PacketType)

def elaborateBranch : (context : List PacketType) → Silmaril.Isotope.LambdaSSA.Region F → Option (Branch types context)
  | context, .br index arg => do
    let label ← readLabel blocks exits index
    return .jump label (← elaborateArg context (types label) arg)
  | context, .case discr left right => do
    let ⟨.coprod a b, value⟩ ← elaborateExpr context discr | none
    return .case value (← elaborateBranch (a :: context) left) (← elaborateBranch (b :: context) right)
  | _, _ => none

/-- Reify the public grammar. A row can unpack products before a pure
terminator, or make one primitive request followed by a literal jump. -/
def elaborateRow (signature : PrimitiveSignature F) :
    (context : List PacketType) → Silmaril.Isotope.LambdaSSA.Region F → Option (Code signature types context)
  | context, .let₂ expr body => do
    let ⟨.product a b, value⟩ ← elaborateExpr context expr | none
    return .unpack value (← elaborateRow signature (b :: a :: context) body)
  | context, .let₁ (.op op arg) (.br index next) => do
    let value ← elaborateArg context (signature.argument op) arg
    let label ← readLabel blocks exits index
    let packet ← elaborateArg (signature.reply op :: context) (types label) next
    return .apply op value label packet
  | context, body => (elaborateBranch types context body).map .term

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

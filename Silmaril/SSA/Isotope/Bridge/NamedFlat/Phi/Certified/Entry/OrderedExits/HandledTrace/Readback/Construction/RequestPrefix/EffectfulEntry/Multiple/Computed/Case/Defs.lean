module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.EffectfulEntry.Multiple.Computed.Defs

/-! # Schedule case tests and branch-local operands -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple.Computed

open LambdaSSA (Region Tm)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible (PacketType PrimitiveSignature)

variable {F : Type} {Γ : List PacketType} {a b : PacketType} {sig : PrimitiveSignature F}

/-- The operand supplies one sum to the sole dispatch. Each case payload
stays at slot zero, and older slots move past the schedule. -/
def scheduleCase (test : Operand sig Γ (.coprod a b)) (left right : Region F) : Region F :=
  let scheduled := test.schedule
  let shift := Silmaril.DeBruijn.lift scheduled.requests.shift
  scheduled.requests.wrap Region.let₁ Region.let₂
    (.case (scheduled.value.erase position) (left.renameVars shift) (right.renameVars shift))

structure CaseTest (sig : PrimitiveSignature F) (Γ : List PacketType) (written : Tm F) where
  leftType : PacketType
  rightType : PacketType
  operand : Operand sig Γ (.coprod leftType rightType)
  source_eq : written = operand.written

def readCaseTest [DecidableEq F] (sig : PrimitiveSignature F) (Γ : List PacketType) (test : Tm F) :
    Option (CaseTest sig Γ test) := do
  let ⟨.coprod a b, arg⟩ ← readOperand sig Γ test | none
  if exactTest : test = arg.written then some ⟨a, b, arg, exactTest⟩ else none

def productTypes (sig : PrimitiveSignature F) (Γ : List PacketType) (value : Tm F) :
    Option (PacketType × PacketType) := do
  let ⟨.product a b, _⟩ ← readOperand sig Γ value | none
  return (a, b)

/-- Traverse written binders with the operand checker's types. A request
argument is scheduled inside its current arm, before the request and its
reply continuation. A transfer operand uses the original destination's type.
The continuation checker verifies the resulting row. -/
def scheduleCases [DecidableEq F] (sig : PrimitiveSignature F) {labels : Nat} (types : Fin labels → PacketType) :
    List PacketType → Region F → Option (Region F)
  | Γ, .br label arg =>
    if within : label < labels then
      (readArgument sig Γ (types ⟨label, within⟩) arg).map (fun found => scheduleJump label found.val)
    else none
  | Γ, .let₁ (.op op argument) tail =>
    (readArgument sig Γ (sig.argument op) argument).bind fun arg =>
      (scheduleCases sig types (sig.reply op :: Γ) tail).map (hoist op arg.val)
  | Γ, .let₁ value tail => (readOperand sig Γ value).bind fun found =>
    (scheduleCases sig types (found.1 :: Γ) tail).map (.let₁ value)
  | Γ, .let₂ value tail => (productTypes sig Γ value).bind fun (a, b) =>
    (scheduleCases sig types (b :: a :: Γ) tail).map (.let₂ value)
  | Γ, .case test left right => (readCaseTest sig Γ test).bind fun found =>
    (scheduleCases sig types (found.leftType :: Γ) left).bind fun left =>
      (scheduleCases sig types (found.rightType :: Γ) right).map (scheduleCase found.operand left)
  | _, .cfg .. => none

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple.Computed

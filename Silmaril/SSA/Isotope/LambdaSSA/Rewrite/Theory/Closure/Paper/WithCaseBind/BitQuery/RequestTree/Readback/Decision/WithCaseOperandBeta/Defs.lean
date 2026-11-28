module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Readback.Defs

/-! # Opt-in beta for the focused Bit request operand -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree.Readback.WithCaseOperandBeta

open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)

abbrev U := (Ty.unit : Ty Empty)

/-- The literal original request, with both reply continuations unchanged. -/
def source (label b : Bool) (payload : Tm signature.Instr) (l r : Region signature.Instr) :
    Region signature.Instr :=
  .case (.op (.ask label) (caseOperand (constructorBit b payload))) l r

theorem operand_typed {Γ : List (Ty Empty)} {payload : Tm signature.Instr} (b : Bool)
    (h : Tm.BranchValue Γ payload U) :
    Tm.HasType Γ (caseOperand (constructorBit b payload)) Bit :=
  .case (constructorBit_value b h).hasType
    (constructorBit_value false .unit).hasType (constructorBit_value true .unit).hasType

theorem source_typed {Γ L : List (Ty Empty)} {payload : Tm signature.Instr}
    (label b : Bool) (h : Tm.BranchValue Γ payload U) {l r : Region signature.Instr}
    (hl : ValueBranches (Bit :: Γ) l L) (hr : ValueBranches (Bit :: Γ) r L) :
    ValueBranches Γ (source label b payload l r) L :=
  .case (.op (operand_typed b h)) hl hr

theorem target_typed {Γ L : List (Ty Empty)} (label b : Bool) {l r : Region signature.Instr}
    (hl : ValueBranches (Bit :: Γ) l L) (hr : ValueBranches (Bit :: Γ) r L) :
    ValueBranches Γ (requestRegion label b l r) L :=
  .case (.op (constructorBit_value b .unit).hasType) hl hr

/-- Only the focused constructor-known case on the unit binder at slot zero.
This rule leaves the primitive label, reply terms and ordered exits intact. -/
inductive Step : VCtx (Ty Empty) → Region signature.Instr → Region signature.Instr → LCtx (Ty Empty) → Prop where
  | reduce {Γ L : List (Ty Empty)} (label b : Bool) {l r : Region signature.Instr}
      (hl : ValueBranches (Bit :: U :: Γ) l L) (hr : ValueBranches (Bit :: U :: Γ) r L) :
      Step (U :: Γ) (source label b (.var 0) l r) (requestRegion label b l r) L

abbrev Eqv := Paper.Extension.Eqv Step

def quote (label : Bool) : Tree 1 :=
  .ask label (.read 0) (.ret false 0) (.ret true 0)

def staged (label : Bool) : Candidate :=
  ⟨(quote label).region inputSlots, (quote label).typed inputSlots⟩

def original (label : Bool) : Candidate :=
  ⟨call label (caseOperand (.var 0)), call_typed label
    (.case (.var (i := 0) rfl) (constructorBit_value false .unit).hasType
      (constructorBit_value true .unit).hasType)⟩

def recognizedLabel : Region signature.Instr → Option Bool
  | .case (.op (.ask label) (.case (.var 0) (.inl .unit) (.inr .unit))) (.br 0 (.var 0)) (.br 1 (.var 0)) =>
    some label
  | _ => none

/-- Admit the exact singleton spelling from #4792 at either request label.
The existing reader reads the certified staging. -/
def readTermCase (fuel : Nat) (p : Candidate) : Option (Tree 1) := do
  let label ← recognizedLabel p.val
  (staged label).readWithDecisions fuel

def packed (p : Candidate) :=
  Paper.Extension.Singleton.ofRegion Step p.property.packExits

def packedTree (t : Tree 1) :=
  Paper.Extension.Singleton.ofRegion Step t.guarded_typed.packExits

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree.Readback.WithCaseOperandBeta

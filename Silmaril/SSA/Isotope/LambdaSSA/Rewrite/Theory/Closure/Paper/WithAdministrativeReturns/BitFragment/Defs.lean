module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Readback.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Model.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.Thms

/-! # A typed block-free case, call and forwarding fragment -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment

open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery
  (signature Exits call call_typed Trace model modelCoherent)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree
  (Tree Observation)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit Answer bit)
open Silmaril.Isotope.LambdaSSA.Acyclic.Native (Endpoint)
open Silmaril.Isotope.LetCase.Structural.Finite (Shape StructuralContext)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (InstructionModel)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli

/-- A case on the first reply selects a slot for the second query. Both
arms can write their slot read under a nested, pure forwarding let. -/
structure Program where
  testLabel : Bool
  callLabel : Bool
  leftSlot : Fin 2
  rightSlot : Fin 2
  nested : Bool

def arm (nested : Bool) (i : Fin 2) : Tm signature.Instr :=
  if nested then .let₁ .unit (.var (i.val + 1)) else .var i.val

/-- An exact known-constructor operand forwards the selected Bit. -/
def operand : Tm signature.Instr := .case (.inl (.var 0)) (.var 0) (.var 2)

def Program.region (p : Program) : Region signature.Instr :=
  .let₁ (.case (.op (.ask p.testLabel) (.var 0)) (arm p.nested p.leftSlot) (arm p.nested p.rightSlot))
    (call p.callLabel operand)

def Program.tree (p : Program) : Tree 1 :=
  .ask p.testLabel (.read 0)
    (.ask p.callLabel (.read p.leftSlot) (.ret false 0) (.ret true 0))
    (.ask p.callLabel (.read p.rightSlot) (.ret false 0) (.ret true 0))

theorem slot_typed (i : Fin 2) : At [Bit, Bit] i.val Bit := by
  fin_cases i <;> rfl

theorem arm_typed (nested : Bool) (i : Fin 2) : Tm.HasType [Bit, Bit] (arm nested i) Bit := by
  cases nested
  · exact .var (slot_typed i)
  · exact .let₁ .unit (.var (i := i.val + 1) (slot_typed i))

theorem test_typed (label : Bool) :
    Tm.HasType [Bit] (.op (.ask label) (.var 0) : Tm signature.Instr) Answer :=
  .op (.var (i := 0) rfl)

theorem operand_typed : Tm.HasType [Bit, Bit] operand Bit :=
  .case (B := Bit) (.inl (.var (i := 0) rfl))
    (.var (i := 0) rfl) (.var (i := 2) rfl)

theorem Program.typed (p : Program) : ValueBranches [Bit] p.region Exits :=
  .let₁ (.case (test_typed p.testLabel) (arm_typed p.nested p.leftSlot)
    (arm_typed p.nested p.rightSlot)) (call_typed p.callLabel operand_typed)

abbrev bitShape : Shape := .sum .unit .unit

instance finiteSignature : Silmaril.Isotope.LetCase.Structural.Finite.Signature signature.Instr where
  source _ := bitShape
  target _ := .sum bitShape bitShape

theorem inputStructural : StructuralContext (.snoc .nil Bit) :=
  .snoc .nil bitShape

/-- Use the existing acyclic compiler on exactly the original region after
literal packing of its two typed exits. -/
def Program.endpoint (p : Program) :
    Endpoint signature.Instr (.snoc .nil Bit) (packedExitType Exits) :=
  ⟨p.region.packExits, p.typed.packExits.hasType, .let₁ _ (.case _ (.br _) (.br _))⟩

/-- The native arrow of the supplied written region at its actual packed interface. -/
def Program.packed (p : Program) :=
  Paper.Extension.Singleton.ofRegion (Step false) p.typed.packExits

/-- Native LetCase equality on the compiler outputs of the original packed syntax. -/
def Program.CompiledEq (p q : Program) : Prop :=
  Silmaril.Isotope.LetCase.LocallyNameless.Equiv false
    Silmaril.Isotope.LetCase.Structural.Reply.Γ₀ (.snoc .nil Bit)
    p.endpoint.compile.1 q.endpoint.compile.1 (packedExitType Exits)

local notation "J" => _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli.J (m := Trace)
local notation "M" => types

noncomputable local instance : InstructionModel J M signature.Instr := instructions model
local instance : RegionTypingCoherent (Φ := signature.Instr) J M := modelCoherent

/-- Observe all tagged-reply histories at the original packed region. -/
noncomputable def Program.observations (p : Program) (g : Bool) : Set Observation :=
  ((denoteSingletonRegion J M p.typed.packExits.hasType).of (bit g)).outcomes

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment

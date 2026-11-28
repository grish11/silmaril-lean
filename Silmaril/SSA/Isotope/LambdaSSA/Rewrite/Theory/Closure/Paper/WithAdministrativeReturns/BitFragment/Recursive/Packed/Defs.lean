module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.BitFragment.Recursive.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.BitFragment.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.BitFragment.Recursive.Syntax

/-! # The actual packed arrows and their existing acyclic compiler outputs -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive

open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery
  (signature Exits Trace model modelCoherent)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree (Observation)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit bit)
open Silmaril.Isotope.LambdaSSA.Acyclic.Native (Endpoint Outward)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (InstructionModel)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli

/-- Interpret the former fixed fragment as a recursive source at the same
written region. Its operand case becomes a constructor-known query. -/
def ofStaged (p : BitFragment.Program) : Program :=
  let arm (i : Fin 2) : Code 1 2 :=
    if p.nested then .letUnit (.ret 0 i) else .ret 0 i
  .letBit (.ask p.testLabel (.read 0) (arm p.leftSlot) (arm p.rightSlot))
    (.ask p.callLabel (.known false 0 1) (.ret 0 0) (.ret 1 0))

theorem ofStaged_written (p : BitFragment.Program) : (ofStaged p).written = p.region := by
  obtain ⟨test, call, left, right, nested⟩ := p
  fin_cases left <;> fin_cases right <;> cases nested <;> rfl

theorem Program.typed (p : Program) : ValueBranches [Bit] p.written Exits :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.BitFragment.Recursive.region_typed p id

theorem Program.outward (p : Program) : Outward 0 p.written.packExits :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.BitFragment.Recursive.outward_packed p id

def Program.endpoint (p : Program) :
    Endpoint signature.Instr (.snoc .nil Bit) (packedExitType Exits) :=
  ⟨p.written.packExits, p.typed.packExits.hasType, p.outward⟩

def Program.packed (p : Program) :=
  Paper.Extension.Singleton.ofRegion (Step false) p.typed.packExits

/-- Native LetCase equality at the actual compiler outputs of the written programs. -/
def Program.CompiledEq (p q : Program) : Prop :=
  Silmaril.Isotope.LetCase.LocallyNameless.Equiv false
    Silmaril.Isotope.LetCase.Structural.Reply.Γ₀ (.snoc .nil Bit)
    p.endpoint.compile.1 q.endpoint.compile.1 (packedExitType Exits)

local notation "J" => _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli.J (m := Trace)
local notation "M" => types

noncomputable local instance : InstructionModel J M signature.Instr := instructions model
local instance : RegionTypingCoherent (Φ := signature.Instr) J M := modelCoherent

/-- The ordered trace at the exact packed representative. -/
noncomputable def Program.observations (p : Program) (g : Bool) : Set Observation :=
  ((denoteSingletonRegion J M p.typed.packExits.hasType).of (bit g)).outcomes

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive

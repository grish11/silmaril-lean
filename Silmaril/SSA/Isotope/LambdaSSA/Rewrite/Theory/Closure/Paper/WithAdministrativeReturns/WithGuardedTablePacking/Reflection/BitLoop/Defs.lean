module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.Reflection.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.BitFragment.Recursive.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Reflection.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Thms

/-! # Live one-row tables over block-free Bit programs

A program with two ordered Bit exits is used as one dispatcher step:
exit zero returns its Bit and exit one repeats with that Bit as the next
state. The loop is a one-row guarded table with a constructor entry.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.DeBruijn (lift)
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (seqValueBranches)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive (Program Code)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery (signature Exits model Trace modelCoherent)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree (Word)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value instructions)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit bit)
open _root_.Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (InstructionModel)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton (ofRegion ofType)

/-- The loop state: the packed form of the one repeat label. -/
abbrev State : Ty Empty := packedExitType [Bit]

theorem unpack_typed : ValueBranches [State] (unpackExits [Bit] : Region signature.Instr) [Bit] :=
  unpackExits_valueFamily [] [Bit] (rfl : At [State] 0 State)

/-- Decode the state and run the written program with its exits tagged. -/
def stepRegion (p : Program) : Region signature.Instr :=
  (unpackExits [Bit]).lsubst (fun _ => p.written.packExits.renameVars (lift Nat.succ))

theorem step_typed (p : Program) :
    ValueBranches [State] (stepRegion p) [Silmaril.coprod Bit State] :=
  seqValueBranches unpack_typed p.typed.packExits

/-- One feedback label around the step. -/
def loopRegion (p : Program) : Region signature.Instr :=
  SyntacticCategory.iterateRegion State (stepRegion p)

theorem loop_typed (p : Program) : ValueBranches [State] (loopRegion p) [Bit] :=
  SyntacticCategory.iterateRegion_valueBranches (step_typed p)

set_option hygiene false in
local notation "N" => Step (τ := Ty Empty) (Φ := signature.Instr) false

def stepArrow (p : Program) : ofType N State ⟶ ofType N (Silmaril.coprod Bit State) :=
  ofRegion N (step_typed p)

def loopArrow (p : Program) : ofType N State ⟶ ofType N Bit :=
  ofRegion N (loop_typed p)

local notation "J" => _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli.J (m := Trace)
local notation "M" => _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli.types

noncomputable local instance : InstructionModel J M signature.Instr := instructions model
local instance : RegionTypingCoherent (Φ := signature.Instr) J M := modelCoherent

/-- The step in the fixed ordered-trace interpreter of this signature:
every request admits all four replies and logs its event. -/
noncomputable def stepModel (p : Program) : value State → Trace (value Bit ⊕ value State) :=
  fun s => (denoteSingletonRegion J M p.typed.packExits.hasType).of (Sum.elim id PEmpty.elim s)

/-- Complete finite runs of the literal loop in that interpreter, from the
state holding `g`. A run that never returns contributes no observation. -/
noncomputable def loopObservations (p : Program) (g : Bool) : Set (Except Bool (value Bit) × Word) :=
  ((denoteSingletonRegion J M (loop_typed p).hasType).of (Sum.inl (bit g))).outcomes

/-- One request per round. The reply tag chooses between returning the
reply payload and repeating with it as the next query. -/
structure Poll where
  label : Bool
  returnRight : Bool

def Poll.program (a : Poll) : Program :=
  .ask a.label (.read 0) (.ret (if a.returnRight then 1 else 0) 0)
    (.ret (if a.returnRight then 0 else 1) 0)

/-- A program is a spelling of a poll when its reflected tree key is the
poll's. It may contain lets, unit binders and constructor-known queries. -/
def Spells (p : Program) (a : Poll) : Prop := p.tree.key = a.program.tree.key

/-- The poll that returns on a left reply, written with a forwarded alias
of the state, a constructor-known query and a unit binder. -/
def aliased (label : Bool) : Program :=
  .letBit (.ret 0 0) (.ask label (.known false 0 1) (.letUnit (.ret 0 0)) (.ret 1 0))

/-- Repeat at once with the unchanged state. -/
def spin : Program := .ret 1 0

/-- Send one request, then repeat on either reply. -/
def askSpin (label : Bool) : Program := .ask label (.read 0) (.ret 1 0) (.ret 1 0)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop

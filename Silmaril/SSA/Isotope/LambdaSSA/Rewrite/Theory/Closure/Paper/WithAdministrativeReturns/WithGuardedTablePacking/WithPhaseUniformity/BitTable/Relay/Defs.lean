module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Mixed.Defs

/-! # A mixed table whose untouched state repeats into itself

State zero runs `q` and never leaves the table. On the reply side where
`q` returns, it repeats into state zero with the returned Bit as its next
state. On the other side it enters a block of duplicated states. Each
block state runs `p`, returns outward, or repeats into state zero.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.DeBruijn (lift)
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (seqValueBranches caseValueBranches)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery (signature Trace model modelCoherent)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree (Word)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value instructions)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit bit)
open _root_.Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (InstructionModel)

/-- The loop of any dispatched rows. -/
def dispatchLoop (K : Nat) (rows : Fin (K + 1) → Region signature.Instr) : Region signature.Instr :=
  SyntacticCategory.iterateRegion (States K) (dispatch K rows)

theorem dispatchLoop_typed {K : Nat} {rows : Fin (K + 1) → Region signature.Instr}
    (h : ∀ i, ValueBranches [State] (rows i) [Silmaril.coprod Bit (States K)]) :
    ValueBranches [States K] (dispatchLoop K rows) [Bit] :=
  SyntacticCategory.iterateRegion_valueBranches (dispatch_typed K h)

/-- That loop entered at state `i` by a constructor branch. -/
def dispatchEntered (K : Nat) (rows : Fin (K + 1) → Region signature.Instr) (i : Fin (K + 1)) :
    Region signature.Instr :=
  (Region.br 0 (injTm K i (.var 0))).lsubst (fun _ => (dispatchLoop K rows).renameVars (lift Nat.succ))

theorem dispatchEntered_typed {K : Nat} {rows : Fin (K + 1) → Region signature.Instr}
    (h : ∀ i, ValueBranches [State] (rows i) [Silmaril.coprod Bit (States K)]) (i : Fin (K + 1)) :
    ValueBranches [State] (dispatchEntered K rows i) [Bit] :=
  seqValueBranches (entry_typed K i) (dispatchLoop_typed h)

theorem stay_typed (K : Nat) (j : Fin (K + 1)) :
    ValueBranches [Bit] (.br 0 (.inr (injTm K j (.inl (.var 0)))) : Region signature.Instr)
      [Silmaril.coprod Bit (States K)] :=
  .br rfl (.inr (injTm_typed (.inl (.var rfl)) K j))

/-- Route a row that never leaves: a return goes to state `j₁` with the
returned Bit as packed state, a repeat goes to state `j₂`. -/
def relayRoute (K : Nat) (j₁ j₂ : Fin (K + 1)) : Region signature.Instr :=
  .case (.var 0) ((Region.br 0 (.inr (injTm K j₁ (.inl (.var 0))))).renameVars (lift Nat.succ))
    ((Region.br 0 (.inr (injTm K j₂ (.var 0)))).renameVars (lift Nat.succ))

theorem relayRoute_typed (K : Nat) (j₁ j₂ : Fin (K + 1)) :
    ValueBranches [Silmaril.coprod Bit State] (relayRoute K j₁ j₂) [Silmaril.coprod Bit (States K)] :=
  caseValueBranches (stay_typed K j₁) (goto_typed K j₂)

def relayRow (K : Nat) (p : Program) (j₁ j₂ : Fin (K + 1)) : Region signature.Instr :=
  (stepRegion p).lsubst (fun _ => (relayRoute K j₁ j₂).renameVars (lift Nat.succ))

theorem relayRow_typed (K : Nat) (p : Program) (j₁ j₂ : Fin (K + 1)) :
    ValueBranches [State] (relayRow K p j₁ j₂) [Silmaril.coprod Bit (States K)] :=
  seqValueBranches (step_typed p) (relayRoute_typed K j₁ j₂)

/-- State zero relays: it repeats into itself or enters block state `j + 1`.
Each of the `K + 1` block states runs `p` and repeats into state zero. -/
def relayRows (K : Nat) (q p : Program) (j : Fin (K + 1)) : Fin (K + 2) → Region signature.Instr :=
  Fin.cases (relayRow (K + 1) q 0 j.succ) (fun _ => row (K + 1) p 0)

theorem relayRows_typed (K : Nat) (q p : Program) (j : Fin (K + 1)) (i : Fin (K + 2)) :
    ValueBranches [State] (relayRows K q p j i) [Silmaril.coprod Bit (States (K + 1))] :=
  Fin.cases (motive := fun i =>
      ValueBranches [State] (relayRows K q p j i) [Silmaril.coprod Bit (States (K + 1))])
    (relayRow_typed (K + 1) q 0 j.succ) (fun _ => row_typed (K + 1) p 0) i

/-- The relay table entered at state `i`. -/
def relayFan (K : Nat) (q p : Program) (j : Fin (K + 1)) (i : Fin (K + 2)) : Region signature.Instr :=
  dispatchEntered (K + 1) (relayRows K q p j) i

theorem relayFan_typed (K : Nat) (q p : Program) (j : Fin (K + 1)) (i : Fin (K + 2)) :
    ValueBranches [State] (relayFan K q p j i) [Bit] :=
  dispatchEntered_typed (relayRows_typed K q p j) i

/-! ## The fixed four-reply interpreter -/

/-- Relay routing on values. -/
def relayRouteVal (K : Nat) (j₁ j₂ : Fin (K + 1)) :
    value Bit ⊕ value State → Trace (value Bit ⊕ value (States K))
  | .inl b => pure (.inr (injVal K j₁ (.inl b)))
  | .inr y => pure (.inr (injVal K j₂ y))

local notation "J" => _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli.J (m := Trace)
local notation "M" => _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli.types

noncomputable local instance : InstructionModel J M signature.Instr := instructions model
local instance : RegionTypingCoherent (Φ := signature.Instr) J M := modelCoherent

/-- The dispatcher step of the relay table in that interpreter. -/
noncomputable def relayStepM (K : Nat) (q p : Program) (j : Fin (K + 1)) :
    value (States (K + 1)) → Trace (value Bit ⊕ value (States (K + 1))) :=
  fun v => (denoteSingletonRegion J M (dispatch_typed (K + 1) (relayRows_typed K q p j)).hasType).of v

/-- Complete finite runs of the relay table entered at state `i`. -/
noncomputable def relayObservations (K : Nat) (q p : Program) (j : Fin (K + 1)) (i : Fin (K + 2))
    (g : Bool) : Set (Except Bool (value Bit) × Word) :=
  ((denoteSingletonRegion J M (relayFan_typed K q p j i).hasType).of (Sum.inl (bit g))).outcomes

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable

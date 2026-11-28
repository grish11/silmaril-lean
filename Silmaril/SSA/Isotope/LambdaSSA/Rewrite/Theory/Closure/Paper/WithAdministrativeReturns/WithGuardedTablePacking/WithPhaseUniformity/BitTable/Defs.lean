module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitLoop.Thms

/-! # Multi-state request dispatchers over block-free Bit programs

A table has `K + 1` states. Each state holds the packed loop state of the
one-row slice and is a summand of `phaseType State K`. Its row runs a
written program. The program's return leaves the table. Its repeat jumps to
the row's successor state with the new packed state.

The table step is the literal dispatcher: a case tree on the state sum, with
each row followed by its routing case. One feedback label closes the loop.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.DeBruijn (lift)
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (seqValueBranches caseValueBranches)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory (phaseType)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery (signature)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)

/-- The state sum of a table with `K + 1` states. -/
abbrev States (K : Nat) : Ty Empty := phaseType State K

/-- Tag a packed state with the table state `j`. -/
def injTm : (K : Nat) → Fin (K + 1) → Tm signature.Instr → Tm signature.Instr
  | 0, _, a => a
  | K + 1, j, a => Fin.cases (.inl a) (fun j => .inr (injTm K j a)) j

theorem injTm_typed {Γ : VCtx (Ty Empty)} {a : Tm signature.Instr} (ha : Tm.BranchValue Γ a State) :
    ∀ (K : Nat) (j : Fin (K + 1)), Tm.BranchValue Γ (injTm K j a) (States K)
  | 0, _ => ha
  | K + 1, j => by
    refine Fin.cases ?_ (fun j => ?_) j
    · exact .inl ha
    · exact .inr (injTm_typed ha K j)

theorem ret_typed (K : Nat) :
    ValueBranches [Bit] (.br 0 (.inl (.var 0)) : Region signature.Instr) [Silmaril.coprod Bit (States K)] :=
  .br rfl (.inl (.var rfl))

theorem goto_typed (K : Nat) (j : Fin (K + 1)) :
    ValueBranches [State] (.br 0 (.inr (injTm K j (.var 0))) : Region signature.Instr)
      [Silmaril.coprod Bit (States K)] :=
  .br rfl (.inr (injTm_typed (.var rfl) K j))

/-- Route a row's packed result: a return leaves, a repeat goes to state `j`. -/
def route (K : Nat) (j : Fin (K + 1)) : Region signature.Instr :=
  .case (.var 0) ((Region.br 0 (.inl (.var 0))).renameVars (lift Nat.succ))
    ((Region.br 0 (.inr (injTm K j (.var 0)))).renameVars (lift Nat.succ))

theorem route_typed (K : Nat) (j : Fin (K + 1)) :
    ValueBranches [Silmaril.coprod Bit State] (route K j) [Silmaril.coprod Bit (States K)] :=
  caseValueBranches (ret_typed K) (goto_typed K j)

/-- One row: the written step of `p` followed by its routing case. -/
def row (K : Nat) (p : Program) (j : Fin (K + 1)) : Region signature.Instr :=
  (stepRegion p).lsubst (fun _ => (route K j).renameVars (lift Nat.succ))

theorem row_typed (K : Nat) (p : Program) (j : Fin (K + 1)) :
    ValueBranches [State] (row K p j) [Silmaril.coprod Bit (States K)] :=
  seqValueBranches (step_typed p) (route_typed K j)

/-- Decode the state sum and run the selected row. -/
def dispatch : (K : Nat) → (Fin (K + 1) → Region signature.Instr) → Region signature.Instr
  | 0, rows => rows 0
  | K + 1, rows => .case (.var 0) ((rows 0).renameVars (lift Nat.succ))
      ((dispatch K (fun i => rows i.succ)).renameVars (lift Nat.succ))

theorem dispatch_typed {D : Ty Empty} :
    ∀ (K : Nat) {rows : Fin (K + 1) → Region signature.Instr},
      (∀ i, ValueBranches [State] (rows i) [D]) → ValueBranches [States K] (dispatch K rows) [D]
  | 0, _, h => h 0
  | K + 1, _, h => caseValueBranches (h 0) (dispatch_typed K (fun i => h i.succ))

/-- A written transition table: a program and a successor for each state. -/
structure Table (K : Nat) where
  prog : Fin (K + 1) → Program
  next : Fin (K + 1) → Fin (K + 1)

def Table.step {K : Nat} (t : Table K) : Region signature.Instr :=
  dispatch K (fun i => row K (t.prog i) (t.next i))

theorem Table.step_typed {K : Nat} (t : Table K) :
    ValueBranches [States K] t.step [Silmaril.coprod Bit (States K)] :=
  dispatch_typed K (fun i => row_typed K (t.prog i) (t.next i))

/-- One feedback label around the dispatcher. -/
def Table.loop {K : Nat} (t : Table K) : Region signature.Instr :=
  SyntacticCategory.iterateRegion (States K) t.step

theorem Table.loop_typed {K : Nat} (t : Table K) : ValueBranches [States K] t.loop [Bit] :=
  SyntacticCategory.iterateRegion_valueBranches t.step_typed

theorem entry_typed (K : Nat) (i : Fin (K + 1)) :
    ValueBranches [State] (.br 0 (injTm K i (.var 0)) : Region signature.Instr) [States K] :=
  .br rfl (injTm_typed (.var rfl) K i)

/-- The loop entered at state `i` by a constructor branch. -/
def Table.entered {K : Nat} (t : Table K) (i : Fin (K + 1)) : Region signature.Instr :=
  (Region.br 0 (injTm K i (.var 0))).lsubst (fun _ => t.loop.renameVars (lift Nat.succ))

theorem Table.entered_typed {K : Nat} (t : Table K) (i : Fin (K + 1)) :
    ValueBranches [State] (t.entered i) [Bit] :=
  seqValueBranches (entry_typed K i) t.loop_typed

/-- Every row runs the same written program. The successors are arbitrary. -/
def Table.Single {K : Nat} (t : Table K) (p : Program) : Prop := ∀ i, t.prog i = p

/-- The table with one state that repeats into itself. -/
def Table.one (p : Program) : Table 0 := ⟨fun _ => p, fun _ => 0⟩

/-- Two states. State zero runs `p` and repeats into state one, which runs
`q` and stays there. -/
def Table.handoff (p q : Program) : Table 1 :=
  ⟨fun i => if i = 0 then p else q, fun _ => 1⟩

/-- Two states running `p` that repeat into each other. -/
def Table.swap (p : Program) : Table 1 := ⟨fun _ => p, fun i => if i = 0 then 1 else 0⟩

/-- Three states running `p` in a cycle. -/
def Table.cycle (p : Program) : Table 2 := ⟨fun _ => p, fun i => i + 1⟩

/-! ## The fixed four-reply interpreter -/

open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery (Trace model modelCoherent)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree (Word)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value instructions)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (bit)
open _root_.Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (InstructionModel)

/-- The value of table state `j` holding the packed state `s`. -/
def injVal : (K : Nat) → Fin (K + 1) → value State → value (States K)
  | 0, _, s => s
  | K + 1, j, s => Fin.cases (Sum.inl s) (fun j => Sum.inr (injVal K j s)) j

/-- Routing on values: a return stays a return, a repeat moves to state `j`. -/
def routeVal (K : Nat) (j : Fin (K + 1)) :
    value Bit ⊕ value State → Trace (value Bit ⊕ value (States K))
  | .inl b => pure (.inl b)
  | .inr y => pure (.inr (injVal K j y))

local notation "J" => _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli.J (m := Trace)
local notation "M" => _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli.types

noncomputable local instance : InstructionModel J M signature.Instr := instructions model
local instance : RegionTypingCoherent (Φ := signature.Instr) J M := modelCoherent

/-- The dispatcher step in that interpreter. -/
noncomputable def Table.stepM {K : Nat} (t : Table K) :
    value (States K) → Trace (value Bit ⊕ value (States K)) :=
  fun v => (denoteSingletonRegion J M t.step_typed.hasType).of v

/-- Complete finite runs of the table entered at state `i` with the Bit `g`. -/
noncomputable def Table.observations {K : Nat} (t : Table K) (i : Fin (K + 1)) (g : Bool) :
    Set (Except Bool (value Bit) × Word) :=
  ((denoteSingletonRegion J M (t.entered_typed i).hasType).of (Sum.inl (bit g))).outcomes

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable

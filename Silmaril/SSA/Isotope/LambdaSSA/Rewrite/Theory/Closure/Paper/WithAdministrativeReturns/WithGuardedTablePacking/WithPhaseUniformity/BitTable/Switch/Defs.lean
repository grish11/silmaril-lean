module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Bisimulation.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Relay.Defs

/-! # Request tables whose successor depends on the reply

A switch table has `K + 1` states. The row of a state runs a written
program and then routes its packed result with two literal case splits:

* a returned `true` leaves the table with `true`,
* a returned `false` continues at the successor `next i false`, with
  packed state `false`,
* a repeat continues at the successor `next i true`, with the repeated
  packed state.

When the program is a poll, the reply of its one request picks among the
three: the returning tag with payload `true` terminates, the returning
tag with payload `false` and the repeating tag select two successors,
and the payload of a repeat is the next round's query.

`Switch.walk` follows a word of successor choices. `Switch.minimized`
identifies states that run the same programs along every word.
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

variable {K : Nat}

/-! ## Rows -/

/-- A returned `false`: continue at state `j` with packed state `false`. -/
theorem hold_typed (K : Nat) (j : Fin (K + 1)) :
    ValueBranches [Ty.unit] (.br 0 (.inr (injTm K j (.inl (.inl (.var 0))))) : Region signature.Instr)
      [Silmaril.coprod Bit (States K)] :=
  .br rfl (.inr (injTm_typed (.inl (.inl (.var rfl))) K j))

/-- A returned `true`: leave with `true`. -/
theorem leave_typed (K : Nat) :
    ValueBranches [Ty.unit] (.br 0 (.inl (.inr (.var 0))) : Region signature.Instr)
      [Silmaril.coprod Bit (States K)] :=
  .br rfl (.inl (.inr (.var rfl)))

/-- Split the returned Bit. -/
def bitRoute (K : Nat) (j : Fin (K + 1)) : Region signature.Instr :=
  .case (.var 0) ((Region.br 0 (.inr (injTm K j (.inl (.inl (.var 0)))))).renameVars (lift Nat.succ))
    ((Region.br 0 (.inl (.inr (.var 0)))).renameVars (lift Nat.succ))

theorem bitRoute_typed (K : Nat) (j : Fin (K + 1)) :
    ValueBranches [Bit] (bitRoute K j) [Silmaril.coprod Bit (States K)] :=
  caseValueBranches (hold_typed K j) (leave_typed K)

/-- Route a packed result: a return is split by its Bit, a repeat goes to
state `j₁`. -/
def switchRoute (K : Nat) (j₀ j₁ : Fin (K + 1)) : Region signature.Instr :=
  .case (.var 0) ((bitRoute K j₀).renameVars (lift Nat.succ))
    ((Region.br 0 (.inr (injTm K j₁ (.var 0)))).renameVars (lift Nat.succ))

theorem switchRoute_typed (K : Nat) (j₀ j₁ : Fin (K + 1)) :
    ValueBranches [Silmaril.coprod Bit State] (switchRoute K j₀ j₁) [Silmaril.coprod Bit (States K)] :=
  caseValueBranches (bitRoute_typed K j₀) (goto_typed K j₁)

/-- One row: the written step of `p` followed by its routing cases. -/
def switchRow (K : Nat) (p : Program) (j₀ j₁ : Fin (K + 1)) : Region signature.Instr :=
  (stepRegion p).lsubst (fun _ => (switchRoute K j₀ j₁).renameVars (lift Nat.succ))

theorem switchRow_typed (K : Nat) (p : Program) (j₀ j₁ : Fin (K + 1)) :
    ValueBranches [State] (switchRow K p j₀ j₁) [Silmaril.coprod Bit (States K)] :=
  seqValueBranches (step_typed p) (switchRoute_typed K j₀ j₁)

/-! ## Tables -/

/-- A program for each state and two successors: `next i false` after a
returned `false`, `next i true` after a repeat. -/
structure Switch (K : Nat) where
  prog : Fin (K + 1) → Program
  next : Fin (K + 1) → Bool → Fin (K + 1)

def Switch.rows (t : Switch K) (i : Fin (K + 1)) : Region signature.Instr :=
  switchRow K (t.prog i) (t.next i false) (t.next i true)

theorem Switch.rows_typed (t : Switch K) (i : Fin (K + 1)) :
    ValueBranches [State] (t.rows i) [Silmaril.coprod Bit (States K)] :=
  switchRow_typed K (t.prog i) (t.next i false) (t.next i true)

/-- The literal loop entered at state `i`. -/
def Switch.entered (t : Switch K) (i : Fin (K + 1)) : Region signature.Instr :=
  dispatchEntered K t.rows i

theorem Switch.entered_typed (t : Switch K) (i : Fin (K + 1)) :
    ValueBranches [State] (t.entered i) [Bit] :=
  dispatchEntered_typed t.rows_typed i

/-- A table whose rows are written polls. -/
def Switch.ofPolls (poll : Fin (K + 1) → Poll) (next : Fin (K + 1) → Bool → Fin (K + 1)) : Switch K :=
  ⟨fun i => (poll i).program, next⟩

/-- The disjoint union: the states of `t` in front, those of `s` at the tail. -/
def Switch.append {P : Nat} (t : Switch P) (s : Switch K) : Switch (K + (P + 1)) where
  prog := joinIdx P t.prog s.prog
  next := joinIdx P (fun i b => frontIdx P (t.next i b)) (fun j b => tailIdx P (s.next j b))

/-- The state reached by a word of successor choices. -/
def Switch.walk (t : Switch K) : Fin (K + 1) → List Bool → Fin (K + 1)
  | x, [] => x
  | x, b :: w => t.walk (t.next x b) w

/-- States that run the same program after every word of choices. -/
def Switch.treeSetoid (t : Switch K) : Setoid (Fin (K + 1)) where
  r x y := ∀ w, t.prog (t.walk x w) = t.prog (t.walk y w)
  iseqv := ⟨fun _ _ => rfl, fun h w => (h w).symm, fun h h' w => (h w).trans (h' w)⟩

/-- A chosen state with the same programs along every word. -/
noncomputable def Switch.rep (t : Switch K) (x : Fin (K + 1)) : Fin (K + 1) :=
  (Quotient.mk t.treeSetoid x).out

/-- The same rows, with every successor replaced by its representative. -/
noncomputable def Switch.minimized (t : Switch K) : Switch K := ⟨t.prog, fun x b => t.rep (t.next x b)⟩

/-- A relation that preserves row programs and both successors. -/
structure Switch.Bisimulation {K₁ K₂ : Nat} (t₁ : Switch K₁) (t₂ : Switch K₂)
    (R : Fin (K₁ + 1) → Fin (K₂ + 1) → Prop) : Prop where
  prog : ∀ x y, R x y → t₁.prog x = t₂.prog y
  next : ∀ x y, R x y → ∀ b, R (t₁.next x b) (t₂.next y b)

/-! ## Regression tables -/

/-- Three states. State zero has two different successors: `b` after a
returned `false` and `c` after a repeat. -/
def triNext (i : Fin 3) (r : Bool) : Fin 3 :=
  match i, r with
  | 0, false => 1
  | 0, true => 2
  | 1, _ => 0
  | 2, false => 2
  | 2, true => 0

def triPolls (a b c : Poll) (i : Fin 3) : Poll :=
  match i with
  | 0 => a
  | 1 => b
  | 2 => c

/-- Six states with other wiring. States three and five are further
copies of the `a` state and state four is reached by the word
`false, false, false` only, among the words of length at most three. -/
def wideNext (i : Fin 6) (r : Bool) : Fin 6 :=
  match i, r with
  | 0, false => 1
  | 0, true => 2
  | 1, false => 3
  | 1, true => 5
  | 2, false => 2
  | 2, true => 5
  | 3, false => 4
  | 3, true => 2
  | 4, _ => 0
  | 5, false => 1
  | 5, true => 2

def widePolls (a b c d : Poll) (i : Fin 6) : Poll :=
  match i with
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => a
  | 4 => d
  | 5 => a

/-! ## The fixed four-reply interpreter -/

/-- Routing on values. -/
def switchRouteVal (K : Nat) (j₀ j₁ : Fin (K + 1)) :
    value Bit ⊕ value State → Trace (value Bit ⊕ value (States K))
  | .inl (.inl u) => pure (.inr (injVal K j₀ (.inl (.inl u))))
  | .inl (.inr u) => pure (.inl (.inr u))
  | .inr y => pure (.inr (injVal K j₁ y))

local notation "J" => _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli.J (m := Trace)
local notation "M" => _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli.types

noncomputable local instance : InstructionModel J M signature.Instr := instructions model
local instance : RegionTypingCoherent (Φ := signature.Instr) J M := modelCoherent

/-- The dispatcher step in that interpreter. -/
noncomputable def Switch.stepM (t : Switch K) : value (States K) → Trace (value Bit ⊕ value (States K)) :=
  fun v => (denoteSingletonRegion J M (dispatch_typed K t.rows_typed).hasType).of v

/-- Complete finite runs of the table entered at state `i` with the Bit `g`. -/
noncomputable def Switch.observations (t : Switch K) (i : Fin (K + 1)) (g : Bool) :
    Set (Except Bool (value Bit) × Word) :=
  ((denoteSingletonRegion J M (t.entered_typed i).hasType).of (Sum.inl (bit g))).outcomes

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable

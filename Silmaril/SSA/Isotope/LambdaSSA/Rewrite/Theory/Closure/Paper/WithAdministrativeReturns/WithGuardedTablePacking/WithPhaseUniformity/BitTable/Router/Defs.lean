module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Switch.Defs

/-! # Request tables with arbitrary routing of the packed result

A router row runs a written program and then inspects its whole packed
result with literal case splits. The result is a return or a repeat,
carrying one Bit. Each of the four values has its own action: return a
chosen Bit, or continue at a chosen state with a chosen next query.

When the program is the poll with a given label that returns on the left
reply, the four packed results are the four replies of its one request:
the reply `(tag, pl)` gives the result with flag `tag` and bit `pl`.
So `act i tag pl` is the action of state `i` on that reply.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.DeBruijn (lift)
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (seqValueBranches caseValueBranches)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery (signature Trace model modelCoherent)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree (Word event)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value instructions)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit bit)
open _root_.Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (InstructionModel)

variable {K : Nat}

/-! ## Actions -/

/-- What a row does with one packed result. -/
inductive Act (K : Nat) where
  /-- Leave the table with the Bit `c`. -/
  | ret (c : Bool)
  /-- Continue at state `j` with the query `q`. -/
  | go (j : Fin (K + 1)) (q : Bool)

/-- Rename the target state. -/
def Act.map {K' : Nat} (f : Fin (K + 1) → Fin (K' + 1)) : Act K → Act K'
  | .ret c => .ret c
  | .go j q => .go (f j) q

/-- Two actions agree up to a relation on their target states. -/
def Act.Rel {K₁ K₂ : Nat} (R : Fin (K₁ + 1) → Fin (K₂ + 1) → Prop) : Act K₁ → Act K₂ → Prop
  | .ret c, .ret c' => c = c'
  | .go j q, .go j' q' => q = q' ∧ R j j'
  | _, _ => False

instance Act.decRel {K₁ K₂ : Nat} (R : Fin (K₁ + 1) → Fin (K₂ + 1) → Prop) [∀ x y, Decidable (R x y)] :
    ∀ (a : Act K₁) (a' : Act K₂), Decidable (Act.Rel R a a')
  | .ret c, .ret c' => inferInstanceAs (Decidable (c = c'))
  | .go j q, .go j' q' => inferInstanceAs (Decidable (q = q' ∧ R j j'))
  | .ret _, .go _ _ => isFalse id
  | .go _ _, .ret _ => isFalse id

/-! ## Rows -/

/-- A Bit constant, built from the unit bound by the innermost split. -/
def bitTm (c : Bool) : Tm signature.Instr :=
  match c with
  | false => .inl (.var 0)
  | true => .inr (.var 0)

theorem bitTm_typed (c : Bool) : Tm.BranchValue [Ty.unit] (bitTm c) Bit := by
  cases c
  · exact .inl (.var rfl)
  · exact .inr (.var rfl)

def actTm (K : Nat) : Act K → Tm signature.Instr
  | .ret c => .inl (bitTm c)
  | .go j q => .inr (injTm K j (.inl (bitTm q)))

theorem actTm_typed (K : Nat) (a : Act K) :
    Tm.BranchValue [Ty.unit] (actTm K a) (Silmaril.coprod Bit (States K)) := by
  cases a
  · exact .inl (bitTm_typed _)
  · exact .inr (injTm_typed (.inl (bitTm_typed _)) K _)

theorem act_typed (K : Nat) (a : Act K) :
    ValueBranches [Ty.unit] (.br 0 (actTm K a) : Region signature.Instr) [Silmaril.coprod Bit (States K)] :=
  .br rfl (actTm_typed K a)

/-- Split a Bit and act on each value. -/
def bitSplit (K : Nat) (a₀ a₁ : Act K) : Region signature.Instr :=
  .case (.var 0) ((Region.br 0 (actTm K a₀)).renameVars (lift Nat.succ))
    ((Region.br 0 (actTm K a₁)).renameVars (lift Nat.succ))

theorem bitSplit_typed (K : Nat) (a₀ a₁ : Act K) :
    ValueBranches [Bit] (bitSplit K a₀ a₁) [Silmaril.coprod Bit (States K)] :=
  caseValueBranches (act_typed K a₀) (act_typed K a₁)

/-- The empty summand of the packed state. It is never taken. -/
theorem dead_typed (K : Nat) :
    ValueBranches [Silmaril.empty] (.br 0 (.inl (.inl .unit)) : Region signature.Instr)
      [Silmaril.coprod Bit (States K)] :=
  .br rfl (.inl (.inl .unit))

/-- Split a packed state. -/
def stateSplit (K : Nat) (a₀ a₁ : Act K) : Region signature.Instr :=
  .case (.var 0) ((bitSplit K a₀ a₁).renameVars (lift Nat.succ))
    ((Region.br 0 (.inl (.inl .unit))).renameVars (lift Nat.succ))

theorem stateSplit_typed (K : Nat) (a₀ a₁ : Act K) :
    ValueBranches [State] (stateSplit K a₀ a₁) [Silmaril.coprod Bit (States K)] :=
  caseValueBranches (bitSplit_typed K a₀ a₁) (dead_typed K)

/-- Route all four packed results. `a false b` acts on a returned `b`
and `a true b` on a repeated `b`. -/
def routerRoute (K : Nat) (a : Bool → Bool → Act K) : Region signature.Instr :=
  .case (.var 0) ((bitSplit K (a false false) (a false true)).renameVars (lift Nat.succ))
    ((stateSplit K (a true false) (a true true)).renameVars (lift Nat.succ))

theorem routerRoute_typed (K : Nat) (a : Bool → Bool → Act K) :
    ValueBranches [Silmaril.coprod Bit State] (routerRoute K a) [Silmaril.coprod Bit (States K)] :=
  caseValueBranches (bitSplit_typed K (a false false) (a false true))
    (stateSplit_typed K (a true false) (a true true))

def routerRow (K : Nat) (p : Program) (a : Bool → Bool → Act K) : Region signature.Instr :=
  (stepRegion p).lsubst (fun _ => (routerRoute K a).renameVars (lift Nat.succ))

theorem routerRow_typed (K : Nat) (p : Program) (a : Bool → Bool → Act K) :
    ValueBranches [State] (routerRow K p a) [Silmaril.coprod Bit (States K)] :=
  seqValueBranches (step_typed p) (routerRoute_typed K a)

/-! ## Tables -/

/-- A program and four actions for each state. -/
structure Router (K : Nat) where
  prog : Fin (K + 1) → Program
  act : Fin (K + 1) → Bool → Bool → Act K

def Router.rows (t : Router K) (i : Fin (K + 1)) : Region signature.Instr :=
  routerRow K (t.prog i) (t.act i)

theorem Router.rows_typed (t : Router K) (i : Fin (K + 1)) :
    ValueBranches [State] (t.rows i) [Silmaril.coprod Bit (States K)] :=
  routerRow_typed K (t.prog i) (t.act i)

/-- The literal loop entered at state `i`. -/
def Router.entered (t : Router K) (i : Fin (K + 1)) : Region signature.Instr :=
  dispatchEntered K t.rows i

theorem Router.entered_typed (t : Router K) (i : Fin (K + 1)) :
    ValueBranches [State] (t.entered i) [Bit] :=
  dispatchEntered_typed t.rows_typed i

/-- The poll with label `l` that returns on the left reply. -/
def labelPoll (l : Bool) : Poll := ⟨l, false⟩

/-- A table of one request per round: `act i tag pl` is the action of
state `i` on the reply `(tag, pl)`. -/
def Router.ofLabels (label : Fin (K + 1) → Bool) (act : Fin (K + 1) → Bool → Bool → Act K) : Router K :=
  ⟨fun i => (labelPoll (label i)).program, act⟩

/-- The disjoint union: the states of `t` in front, those of `s` at the tail. -/
def Router.append {P : Nat} (t : Router P) (s : Router K) : Router (K + (P + 1)) where
  prog := joinIdx P t.prog s.prog
  act := joinIdx P (fun i f b => (t.act i f b).map (frontIdx P)) (fun j f b => (s.act j f b).map (tailIdx P))

/-- A relation that preserves row programs and all four actions. -/
structure Router.Bisimulation {K₁ K₂ : Nat} (t₁ : Router K₁) (t₂ : Router K₂)
    (R : Fin (K₁ + 1) → Fin (K₂ + 1) → Prop) : Prop where
  prog : ∀ x y, R x y → t₁.prog x = t₂.prog y
  act : ∀ x y, R x y → ∀ f b, Act.Rel R (t₁.act x f b) (t₂.act y f b)

/-- Some bisimulation relates the two states. -/
def Router.Bisimilar {K₁ K₂ : Nat} (t₁ : Router K₁) (t₂ : Router K₂) (x : Fin (K₁ + 1))
    (y : Fin (K₂ + 1)) : Prop :=
  ∃ R, Router.Bisimulation t₁ t₂ R ∧ R x y

/-! ## Regression tables -/

/-- Four states. State zero returns on one reply and sends the other
three to three different states with chosen queries. -/
def hubAct (i : Fin 4) (tag pl : Bool) : Act 3 :=
  match i, tag, pl with
  | 0, false, false => .ret false
  | 0, false, true => .go 1 false
  | 0, true, false => .go 2 true
  | 0, true, true => .go 3 false
  | 1, _, pl => .ret pl
  | 2, _, pl => .ret (!pl)
  | 3, false, _ => .ret false
  | 3, true, pl => .go 0 pl

def hubLabel (a b c d : Bool) (i : Fin 4) : Bool :=
  match i with
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => d

/-- Six states with other wiring: states four and five are further copies
of states zero and three. State four returns `x` on its first reply. -/
def spreadAct (x : Bool) (i : Fin 6) (tag pl : Bool) : Act 5 :=
  match i, tag, pl with
  | 0, false, false => .ret false
  | 0, false, true => .go 1 false
  | 0, true, false => .go 2 true
  | 0, true, true => .go 3 false
  | 1, _, pl => .ret pl
  | 2, _, pl => .ret (!pl)
  | 3, false, _ => .ret false
  | 3, true, pl => .go 4 pl
  | 4, false, false => .ret x
  | 4, false, true => .go 1 false
  | 4, true, false => .go 2 true
  | 4, true, true => .go 5 false
  | 5, false, _ => .ret false
  | 5, true, pl => .go 0 pl

def spreadLabel (a b c d : Bool) (i : Fin 6) : Bool :=
  match i with
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => d
  | 4 => a
  | 5 => d

/-- Three requests: to state three, back to a copy of state zero, and
the first reply there. -/
abbrev hubWord (a d g : Bool) : Word :=
  FreeMonoid.of (event a g (true, true)) *
    (FreeMonoid.of (event d false (true, false)) * (FreeMonoid.of (event a false (false, false)) * 1))

/-- One state whose every reply repeats into itself. -/
def deadAct (_ : Fin 1) (_ pl : Bool) : Act 0 := .go 0 pl

/-! ## The fixed four-reply interpreter -/

/-- The value of an action. -/
def actVal (K : Nat) : Act K → value Bit ⊕ value (States K)
  | .ret c => .inl (bit c)
  | .go j q => .inr (injVal K j (.inl (bit q)))

/-- Routing on values. -/
def routerRouteVal (K : Nat) (a : Bool → Bool → Act K) :
    value Bit ⊕ value State → Trace (value Bit ⊕ value (States K))
  | .inl (.inl _) => pure (actVal K (a false false))
  | .inl (.inr _) => pure (actVal K (a false true))
  | .inr (.inl (.inl _)) => pure (actVal K (a true false))
  | .inr (.inl (.inr _)) => pure (actVal K (a true true))
  | .inr (.inr e) => e.elim

local notation "J" => _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli.J (m := Trace)
local notation "M" => _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli.types

noncomputable local instance routerDefInstructions : InstructionModel J M signature.Instr := instructions model
local instance routerDefCoherent : RegionTypingCoherent (Φ := signature.Instr) J M := modelCoherent

/-- The dispatcher step in that interpreter. -/
noncomputable def Router.stepM (t : Router K) : value (States K) → Trace (value Bit ⊕ value (States K)) :=
  fun v => (denoteSingletonRegion J M (dispatch_typed K t.rows_typed).hasType).of v

/-- Complete finite runs of the table entered at state `i` with the Bit `g`. -/
noncomputable def Router.observations (t : Router K) (i : Fin (K + 1)) (g : Bool) :
    Set (Except Bool (value Bit) × Word) :=
  ((denoteSingletonRegion J M (t.entered_typed i).hasType).of (Sum.inl (bit g))).outcomes

/-- What follows the first event of a complete run, by the action taken:
nothing after a return, a complete run of the target after a jump. -/
def Router.Cont (t : Router K) : Act K → Except Bool (value Bit) → Word → Prop
  | .ret c, r, v => r = .ok (bit c) ∧ v = 1
  | .go j q, r, v => (r, v) ∈ t.observations j q

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable

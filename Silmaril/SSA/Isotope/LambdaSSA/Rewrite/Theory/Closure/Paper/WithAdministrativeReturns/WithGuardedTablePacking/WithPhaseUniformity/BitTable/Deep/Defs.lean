module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Router.Defs

/-! # Rows with a second request inlined at a reply

A deep table has one continuation: a labelled request with four plain
actions. In a deep row each of the four replies either takes a plain
action or continues at once with that second request, sent with a chosen
query. So one round has one or two requests, and whether the second one
is sent, and with which query, depends on the first reply.

`Deep.expand` puts the continuation in a state of its own, in front, and
replaces each inlined occurrence by a jump to it.
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

/-- What a deep row does with one reply. -/
inductive Leaf (K : Nat) where
  /-- A plain action. -/
  | act (a : Act K)
  /-- Send the second request at once, with the query `q`. -/
  | ask (q : Bool)

/-- In the expanded table an inlined request is a jump to the new state. -/
def Leaf.expand : Leaf K → Act (K + 1)
  | .act a => a.map Fin.succ
  | .ask q => .go 0 q

/-- A constant packed state. -/
theorem const_typed (q : Bool) :
    ValueBranches [Ty.unit] (.br 0 (.inl (bitTm q)) : Region signature.Instr) [State] :=
  .br rfl (.inl (bitTm_typed q))

/-- The second request, sent with the query `q`. -/
def inlineRegion (K : Nat) (pc : Program) (ac : Bool → Bool → Act K) (q : Bool) : Region signature.Instr :=
  (Region.br 0 (.inl (bitTm q))).lsubst (fun _ => (routerRow K pc ac).renameVars (lift Nat.succ))

theorem inline_typed (K : Nat) (pc : Program) (ac : Bool → Bool → Act K) (q : Bool) :
    ValueBranches [Ty.unit] (inlineRegion K pc ac q) [Silmaril.coprod Bit (States K)] :=
  seqValueBranches (const_typed q) (routerRow_typed K pc ac)

def leafRegion (K : Nat) (pc : Program) (ac : Bool → Bool → Act K) : Leaf K → Region signature.Instr
  | .act a => .br 0 (actTm K a)
  | .ask q => inlineRegion K pc ac q

theorem leaf_typed (K : Nat) (pc : Program) (ac : Bool → Bool → Act K) (x : Leaf K) :
    ValueBranches [Ty.unit] (leafRegion K pc ac x) [Silmaril.coprod Bit (States K)] := by
  cases x
  · exact act_typed K _
  · exact inline_typed K pc ac _

def leafSplit (K : Nat) (pc : Program) (ac : Bool → Bool → Act K) (x₀ x₁ : Leaf K) : Region signature.Instr :=
  .case (.var 0) ((leafRegion K pc ac x₀).renameVars (lift Nat.succ))
    ((leafRegion K pc ac x₁).renameVars (lift Nat.succ))

theorem leafSplit_typed (K : Nat) (pc : Program) (ac : Bool → Bool → Act K) (x₀ x₁ : Leaf K) :
    ValueBranches [Bit] (leafSplit K pc ac x₀ x₁) [Silmaril.coprod Bit (States K)] :=
  caseValueBranches (leaf_typed K pc ac x₀) (leaf_typed K pc ac x₁)

def leafState (K : Nat) (pc : Program) (ac : Bool → Bool → Act K) (x₀ x₁ : Leaf K) : Region signature.Instr :=
  .case (.var 0) ((leafSplit K pc ac x₀ x₁).renameVars (lift Nat.succ))
    ((Region.br 0 (.inl (.inl .unit))).renameVars (lift Nat.succ))

theorem leafState_typed (K : Nat) (pc : Program) (ac : Bool → Bool → Act K) (x₀ x₁ : Leaf K) :
    ValueBranches [State] (leafState K pc ac x₀ x₁) [Silmaril.coprod Bit (States K)] :=
  caseValueBranches (leafSplit_typed K pc ac x₀ x₁) (dead_typed K)

def deepRoute (K : Nat) (pc : Program) (ac : Bool → Bool → Act K) (b : Bool → Bool → Leaf K) :
    Region signature.Instr :=
  .case (.var 0) ((leafSplit K pc ac (b false false) (b false true)).renameVars (lift Nat.succ))
    ((leafState K pc ac (b true false) (b true true)).renameVars (lift Nat.succ))

theorem deepRoute_typed (K : Nat) (pc : Program) (ac : Bool → Bool → Act K) (b : Bool → Bool → Leaf K) :
    ValueBranches [Silmaril.coprod Bit State] (deepRoute K pc ac b) [Silmaril.coprod Bit (States K)] :=
  caseValueBranches (leafSplit_typed K pc ac (b false false) (b false true))
    (leafState_typed K pc ac (b true false) (b true true))

def deepRow (K : Nat) (p pc : Program) (ac : Bool → Bool → Act K) (b : Bool → Bool → Leaf K) :
    Region signature.Instr :=
  (stepRegion p).lsubst (fun _ => (deepRoute K pc ac b).renameVars (lift Nat.succ))

theorem deepRow_typed (K : Nat) (p pc : Program) (ac : Bool → Bool → Act K) (b : Bool → Bool → Leaf K) :
    ValueBranches [State] (deepRow K p pc ac b) [Silmaril.coprod Bit (States K)] :=
  seqValueBranches (step_typed p) (deepRoute_typed K pc ac b)

/-- A first program and four leaves for each state, and one continuation. -/
structure Deep (K : Nat) where
  prog : Fin (K + 1) → Program
  leaf : Fin (K + 1) → Bool → Bool → Leaf K
  cont : Program
  contAct : Bool → Bool → Act K

def Deep.rows (t : Deep K) (i : Fin (K + 1)) : Region signature.Instr :=
  deepRow K (t.prog i) t.cont t.contAct (t.leaf i)

theorem Deep.rows_typed (t : Deep K) (i : Fin (K + 1)) :
    ValueBranches [State] (t.rows i) [Silmaril.coprod Bit (States K)] :=
  deepRow_typed K (t.prog i) t.cont t.contAct (t.leaf i)

/-- The literal loop entered at state `i`. -/
def Deep.entered (t : Deep K) (i : Fin (K + 1)) : Region signature.Instr :=
  dispatchEntered K t.rows i

theorem Deep.entered_typed (t : Deep K) (i : Fin (K + 1)) : ValueBranches [State] (t.entered i) [Bit] :=
  dispatchEntered_typed t.rows_typed i

/-- The router table with the continuation as state zero. -/
def Deep.expand (t : Deep K) : Router (K + 1) where
  prog := Fin.cases t.cont t.prog
  act := Fin.cases (fun x b => (t.contAct x b).map Fin.succ) (fun i x b => (t.leaf i x b).expand)

/-- A deep table of labelled requests. -/
def Deep.ofLabels (label : Fin (K + 1) → Bool) (leaf : Fin (K + 1) → Bool → Bool → Leaf K) (lc : Bool)
    (ac : Bool → Bool → Act K) : Deep K :=
  ⟨fun i => (labelPoll (label i)).program, leaf, (labelPoll lc).program, ac⟩

/-- The labels of its expansion. -/
def deepLabel (label : Fin (K + 1) → Bool) (lc : Bool) : Fin (K + 2) → Bool := Fin.cases lc label

/-- The actions of its expansion. -/
def deepAct (leaf : Fin (K + 1) → Bool → Bool → Leaf K) (ac : Bool → Bool → Act K) :
    Fin (K + 2) → Bool → Bool → Act (K + 1) :=
  Fin.cases (fun x b => (ac x b).map Fin.succ) (fun i x b => (leaf i x b).expand)

/-! ## Regression tables -/

/-- One state. Its first reply returns, two replies send the second
request with the reply's payload as query, and the last repeats. -/
def duoLeaf (_ : Fin 1) (tag pl : Bool) : Leaf 0 :=
  match tag, pl with
  | false, false => .act (.ret false)
  | false, true => .ask true
  | true, false => .ask false
  | true, true => .act (.go 0 true)

/-- The second request returns its payload or goes back with it. -/
def duoCont (tag pl : Bool) : Act 0 :=
  match tag with
  | false => .ret pl
  | true => .go 0 pl

/-- Explicit rows with other boundaries: the second request has one state
for each query. -/
def splitAct (i : Fin 3) (tag pl : Bool) : Act 2 :=
  match i, tag, pl with
  | 0, false, false => .ret false
  | 0, false, true => .go 1 true
  | 0, true, false => .go 2 false
  | 0, true, true => .go 0 true
  | 1, false, pl => .ret pl
  | 1, true, pl => .go 0 pl
  | 2, false, pl => .ret pl
  | 2, true, pl => .go 0 pl

def splitLabel (a c : Bool) (i : Fin 3) : Bool :=
  match i with
  | 0 => a
  | 1 => c
  | 2 => c

/-- A deep row that never returns: every reply sends the second request. -/
def loopLeaf (_ : Fin 1) (_ pl : Bool) : Leaf 0 := .ask pl

/-- And the second request always goes back. -/
def loopCont (_ pl : Bool) : Act 0 := .go 0 pl

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable

module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Deep.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Router.Prefix.Defs

/-! # Literal request trees as rows

A `Tree` says what happens at a reply: a plain action, or a further
request sent at once with a chosen query, whose four replies are trees
again. A row of a tree table is a first request with a tree at each
reply. Its region is the literal nesting: every inner request is written
inside the reply branch that sends it.

`TreeTable.nest n` writes the first `n` states of a table inside the
rows that jump to them, one state at a time from state zero. Applied to a
router table whose first `n` rows only jump forward it gives literal
request trees over the remaining states.
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

/-! ## Rows with arbitrary regions at the four results -/

def pairSplit (r₀ r₁ : Region signature.Instr) : Region signature.Instr :=
  .case (.var 0) (r₀.renameVars (lift Nat.succ)) (r₁.renameVars (lift Nat.succ))

/-- Route the four packed results to four regions. -/
def genRoute (r : Bool → Bool → Region signature.Instr) : Region signature.Instr :=
  .case (.var 0) ((pairSplit (r false false) (r false true)).renameVars (lift Nat.succ))
    ((Region.case (.var 0) ((pairSplit (r true false) (r true true)).renameVars (lift Nat.succ))
      ((Region.br 0 (.inl (.inl .unit))).renameVars (lift Nat.succ))).renameVars (lift Nat.succ))

theorem genRoute_typed {r : Bool → Bool → Region signature.Instr}
    (h : ∀ x y, ValueBranches [Ty.unit] (r x y) [Silmaril.coprod Bit (States K)]) :
    ValueBranches [Silmaril.coprod Bit State] (genRoute r) [Silmaril.coprod Bit (States K)] :=
  caseValueBranches (caseValueBranches (h false false) (h false true))
    (caseValueBranches (caseValueBranches (h true false) (h true true)) (dead_typed K))

def genRow (p : Program) (r : Bool → Bool → Region signature.Instr) : Region signature.Instr :=
  (stepRegion p).lsubst (fun _ => (genRoute r).renameVars (lift Nat.succ))

theorem genRow_typed (p : Program) {r : Bool → Bool → Region signature.Instr}
    (h : ∀ x y, ValueBranches [Ty.unit] (r x y) [Silmaril.coprod Bit (States K)]) :
    ValueBranches [State] (genRow p r) [Silmaril.coprod Bit (States K)] :=
  seqValueBranches (step_typed p) (genRoute_typed h)

/-! ## Trees -/

/-- What happens at a reply. -/
inductive Tree (K : Nat) where
  /-- A plain action. -/
  | leaf (a : Act K)
  /-- Send the request of `p` at once with the query `q`. -/
  | ask (q : Bool) (p : Program) (kids : Bool → Bool → Tree K)

def treeRegion (K : Nat) : Tree K → Region signature.Instr
  | .leaf a => .br 0 (actTm K a)
  | .ask q p kids => (Region.br 0 (.inl (bitTm q))).lsubst
      (fun _ => (genRow p fun x y => treeRegion K (kids x y)).renameVars (lift Nat.succ))

theorem treeRegion_typed (K : Nat) :
    ∀ t : Tree K, ValueBranches [Ty.unit] (treeRegion K t) [Silmaril.coprod Bit (States K)]
  | .leaf a => act_typed K a
  | .ask q p kids => seqValueBranches (const_typed q)
      (genRow_typed p fun x y => treeRegion_typed K (kids x y))

/-- Write the row of state zero in place of each jump to it, and rename
the other targets. -/
def Tree.inline (p₀ : Program) (k₀ : Bool → Bool → Tree K) : Tree (K + 1) → Tree K
  | .leaf (.ret c) => .leaf (.ret c)
  | .leaf (.go j q) => Fin.cases (.ask q p₀ k₀) (fun j' => .leaf (.go j' q)) j
  | .ask q p kids => .ask q p fun x y => (kids x y).inline p₀ k₀

/-- Every jump goes to a state strictly above `m`. -/
def Tree.Above (m : Nat) : Tree K → Prop
  | .leaf (.ret _) => True
  | .leaf (.go j _) => m < j.val
  | .ask _ _ kids => ∀ x y, (kids x y).Above m

/-- The largest number of further requests along a path of the tree. -/
def Tree.depth : Tree K → Nat
  | .leaf _ => 0
  | .ask _ _ kids => 1 + max (max (kids false false).depth (kids false true).depth)
      (max (kids true false).depth (kids true true).depth)

/-! ## Tables -/

/-- A first program and four trees for each state. -/
structure TreeTable (K : Nat) where
  prog : Fin (K + 1) → Program
  kids : Fin (K + 1) → Bool → Bool → Tree K

def TreeTable.rows (t : TreeTable K) (i : Fin (K + 1)) : Region signature.Instr :=
  genRow (t.prog i) fun x y => treeRegion K (t.kids i x y)

theorem TreeTable.rows_typed (t : TreeTable K) (i : Fin (K + 1)) :
    ValueBranches [State] (t.rows i) [Silmaril.coprod Bit (States K)] :=
  genRow_typed (t.prog i) fun x y => treeRegion_typed K (t.kids i x y)

/-- The literal loop entered at state `i`. -/
def TreeTable.entered (t : TreeTable K) (i : Fin (K + 1)) : Region signature.Instr :=
  dispatchEntered K t.rows i

theorem TreeTable.entered_typed (t : TreeTable K) (i : Fin (K + 1)) :
    ValueBranches [State] (t.entered i) [Bit] :=
  dispatchEntered_typed t.rows_typed i

/-- A router table is a tree table whose trees are leaves. Its rows and
entered loops are the same regions. -/
def Router.toTrees (t : Router K) : TreeTable K := ⟨t.prog, fun i x y => .leaf (t.act i x y)⟩

/-- The row of state zero with its targets renamed. It is only used when
that row does not jump to state zero. -/
def TreeTable.frontKids (t : TreeTable (K + 1)) (x y : Bool) : Tree K :=
  (t.kids 0 x y).inline (t.prog 0) fun _ _ => .leaf (.ret false)

/-- Write state zero inside the rows that jump to it. -/
def TreeTable.inlineFront (t : TreeTable (K + 1)) : TreeTable K :=
  ⟨fun i => t.prog i.succ, fun i x y => (t.kids i.succ x y).inline (t.prog 0) t.frontKids⟩

/-- Write the first `n` states inside the rows that jump to them. -/
def TreeTable.nest : (n : Nat) → TreeTable (K + n) → TreeTable K
  | 0, t => t
  | n + 1, t => TreeTable.nest n t.inlineFront

/-- State `i` of the remaining states, in the table with `n` states in front. -/
def shiftN : (n : Nat) → Fin (K + 1) → Fin (K + n + 1)
  | 0, i => i
  | n + 1, i => (shiftN n i).succ

/-- The first `n` rows only jump forward. -/
def Router.Forward (n : Nat) (t : Router K) : Prop :=
  ∀ k : Fin (K + 1), k.val < n → ∀ x y, (Tree.leaf (t.act k x y)).Above k.val

/-! ## Regression tables -/

/-- Three continuations `A`, `B`, `C` in front of one state `O`.
`O` returns, sends `A` with its payload as query, sends `B`, or repeats.
`A` sends `B` or returns. `B` sends `C` or goes back. `C` returns or goes
back. So a round has up to four requests. -/
def chainedAct (i : Fin 4) (tag pl : Bool) : Act 3 :=
  match i, tag, pl with
  | 0, false, pl => .go 1 pl
  | 0, true, pl => .ret pl
  | 1, false, pl => .go 2 pl
  | 1, true, pl => .go 3 pl
  | 2, false, pl => .ret (!pl)
  | 2, true, pl => .go 3 pl
  | 3, false, false => .ret false
  | 3, false, true => .go 0 true
  | 3, true, false => .go 1 false
  | 3, true, true => .go 3 true

def chainedLabel (a b c o : Bool) (i : Fin 4) : Bool :=
  match i with
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => o

/-- Two continuations in front of one state, none of which returns:
`O` sends `A`, `A` sends `B`, `B` goes back. -/
def spiralAct (i : Fin 3) (_ pl : Bool) : Act 2 :=
  match i with
  | 0 => .go 1 pl
  | 1 => .go 2 pl
  | 2 => .go 0 pl

def spiralLabel (a b o : Bool) (i : Fin 3) : Bool :=
  match i with
  | 0 => a
  | 1 => b
  | 2 => o

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable

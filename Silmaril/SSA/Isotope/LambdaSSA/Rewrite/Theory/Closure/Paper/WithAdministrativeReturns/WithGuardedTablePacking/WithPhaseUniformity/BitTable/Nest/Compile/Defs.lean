module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Nest.Defs

/-! # From any tree table to a router table

`TreeTable.outlineAt` moves one request that stands directly at a reply
of a row into a new state zero and leaves a jump in its place. The other
states keep their order behind it. Repeating this until no inner request
is left gives a router table.

`LTree` and `LTable` are the trees and tables whose requests are all
labelled requests.
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

/-- Rename every target to its successor. -/
def Tree.shift : Tree K → Tree (K + 1)
  | .leaf a => .leaf (a.map Fin.succ)
  | .ask q p kids => .ask q p fun x y => (kids x y).shift

/-- The number of requests in a tree. -/
def Tree.size : Tree K → Nat
  | .leaf _ => 0
  | .ask _ _ kids => 1 + ((kids false false).size + (kids false true).size +
      ((kids true false).size + (kids true true).size))

/-- Every request of the tree runs a program in `Q`. -/
def Tree.All (Q : Program → Prop) : Tree K → Prop
  | .leaf _ => True
  | .ask _ p kids => Q p ∧ ∀ x y, (kids x y).All Q

def TreeTable.All (Q : Program → Prop) (t : TreeTable K) : Prop :=
  (∀ j, Q (t.prog j)) ∧ ∀ j x y, (t.kids j x y).All Q

/-- A sum over `Fin n`. -/
def finSum : (n : Nat) → (Fin n → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => f 0 + finSum n fun j => f j.succ

def TreeTable.rowAsks (t : TreeTable K) (j : Fin (K + 1)) : Nat :=
  (t.kids j false false).size + (t.kids j false true).size +
    ((t.kids j true false).size + (t.kids j true true).size)

/-- The number of inner requests of a table. -/
def TreeTable.asks (t : TreeTable K) : Nat := finSum (K + 1) t.rowAsks

/-- Move the request `ask q p ks` at reply `(x, y)` of row `i` into a new
state zero. -/
def TreeTable.outlineAt (t : TreeTable K) (i : Fin (K + 1)) (x y q : Bool) (p : Program)
    (ks : Bool → Bool → Tree K) : TreeTable (K + 1) where
  prog := Fin.cases p t.prog
  kids := Fin.cases (fun x' y' => (ks x' y').shift)
    (fun j x' y' => if j = i ∧ x' = x ∧ y' = y then .leaf (.go 0 q) else (t.kids j x' y').shift)

/-- The action of a leaf. -/
def Tree.leafAct : Tree K → Act K
  | .leaf a => a
  | .ask _ _ _ => .ret false

/-- The router table of a table without inner requests. -/
def TreeTable.flatten (t : TreeTable K) : Router K := ⟨t.prog, fun j x y => (t.kids j x y).leafAct⟩

/-- A program that is one labelled request. -/
def IsLabel (p : Program) : Prop := ∃ l, p = (labelPoll l).program

/-! ## Trees of labelled requests -/

inductive LTree (K : Nat) where
  | leaf (a : Act K)
  | ask (q l : Bool) (kids : Bool → Bool → LTree K)

def LTree.toTree : LTree K → Tree K
  | .leaf a => .leaf a
  | .ask q l kids => .ask q (labelPoll l).program fun x y => (kids x y).toTree

/-- A first label and four trees of labelled requests for each state. -/
structure LTable (K : Nat) where
  label : Fin (K + 1) → Bool
  kids : Fin (K + 1) → Bool → Bool → LTree K

def LTable.toTable (t : LTable K) : TreeTable K :=
  ⟨fun j => (labelPoll (t.label j)).program, fun j x y => (t.kids j x y).toTree⟩

/-- The literal loop entered at state `i`. -/
def LTable.entered (t : LTable K) (i : Fin (K + 1)) : Region signature.Instr := t.toTable.entered i

theorem LTable.entered_typed (t : LTable K) (i : Fin (K + 1)) : ValueBranches [State] (t.entered i) [Bit] :=
  t.toTable.entered_typed i

/-! ## Regression tables -/

/-- A second request: it returns its payload or goes to the last state. -/
def contKids (x y : Bool) : LTree 1 :=
  match x with
  | false => .leaf (.ret y)
  | true => .leaf (.go 1 y)

def cont (a q : Bool) : LTree 1 := .ask q a contKids

/-- Two rows written as trees. Row zero sends the second request after
three of its replies, with the reply payload or `false` as query. Row one
never returns. -/
def sourceKids (a : Bool) (j : Fin 2) (x y : Bool) : LTree 1 :=
  match j, x, y with
  | 0, false, y => cont a y
  | 0, true, false => .leaf (.ret false)
  | 0, true, true => cont a false
  | 1, _, y => .leaf (.go 1 y)

def sourceLabel (o d : Bool) (j : Fin 2) : Bool :=
  match j with
  | 0 => o
  | 1 => d

def sourceTable (a o d : Bool) : LTable 1 := ⟨sourceLabel o d, sourceKids a⟩

/-- The same table with the second request as an explicit state zero. -/
def explicitAct (j : Fin 3) (x y : Bool) : Act 2 :=
  match j, x, y with
  | 0, false, y => .ret y
  | 0, true, y => .go 2 y
  | 1, false, y => .go 0 y
  | 1, true, false => .ret false
  | 1, true, true => .go 0 false
  | 2, _, y => .go 2 y

def explicitLabel (a o d : Bool) (j : Fin 3) : Bool :=
  match j with
  | 0 => a
  | 1 => o
  | 2 => d

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable

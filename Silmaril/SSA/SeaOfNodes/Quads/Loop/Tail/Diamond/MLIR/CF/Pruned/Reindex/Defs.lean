module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Comparison.Equation.Defs
public import Mathlib.Logic.Equiv.Defs

/-! # Typed entry permutations of the checked pure quad diamond -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex

open SeaOfNodes.Diamond (ValueSort dataPorts)
open SeaOfNodes.Loop.MLIR.CF (Op TargetOp evalOp)
open SeaOfNodes.MLIR.Lowering (Names valueWidth)
open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF.SwitchAssert (Cfg Outcome)
open RVSDG (Dialect PortType Port Tuple Wires)
open RVSDG.NestedTheta (Graph Term)
open RVSDG.NestedTheta.Institution.RuntimeObservation (Sentence)
open Blocks.Prune (Mask)
open Diamond.Prune (Checked)

universe u v w

/-- Each source entry position names exactly one new entry position of
the same sort, with the inverse covering every new position. -/
abbrev Permutation {T : Type u} (old new : List T) :=
  ∀ t, Port old t ≃ Port new t

def Permutation.refl {T : Type u} (ports : List T) : Permutation ports ports :=
  fun t => Equiv.refl (Port ports t)

/-- Apply the first port map, then the second port map. -/
def Permutation.trans {T : Type u} {old mid new : List T}
    (first : Permutation old mid) (second : Permutation mid new) : Permutation old new :=
  fun t => (first t).trans (second t)

def Permutation.symm {T : Type u} {old new : List T} (order : Permutation old new) : Permutation new old :=
  fun t => (order t).symm

/-- Exchange the first two positions while preserving the sort of each port. -/
def Permutation.swap {T : Type u} (a b : T) (rest : List T) :
    Permutation (a :: b :: rest) (b :: a :: rest) := fun _ =>
  { toFun := fun
      | .head => .tail .head
      | .tail .head => .head
      | .tail (.tail port) => .tail (.tail port)
    invFun := fun
      | .head => .tail .head
      | .tail .head => .head
      | .tail (.tail port) => .tail (.tail port)
    left_inv := by
      intro port
      cases port with
      | head => rfl
      | tail port => cases port <;> rfl
    right_inv := by
      intro port
      cases port with
      | head => rfl
      | tail port => cases port <;> rfl }

def Permutation.cons {T : Type u} {old new : List T} (order : Permutation old new) (first : T) :
    Permutation (first :: old) (first :: new) := fun _ =>
  { toFun := fun
      | .head => .head
      | .tail port => .tail (order _ port)
    invFun := fun
      | .head => .head
      | .tail port => .tail ((order _).symm port)
    left_inv := by
      intro port
      cases port with
      | head => rfl
      | tail port => exact congrArg Port.tail ((order _).symm_apply_apply port)
    right_inv := by
      intro port
      cases port with
      | head => rfl
      | tail port => exact congrArg Port.tail ((order _).apply_symm_apply port) }

/-- Apply a permutation after a fixed prefix of entry sorts. -/
def Permutation.under {T : Type u} {old new : List T} (order : Permutation old new) :
    (fixed : List T) → Permutation (fixed ++ old) (fixed ++ new)
  | [] => order
  | first :: rest => (order.under rest).cons first

def pull {T : Type u} {F : T → Type w} {old new : List T}
    (order : Permutation old new) (input : Tuple F new) : Tuple F old :=
  tabulate old fun {t} port => input.get (order t port)

section Graph

variable {V S : Type u} {Φ : Dialect.{u, v} V S}
variable {old new outs : List (PortType V S)} {past sigs : List (List (PortType V S))}

def wires (order : Permutation old new) (bundle : Wires old past outs) : Wires new past outs :=
  bundle.map fun t => fun
    | .arg port => .arg (order t port)
    | .output producer port => .output producer port

/-- Change outer argument origins. The ordered bindings and the original
child regions, including the entire θ body, are reused. -/
def term (order : Permutation old new) : {past sigs : List (List (PortType V S))} →
    Term Φ old past sigs outs → Term Φ new past sigs outs
  | _, _, .ret result => .ret (wires order result)
  | _, _, .bind node children rest =>
    .bind ⟨node.ins, node.kind, wires order node.inputs, node.childSigs⟩ children (term order rest)

def graph (order : Permutation old new) (g : Graph Φ old past sigs outs) : Graph Φ new past sigs outs :=
  (term order g.toTerm).toGraph

end Graph

variable {regs external : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}
variable {p : Program src entry} {mask : Mask regs}

abbrev EntryPermutation (regs external : List (ValueSort Width)) :=
  Permutation (dataPorts regs) (dataPorts external)

def cfNames (order : EntryPermutation regs external) :
    Tuple (Names (Widths external)) (dataPorts regs) :=
  pull order (entryNames external)

def lowerCF (order : EntryPermutation regs external) (checked : Checked p mask) :
    Silmaril.MLIR.CF.Cfg TargetOp (Label p.header regs mask.kept out) (Widths external) [valueWidth out] :=
  lowerWith checked (cfNames order)

noncomputable def observeCF (order : EntryPermutation regs external) (checked : Checked p mask)
    (input : Env (Widths external)) : Part (Outcome [valueWidth out]) :=
  (Cfg.embed (lowerCF order checked)).denotePart evalOp input

variable {w : Width} {leftSize rightSize : Nat}
variable {leftSource : Source Op regs (.data w) leftSize}
variable {rightSource : Source Op regs (.data w) rightSize}
variable {leftEntry : Fin leftSize} {rightEntry : Fin rightSize}
variable {left : Program leftSource leftEntry} {right : Program rightSource rightEntry}
variable {leftMask rightMask : Mask regs}

/-- Package the reindexed unpruned graphs in the existing native sentence. -/
def nativeEquation (order : EntryPermutation regs external)
    (left : Program leftSource leftEntry) (right : Program rightSource rightEntry) : Sentence Equation.signature :=
  .equation ⟨_, graph order left.lower⟩ ⟨_, graph order right.lower⟩

def prunedEquation (order : EntryPermutation regs external)
    (lhs : Checked left leftMask) (rhs : Checked right rightMask) : Sentence Equation.signature :=
  .equation ⟨_, graph order lhs.lower⟩ ⟨_, graph order rhs.lower⟩

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex

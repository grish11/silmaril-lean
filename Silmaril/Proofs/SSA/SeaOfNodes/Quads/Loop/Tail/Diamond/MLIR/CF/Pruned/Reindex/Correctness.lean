module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Comparison.Equation.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Categorical.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex.Proofs

open SeaOfNodes.Diamond (ValueSort dataPorts)
open SeaOfNodes.Loop.MLIR.CF (Op model evalOp)
open SeaOfNodes.MLIR.Lowering (NamesAgree encodeValues)
open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF.SwitchAssert (Cfg)
open RVSDG (Dialect PortType Port Tuple Locals Wires)
open RVSDG.NestedTheta (Graph Term)
open Blocks (Bank)
open Blocks.Prune (Mask)
open Diamond.Prune (Checked)

universe u v w

section Pull

variable {T : Type u} {F : T → Type w} {old new : List T} (order : Permutation old new)

theorem pull_get (input : Tuple F new) {t : T} (port : Port old t) :
    (pull order input).get port = input.get (order t port) :=
  Quads.get_tabulate _ port

theorem pull_surjective : Function.Surjective (pull order : Tuple F new → Tuple F old) := by
  intro input
  refine ⟨pull order.symm input, ?_⟩
  have ports : (fun {t} (port : Port old t) => (pull order.symm input).get (order t port)) =
      (fun {t} (port : Port old t) => input.get port) := by
    funext t port
    rw [pull_get]
    exact congrArg input.get ((order t).symm_apply_apply port)
  exact (congrArg (tabulate old) ports).trans (Quads.tabulate_get_eq input)

private theorem forall_pull_iff (P : Tuple F old → Prop) :
    (∀ input, P (pull order input)) ↔ ∀ input, P input := by
  constructor
  · intro holds input
    obtain ⟨external, rfl⟩ := pull_surjective order input
    exact holds external
  · exact fun holds input => holds (pull order input)

end Pull

section Graph

variable {V S : Type u} {Φ : Dialect.{u, v} V S}
variable {old new outs : List (PortType V S)} {past sigs : List (List (PortType V S))}
variable (order : Permutation old new) (m : RVSDG.Model.{u, v, w} Φ) (fuel : Nat)

private theorem read_wires (bundle : Wires old past outs)
    (input : Tuple m.Val new) (locals : Locals m.Val past) :
    (wires order bundle).read input locals = bundle.read (pull order input) locals := by
  induction bundle with
  | nil => rfl
  | cons origin rest ih =>
    cases origin with
    | arg port =>
      change Tuple.cons (input.get (order _ port)) ((wires order rest).read input locals) =
        Tuple.cons ((pull order input).get port) (Wires.read rest (pull order input) locals)
      rw [pull_get, ih]
    | output producer port =>
      exact congrArg (Tuple.cons ((locals.get producer).get port)) ih

private theorem term_eval (t : Term Φ old past sigs outs)
    (input : Tuple m.Val new) (locals : Locals m.Val past) :
    (term order t).eval m fuel input locals = t.eval m fuel (pull order input) locals := by
  induction t with
  | ret results => exact congrArg some (read_wires order m results input locals)
  | bind node children rest _ ih =>
    simp only [term, Term.eval, read_wires, ih]

theorem graph_run (g : Graph Φ old [] sigs outs) (input : Tuple m.Val new) :
    (graph order g).run m fuel input = g.run m fuel (pull order input) := by
  rw [← (graph order g).run_toTerm, graph, Term.toTerm_toGraph, ← g.run_toTerm]
  exact term_eval order m fuel g.toTerm input PUnit.unit

theorem graph_observe (g : Graph Φ old [] sigs outs) (input : Tuple m.Val new) :
    (graph order g).denotePart m input = g.denotePart m (pull order input) := by
  apply Part.ext
  intro result
  rw [Graph.mem_denote, Graph.mem_denote, ← Graph.returns_iff, ← Graph.returns_iff]
  exact exists_congr fun fuel => by rw [graph_run]

end Graph

variable {regs external : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}
variable {p : Program src entry} {mask : Mask regs}
variable (order : EntryPermutation regs external)

private theorem cfNames_agree (input : Bank (regs := external) model) :
    NamesAgree (encodeValues input) (cfNames order) (pull order input) := by
  intro sort port
  unfold cfNames
  rw [pull_get, pull_get]
  exact CF.entryNames_agree input (order _ port)

theorem cf_run (checked : Checked p mask) (fuel : Nat) (input : Bank (regs := external) model) :
    (lowerCF order checked).run evalOp fuel (encodeValues input) =
      (Pruned.lower checked).run evalOp fuel (encodeValues (pull order input)) := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    exact (Pruned.lowerWith_run checked (cfNames order) (encodeValues input)
      fuel (pull order input) (cfNames_agree order input)).trans
        (Pruned.lower_run checked fuel (pull order input)).symm

theorem cf_observe {w : Width} {src : Source Op regs (.data w) size} {entry : Fin size}
    {p : Program src entry} (checked : Checked p mask) (input : Bank (regs := external) model) :
    observeCF order checked (encodeValues input) =
      Equation.observeCF checked (encodeValues (pull order input)) := by
  apply Part.ext
  intro result
  simp only [observeCF, Equation.observeCF, Cfg.mem_denotePart_iff, Cfg.embed_run, cf_run]

variable {word : Width} {leftSize rightSize : Nat}
variable {leftSource : Source Op regs (.data word) leftSize}
variable {rightSource : Source Op regs (.data word) rightSize}
variable {leftEntry : Fin leftSize} {rightEntry : Fin rightSize}
variable {left : Program leftSource leftEntry} {right : Program rightSource rightEntry}
variable {leftMask rightMask : Mask regs}

theorem native_satisfaction (left : Program leftSource leftEntry) (right : Program rightSource rightEntry) :
    (nativeEquation order left right).Holds (Join.model model) ↔
      (Equation.nativeEquation left right).Holds (Join.model model) := by
  change (∀ input : Bank (regs := external) model,
    (graph order left.lower).denotePart (Join.model model) input =
      (graph order right.lower).denotePart (Join.model model) input) ↔ _
  simp only [graph_observe]
  exact forall_pull_iff order (fun bank : Bank (regs := regs) model =>
    left.lower.denotePart (Join.model model) bank = right.lower.denotePart (Join.model model) bank)

theorem rvsdg_satisfaction (lhs : Checked left leftMask) (rhs : Checked right rightMask) :
    (prunedEquation order lhs rhs).Holds (Join.model model) ↔
      (Equation.nativeEquation left right).Holds (Join.model model) := by
  suffices (prunedEquation order lhs rhs).Holds (Join.model model) ↔
      (Equation.prunedEquation lhs rhs).Holds (Join.model model) from
    this.trans (Equation.rvsdg_satisfaction lhs rhs)
  change (∀ input : Bank (regs := external) model,
    (graph order lhs.lower).denotePart (Join.model model) input =
      (graph order rhs.lower).denotePart (Join.model model) input) ↔ _
  simp only [graph_observe]
  exact forall_pull_iff order (fun bank : Bank (regs := regs) model =>
    lhs.lower.denotePart (Join.model model) bank = rhs.lower.denotePart (Join.model model) bank)

theorem cf_satisfaction (lhs : Checked left leftMask) (rhs : Checked right rightMask) :
    (∀ input : Env (Widths external), observeCF order lhs input = observeCF order rhs input) ↔
      (Equation.nativeEquation left right).Holds (Join.model model) := by
  rw [← Equation.cf_satisfaction lhs rhs]
  constructor
  · intro holds env
    obtain ⟨input, rfl⟩ := Equation.encodeValues_surjective regs env
    obtain ⟨external, rfl⟩ := pull_surjective order input
    exact (cf_observe order lhs external).symm.trans
      ((holds (encodeValues external)).trans (cf_observe order rhs external))
  · intro holds env
    obtain ⟨input, rfl⟩ := Equation.encodeValues_surjective external env
    rw [cf_observe, cf_observe]
    exact holds (encodeValues (pull order input))

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex.Proofs

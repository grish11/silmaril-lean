module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Defs
import Silmaril.SSA.SeaOfNodes.Quads.CFG.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Chain.Segment.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Proofs

open SeaOfNodes.Diamond (Model ValueSort)
open Join (Block)
open Blocks (Bank)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}
variable (p : Program src entry) (m : Model.{u, v, w} Op)

theorem merge_bank (old : Bank (regs := regs) m) (occurrence : Occurrence) :
    p.mergeBank m old occurrence = (p.pathQuads occurrence).eval m old := by
  exact (CFG.compileBlock_read (past := []) (p.pathQuads occurrence) m old PUnit.unit (initial regs)).trans
    (congrArg (Block.eval (p.pathQuads occurrence) m) (read_initial m old))

private theorem segment_starts {target site : Fin size}
    (arm : Chain.Segment src target site) (away : site ≠ target) : site ∈ arm.blocks := by
  cases arm with
  | empty => exact (away rfl).elim
  | jump => exact List.Mem.head _

private theorem segment_direct {target site : Fin size} (arm : Chain.Segment src target site)
    (same : site = target) (noTarget : target ∉ arm.blocks) (caller : Fin size) :
    arm.blocks = [] ∧ arm.quads = [] ∧ arm.predecessor caller = caller := by
  subst site
  cases arm with
  | empty => exact ⟨rfl, rfl, rfl⟩
  | jump => exact (noTarget (List.Mem.head _)).elim

theorem parallel_inner_merge (same : p.onInnerTrue = p.onInnerFalse) (old : Bank (regs := regs) m)
    (outerTaken : (((src p.header).body.eval m old).get p.outerTest).down = true) :
    let inner := (src p.inner).body.eval m ((src p.header).body.eval m old)
    let occurrence := p.selected m old
    p.incomingEdge occurrence = (p.inner, if (inner.get p.innerTest).down then 0 else 1) ∧
      p.mergeBank m old occurrence = inner ∧ p.mergeVisits occurrence = 2 := by
  have ordered := p.distinct
  simp only [List.append_assoc] at ordered
  have arms := (List.nodup_append.mp ordered).2.1
  have trueDisjoint := (List.nodup_append.mp arms).2.2
  have falseDisjoint := (List.nodup_append.mp (List.nodup_append.mp arms).2.1).2.2
  have atJoin : p.onInnerTrue = p.join := by
    by_cases here : p.onInnerTrue = p.join
    · exact here
    · have left := segment_starts p.innerTrue here
      have right := segment_starts p.innerFalse (same ▸ here)
      exact (trueDisjoint _ left _ (List.mem_append_left _ right) same).elim
  obtain ⟨trueBlocks, trueQuads, truePred⟩ := segment_direct p.innerTrue atJoin
    (fun mem => trueDisjoint _ mem _ (by simp) rfl) p.inner
  obtain ⟨falseBlocks, falseQuads, falsePred⟩ := segment_direct p.innerFalse (same ▸ atJoin)
    (fun mem => falseDisjoint _ mem _ (by simp) rfl) p.inner
  dsimp only
  unfold Program.selected Control.selected
  rw [ite_eq_left outerTaken]
  by_cases taken : (((src p.inner).body.eval m ((src p.header).body.eval m old)).get p.innerTest).down = true
  · rw [ite_eq_left taken, ite_eq_left taken, merge_bank]
    dsimp only [Program.incomingEdge, Program.predecessor, Program.arm, Program.armStart, Program.splitSite,
      Program.pathQuads, Program.mergeVisits, Block.eval]
    rw [truePred, trueBlocks, trueQuads, List.append_nil, List.foldl_append]
    exact ⟨rfl, rfl, rfl⟩
  · rw [ite_eq_right taken, ite_eq_right taken, merge_bank]
    dsimp only [Program.incomingEdge, Program.predecessor, Program.arm, Program.armStart, Program.splitSite,
      Program.pathQuads, Program.mergeVisits, Block.eval]
    rw [falsePred, falseBlocks, falseQuads, List.append_nil, List.foldl_append]
    exact ⟨rfl, rfl, rfl⟩

private theorem run_split {site yes no : Fin size} {test}
    (edge : (src site).terminator = .branch test (.jump yes) (.jump no))
    (old : Bank (regs := regs) m) (fuel : Nat) (direction : Bool)
    (taken : (((src site).body.eval m old).get test).down = direction) :
    src.runFrom m (fuel + 1) site old =
      src.runFrom m fuel (if direction then yes else no) ((src site).body.eval m old) := by
  simp only [Tail.Source.runFrom, edge, Tail.Terminator.select, taken]
  cases direction <;> rfl

theorem run_to_merge (old : Bank (regs := regs) m) (fuel : Nat) :
    let occurrence := p.selected m old
    src.runFrom m (fuel + p.mergeVisits occurrence) p.header old =
      src.runFrom m fuel p.join (p.mergeBank m old occurrence) := by
  let outer := (src p.header).body.eval m old
  let inner := (src p.inner).body.eval m outer
  have selection : p.selected m old =
      if (outer.get p.outerTest).down then
        if (inner.get p.innerTest).down then .innerTrue else .innerFalse
      else .outerFalse := rfl
  dsimp only
  rw [selection]
  by_cases yes : (outer.get p.outerTest).down = true
  · rw [ite_eq_left yes]
    have outerStep (remaining : Nat) :
        src.runFrom m (remaining + 1) p.header old = src.runFrom m remaining p.inner outer :=
      run_split m p.outerEdge old remaining true yes
    by_cases innerYes : (inner.get p.innerTest).down = true
    · rw [ite_eq_left innerYes, merge_bank]
      have cost : fuel + (p.innerTrue.blocks.length + 2) =
          fuel + p.innerTrue.blocks.length + 1 + 1 := by omega
      have innerStep :
          src.runFrom m (fuel + p.innerTrue.blocks.length + 1) p.inner outer =
            src.runFrom m (fuel + p.innerTrue.blocks.length) p.onInnerTrue inner :=
        run_split m p.innerEdge outer _ true innerYes
      rw [Program.mergeVisits, cost, outerStep, innerStep, p.innerTrue.run_segment m]
      simp only [Program.pathQuads, Program.arm, Block.eval, List.foldl_append, outer, inner] <;> rfl
    · rw [ite_eq_right innerYes, merge_bank]
      have cost : fuel + (p.innerFalse.blocks.length + 2) =
          fuel + p.innerFalse.blocks.length + 1 + 1 := by omega
      have innerStep :
          src.runFrom m (fuel + p.innerFalse.blocks.length + 1) p.inner outer =
            src.runFrom m (fuel + p.innerFalse.blocks.length) p.onInnerFalse inner :=
        run_split m p.innerEdge outer _ false (Bool.eq_false_iff.mpr innerYes)
      rw [Program.mergeVisits, cost, outerStep, innerStep, p.innerFalse.run_segment m]
      simp only [Program.pathQuads, Program.arm, Block.eval, List.foldl_append, outer, inner] <;> rfl
  · rw [ite_eq_right yes, merge_bank]
    have cost : fuel + (p.outerFalse.blocks.length + 1) =
        fuel + p.outerFalse.blocks.length + 1 := by omega
    have outerStep :
        src.runFrom m (fuel + p.outerFalse.blocks.length + 1) p.header old =
          src.runFrom m (fuel + p.outerFalse.blocks.length) p.onOuterFalse outer :=
      run_split m p.outerEdge old _ false (Bool.eq_false_iff.mpr yes)
    rw [Program.mergeVisits, cost, outerStep, p.outerFalse.run_segment m]
    simp only [Program.pathQuads, Program.arm, Block.eval, List.foldl_append, outer] <;> rfl

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Proofs

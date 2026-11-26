module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Defs
import Silmaril.SSA.SeaOfNodes.Quads.CFG.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Chain.Segment.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Proofs

open SeaOfNodes.Diamond (Model ValueSort)
open Join (Block)
open Blocks (Bank)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}
variable (p : Program src entry) (m : Model.{u, v, w} Op)

private theorem compiled_bank (quads : Block Op regs) (old : Bank (regs := regs) m) :
    let compiled := CFG.compileBlock quads (initial regs)
    compiled.outgoing.read old (compiled.flow.eval m old PUnit.unit) = quads.eval m old :=
  (CFG.compileBlock_read (past := []) quads m old PUnit.unit (initial regs)).trans
    (congrArg (Block.eval quads m) (read_initial m old))

theorem prefix_bank (old : Bank (regs := regs) m) (occurrence : Occurrence) :
    p.prefixBank m old occurrence = (p.prefixQuads occurrence).eval m old :=
  compiled_bank m _ old

theorem suffix_bank (incoming : Bank (regs := regs) m) :
    p.suffixBank m incoming = p.suffix.quads.eval m incoming :=
  compiled_bank m _ incoming

private theorem predecessor_mem {target site : Fin size}
    (segment : Chain.Segment src target site) (caller : Fin size) :
    (segment.blocks = [] ∧ segment.predecessor caller = caller) ∨
      segment.predecessor caller ∈ segment.blocks := by
  induction segment generalizing caller with
  | empty => exact Or.inl ⟨rfl, rfl⟩
  | jump site _ rest ih =>
    rcases ih site with ⟨_, same⟩ | mem
    · exact Or.inr (by
        show rest.predecessor site ∈ site :: rest.blocks
        rw [same]
        exact List.Mem.head _)
    · exact Or.inr (List.Mem.tail _ mem)

theorem inner_edges_distinct : p.innerEdgeOccurrence true ≠ p.innerEdgeOccurrence false := by
  have ordered := p.distinct
  simp only [List.append_assoc, List.cons_append, List.nil_append] at ordered
  have innerFirst := List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp ordered).2).2
  have separate := (List.nodup_append.mp innerFirst.2).2.2
  intro equal
  have samePred := congrArg Prod.fst equal
  change p.innerTrue.predecessor p.inner = p.innerFalse.predecessor p.inner at samePred
  rcases predecessor_mem p.innerTrue p.inner with ⟨_, yes⟩ | yes
  · rcases predecessor_mem p.innerFalse p.inner with ⟨empty, no⟩ | no
    · have sameSlot := congrArg Prod.snd equal
      change (0 : Fin 2) = (bif p.innerFalse.blocks.isEmpty then 1 else 0) at sameSlot
      rw [empty] at sameSlot
      exact (show (0 : Fin 2) ≠ 1 by decide) sameSlot
    · exact innerFirst.1 (List.mem_append_right _ (List.mem_append_left _ ((yes.symm.trans samePred) ▸ no)))
  · rcases predecessor_mem p.innerFalse p.inner with ⟨_, no⟩ | no
    · exact innerFirst.1 (List.mem_append_left _ ((samePred.trans no) ▸ yes))
    · exact separate _ yes _ (List.mem_append_left _ no) samePred

private theorem run_branch {site yes no : Fin size} {test}
    (edge : (src site).terminator = .branch test (.jump yes) (.jump no))
    (old : Bank (regs := regs) m) (fuel : Nat) (taken : Bool)
    (guard : (((src site).body.eval m old).get test).down = taken) :
    src.runFrom m (fuel + 1) site old =
      src.runFrom m fuel (if taken then yes else no) ((src site).body.eval m old) := by
  simp only [Tail.Source.runFrom, edge, Tail.Terminator.select, guard]
  cases taken <;> rfl

theorem run_prefix (old : Bank (regs := regs) m) (fuel : Nat) :
    let occurrence := p.toControl.selected m old
    src.runFrom m (fuel + p.prefixVisits occurrence) p.header old =
      src.runFrom m fuel (p.prefixTarget occurrence) (p.prefixBank m old occurrence) := by
  let outer := (src p.header).body.eval m old
  let inner := (src p.inner).body.eval m outer
  have selection : p.toControl.selected m old =
      if (outer.get p.outerTest).down then
        if (inner.get p.innerTest).down then .innerTrue else .innerFalse
      else .outerFalse := rfl
  dsimp only
  rw [selection]
  by_cases outerTaken : (outer.get p.outerTest).down = true
  · simp only [ite_eq_left outerTaken]
    have enterInner (remaining : Nat) :
        src.runFrom m (remaining + 1) p.header old = src.runFrom m remaining p.inner outer :=
      run_branch m p.outerEdge old remaining true outerTaken
    by_cases innerTaken : (inner.get p.innerTest).down = true
    · simp only [ite_eq_left innerTaken, Program.prefixVisits, Program.prefixTarget]
      have enterArm : src.runFrom m (fuel + p.innerTrue.blocks.length + 1) p.inner outer =
          src.runFrom m (fuel + p.innerTrue.blocks.length) p.onInnerTrue inner :=
        run_branch m p.innerEdge outer _ true innerTaken
      have cost : fuel + (p.innerTrue.blocks.length + 2) = fuel + p.innerTrue.blocks.length + 1 + 1 := by omega
      rw [cost, enterInner, enterArm, p.innerTrue.run_segment m, prefix_bank]
      simp only [Program.prefixQuads, Block.eval, List.foldl_append, outer, inner]
    · simp only [ite_eq_right innerTaken, Program.prefixVisits, Program.prefixTarget]
      have enterArm : src.runFrom m (fuel + p.innerFalse.blocks.length + 1) p.inner outer =
          src.runFrom m (fuel + p.innerFalse.blocks.length) p.onInnerFalse inner :=
        run_branch m p.innerEdge outer _ false (Bool.eq_false_iff.mpr innerTaken)
      have cost : fuel + (p.innerFalse.blocks.length + 2) = fuel + p.innerFalse.blocks.length + 1 + 1 := by omega
      rw [cost, enterInner, enterArm, p.innerFalse.run_segment m, prefix_bank]
      simp only [Program.prefixQuads, Block.eval, List.foldl_append, outer, inner]
  · simp only [ite_eq_right outerTaken, Program.prefixVisits, Program.prefixTarget]
    have leaveOuter : src.runFrom m (fuel + p.outerFalse.blocks.length + 1) p.header old =
        src.runFrom m (fuel + p.outerFalse.blocks.length) p.onOuterFalse outer :=
      run_branch m p.outerEdge old _ false (Bool.eq_false_iff.mpr outerTaken)
    rw [← Nat.add_assoc, leaveOuter, p.outerFalse.run_segment m, prefix_bank]
    simp only [Program.prefixQuads, Block.eval, List.foldl_append, outer]

theorem run_suffix (incoming : Bank (regs := regs) m) (fuel : Nat) :
    src.runFrom m (fuel + p.suffix.blocks.length) p.meet incoming =
      src.runFrom m fuel p.join (p.suffixBank m incoming) := by
  rw [p.suffix.run_segment m, suffix_bank]

theorem run_to_merge (old : Bank (regs := regs) m) (fuel : Nat) :
    let occurrence := p.toControl.selected m old
    src.runFrom m (fuel + p.mergeVisits occurrence) p.header old =
      src.runFrom m fuel p.join (p.mergeBank m old occurrence) := by
  dsimp only
  cases chosen : p.toControl.selected m old with
  | innerTrue =>
    rw [Program.mergeVisits, Program.mergeBank, ← Nat.add_assoc,
      Nat.add_right_comm fuel (p.prefixVisits .innerTrue)]
    have arrived := run_prefix p m old (fuel + p.suffix.blocks.length)
    rw [chosen] at arrived
    exact arrived.trans (run_suffix p m (p.prefixBank m old .innerTrue) fuel)
  | innerFalse =>
    rw [Program.mergeVisits, Program.mergeBank, ← Nat.add_assoc,
      Nat.add_right_comm fuel (p.prefixVisits .innerFalse)]
    have arrived := run_prefix p m old (fuel + p.suffix.blocks.length)
    rw [chosen] at arrived
    exact arrived.trans (run_suffix p m (p.prefixBank m old .innerFalse) fuel)
  | outerFalse =>
    simpa only [chosen, Program.mergeVisits, Nat.add_zero, Program.mergeBank, Program.prefixTarget] using
      run_prefix p m old fuel

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Proofs

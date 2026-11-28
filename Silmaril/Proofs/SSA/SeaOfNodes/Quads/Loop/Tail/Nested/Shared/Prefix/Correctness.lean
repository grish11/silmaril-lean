module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Prefix.Defs
import Silmaril.SSA.SeaOfNodes.Quads.CFG.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Chain.Segment.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Numbered.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Join.Finite.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Join.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Prefix.Proofs

open SeaOfNodes.Diamond (Model Ty Val ValueSort dataPorts)
open RVSDG (Locals Tuple Wires extend)
open RVSDG.NestedTheta (Term)
open Join (Opcode model)
open Join.Finite (Plan Stage)
open Nested.Numbered (linkGamma_eval splitSigs)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond (thenBase_eval)
open Join (Block)
open Blocks (Bank)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}
variable (p : Routes src entry) (m : Model.{u, v, w} Op)

theorem compiled_bank (quads : Block Op regs) (old : Bank (regs := regs) m) :
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

theorem predecessor_mem {target site : Fin size}
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

theorem inner_edges_distinct {later : List (Fin size)}
    (ordered : ([entry, p.header, p.inner] ++ p.innerTrue.blocks ++ p.innerFalse.blocks ++ later).Nodup) :
    p.innerEdgeOccurrence true ≠ p.innerEdgeOccurrence false := by
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
    · simp only [ite_eq_left innerTaken, Routes.prefixVisits, Routes.prefixTarget]
      have enterArm : src.runFrom m (fuel + p.innerTrue.blocks.length + 1) p.inner outer =
          src.runFrom m (fuel + p.innerTrue.blocks.length) p.onInnerTrue inner :=
        run_branch m p.innerEdge outer _ true innerTaken
      have cost : fuel + (p.innerTrue.blocks.length + 2) = fuel + p.innerTrue.blocks.length + 1 + 1 := by omega
      rw [cost, enterInner, enterArm, p.innerTrue.run_segment m, prefix_bank]
      simp only [Routes.prefixQuads, Block.eval, List.foldl_append, outer, inner]
    · simp only [ite_eq_right innerTaken, Routes.prefixVisits, Routes.prefixTarget]
      have enterArm : src.runFrom m (fuel + p.innerFalse.blocks.length + 1) p.inner outer =
          src.runFrom m (fuel + p.innerFalse.blocks.length) p.onInnerFalse inner :=
        run_branch m p.innerEdge outer _ false (Bool.eq_false_iff.mpr innerTaken)
      have cost : fuel + (p.innerFalse.blocks.length + 2) = fuel + p.innerFalse.blocks.length + 1 + 1 := by omega
      rw [cost, enterInner, enterArm, p.innerFalse.run_segment m, prefix_bank]
      simp only [Routes.prefixQuads, Block.eval, List.foldl_append, outer, inner]
  · simp only [ite_eq_right outerTaken, Routes.prefixVisits, Routes.prefixTarget]
    have leaveOuter : src.runFrom m (fuel + p.outerFalse.blocks.length + 1) p.header old =
        src.runFrom m (fuel + p.outerFalse.blocks.length) p.onOuterFalse outer :=
      run_branch m p.outerEdge old _ false (Bool.eq_false_iff.mpr outerTaken)
    rw [← Nat.add_assoc, leaveOuter, p.outerFalse.run_segment m, prefix_bank]
    simp only [Routes.prefixQuads, Block.eval, List.foldl_append, outer]

theorem run_suffix (incoming : Bank (regs := regs) m) (fuel : Nat) :
    src.runFrom m (fuel + p.suffix.blocks.length) p.meet incoming =
      src.runFrom m fuel p.stop (p.suffixBank m incoming) := by
  rw [p.suffix.run_segment m, suffix_bank]

theorem run_to_outer (old : Bank (regs := regs) m) (fuel : Nat) :
    let occurrence := p.toControl.selected m old
    src.runFrom m (fuel + p.outerVisits occurrence) p.header old =
      src.runFrom m fuel p.stop (p.outerBank m old occurrence) := by
  dsimp only
  cases chosen : p.toControl.selected m old with
  | innerTrue =>
    rw [Routes.outerVisits, Routes.outerBank, ← Nat.add_assoc,
      Nat.add_right_comm fuel (p.prefixVisits .innerTrue)]
    have arrived := run_prefix p m old (fuel + p.suffix.blocks.length)
    rw [chosen] at arrived
    exact arrived.trans (run_suffix p m (p.prefixBank m old .innerTrue) fuel)
  | innerFalse =>
    rw [Routes.outerVisits, Routes.outerBank, ← Nat.add_assoc,
      Nat.add_right_comm fuel (p.prefixVisits .innerFalse)]
    have arrived := run_prefix p m old (fuel + p.suffix.blocks.length)
    rw [chosen] at arrived
    exact arrived.trans (run_suffix p m (p.prefixBank m old .innerFalse) fuel)
  | outerFalse =>
    simpa only [chosen, Routes.outerVisits, Nat.add_zero, Routes.outerBank, Routes.prefixTarget] using
      run_prefix p m old fuel

private def innerBank (header : Bank (regs := regs) m) : Bank (regs := regs) m :=
  p.suffixBank m ((innerPlan p).eval m ((src p.inner).body.eval m header))

private def branchBank (header : Bank (regs := regs) m) : Bank (regs := regs) m :=
  if (header.get p.outerTest).down then innerBank p m header else p.outerFalse.quads.eval m header

private theorem inner_run (fuel : Nat) (header : Bank (regs := regs) m) :
    (innerRegion p).run (model m) fuel header = some (innerBank p m header) := by
  unfold innerRegion Term.run innerBank
  erw [thenBase_eval (observe := fun bank => some (p.suffixBank m ((innerPlan p).eval m bank)))]
  · erw [Block.lowerFrom_eval, read_initial]
    rfl
  · intro wires locals
    erw [thenBase_eval (observe := fun bank => some (p.suffixBank m bank)), Plan.lowerFrom_eval]
    intro incoming locals'
    erw [Term.eval_ofBase, Block.lowerFrom_eval, suffix_bank p m]
    rfl

private theorem outer_arm_run (fuel : Nat) (bank : Bank (regs := regs) m) :
    (outerArm p ((outerChoice p).eval bank)).run (model m) fuel bank = some (branchBank p m bank) := by
  by_cases yes : (bank.get p.outerTest).down = true
  · have pick : (outerChoice p).eval bank = 0 := by simp [outerChoice, Join.Choice.eval, yes]
    rw [pick, branchBank, ite_eq_left yes]
    exact inner_run p m fuel bank
  · have pick : (outerChoice p).eval bank = 1 := by simp [outerChoice, Join.Choice.eval, yes]
    rw [pick, branchBank, ite_eq_right yes]
    change (Term.ofBase (p.outerFalse.quads.lowerFrom (initial regs) .jump)).run (model m) fuel bank = _
    rw [Term.run_ofBase]
    unfold RVSDG.Term.run
    erw [Block.lowerFrom_eval, read_initial]
    rfl

private theorem branchBank_agrees (old : Bank (regs := regs) m) :
    branchBank p m ((src p.header).body.eval m old) =
      p.outerBank m old (p.toControl.selected m old) := by
  let outer := (src p.header).body.eval m old
  let inner := (src p.inner).body.eval m outer
  have selection : p.toControl.selected m old =
      if (outer.get p.outerTest).down then
        if (inner.get p.innerTest).down then .innerTrue else .innerFalse
      else .outerFalse := rfl
  rw [selection]
  change (if (outer.get p.outerTest).down then p.suffixBank m ((innerPlan p).eval m inner)
    else p.outerFalse.quads.eval m outer) = _
  by_cases yes : (outer.get p.outerTest).down = true
  · rw [ite_eq_left yes, ite_eq_left yes]
    by_cases innerYes : (inner.get p.innerTest).down = true
    · rw [ite_eq_left innerYes]
      dsimp only [Routes.outerBank]
      rw [prefix_bank p m]
      simp only [innerPlan, Plan.eval, List.foldl_cons, List.foldl_nil, Stage.eval, Stage.table,
        Join.Choice.eval, ite_eq_left innerYes]
      simp only [Routes.prefixQuads, Block.eval, List.foldl_append, outer, inner]
      rfl
    · rw [ite_eq_right innerYes]
      dsimp only [Routes.outerBank]
      rw [prefix_bank p m]
      simp only [innerPlan, Plan.eval, List.foldl_cons, List.foldl_nil, Stage.eval, Stage.table,
        Join.Choice.eval, ite_eq_right innerYes]
      simp only [Routes.prefixQuads, Block.eval, List.foldl_append, outer, inner]
      rfl
  · rw [ite_eq_right yes, ite_eq_right yes]
    dsimp only [Routes.outerBank]
    rw [prefix_bank p m]
    simp only [Routes.prefixQuads, Block.eval, List.foldl_append, outer]

private theorem afterOuter_eval {args results : List (Ty Data)} {past suffix : List (List (Ty Data))}
    (current : Wires args past (dataPorts regs))
    (finish : Wires args (extend past (splitSigs regs)) (dataPorts regs) →
      Term (Opcode Op) args (extend past (splitSigs regs)) suffix results)
    (fuel : Nat) (input : Tuple (Val m.value) args) (locals : Locals (Val m.value) past)
    (observe : Bank (regs := regs) m → Option (Tuple (Val m.value) results))
    (agrees : ∀ wires locals', (finish wires).eval (model m) fuel input locals' =
      observe (wires.read input locals')) :
    (afterOuter p current finish).eval (model m) fuel input locals =
      observe (branchBank p m (current.read input locals)) :=
  linkGamma_eval m (outerChoice p) (outerSigs p) (outerArm p) current finish fuel input locals
    (branchBank p m) (outer_arm_run p m fuel) observe agrees

theorem afterHeader_run {results : List (Ty Data)} {suffix : List (List (Ty Data))}
    (finish : Wires (dataPorts regs)
        (extend (extend [] (src p.header).body.producers) (splitSigs regs)) (dataPorts regs) →
      Term (Opcode Op) (dataPorts regs)
        (extend (extend [] (src p.header).body.producers) (splitSigs regs)) suffix results)
    (fuel : Nat) (old : Bank (regs := regs) m) (observe : Bank (regs := regs) m → Option (Tuple (Val m.value) results))
    (agrees : ∀ wires locals, (finish wires).eval (model m) fuel old locals = observe (wires.read old locals)) :
    (afterHeader p finish).run (model m) fuel old =
      observe (p.outerBank m old (p.toControl.selected m old)) := by
  unfold afterHeader Term.run
  erw [thenBase_eval (observe := fun bank => observe (branchBank p m bank))]
  · erw [Block.lowerFrom_eval, read_initial, branchBank_agrees]
  · intro wires locals
    exact afterOuter_eval p m wires finish fuel old locals observe agrees

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Prefix.Proofs

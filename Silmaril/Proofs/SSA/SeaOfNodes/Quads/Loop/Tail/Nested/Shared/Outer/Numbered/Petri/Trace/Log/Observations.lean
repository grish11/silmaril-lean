module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Log.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Log.Replay
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Inversion.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Log.Proofs

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open Silmaril.MLIR.Arith (Width)
open Blocks (Bank)
open RVSDG.NestedTheta.Petri (finished pending)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} (p : Program src entry)
variable (input : Bank (regs := regs) model)
variable {pre : PreMark p} {old : Bank (regs := regs) model} {roots : List (RootMark p)}

theorem firstOuter_eq (s : Slice p input pre old (pending semantics (thetaBody p)) roots) :
    s.firstOuter = some (packetsAt p old).outer.2 := by
  have done := Option.isSome_iff_exists.mpr ⟨_, s.complete⟩
  obtain ⟨earlier, before, after, later, split, absent, notYet, _, read, _⟩ :=
    first_outer_read p old s.body s.legal done
  unfold Slice.firstOuter
  rw [split, List.findSome?_append, List.findSome?_eq_none_iff.mpr absent]
  simp [notYet, read]

theorem packet_eq (s : Slice p input pre old (pending semantics (thetaBody p)) roots) :
    let next := nextBank p model old
    s.packet = RVSDG.Theta.bodyResult semantics (next.get p.again).down next := by
  have trace := reaches _ s.body s.legal
  have done := Option.isSome_iff_exists.mpr ⟨_, s.complete⟩
  exact Option.some.inj (s.complete.symm.trans (completed_activation p old trace done).2)

theorem boundary (s : Slice p input pre old (pending semantics (thetaBody p)) roots)
    (preDone : (finished semantics (preheader p) input PUnit.unit pre).isSome) :
    let next := nextBank p model old
    s.after = afterLatch p pre (next.get p.again).down next :=
  (latch_step p old input preDone (reaches _ s.body s.legal)
    (Option.isSome_iff_exists.mpr ⟨_, s.complete⟩) s.consumes).1

private theorem decode (again : Bool) (next : Bank (regs := regs) model) :
    feedback (RVSDG.Theta.bodyResult semantics again next) = again ∧
      nextBankOf (RVSDG.Theta.bodyResult semantics again next) = next := by
  cases again <;> exact ⟨rfl, rfl⟩

theorem observation_agrees (inner : Shared.MLIR.CF.InnerPhi.Rows p.toRoutes) (outer : MLIR.CF.Phi.Rows p)
    (s : Slice p input pre old (pending semantics (thetaBody p)) roots)
    {bank : Bank (regs := regs) model} (read : s.firstOuter = some bank) :
    (s.observation p input bank).Agrees p input inner outer := by
  let next := nextBank p model old
  have packet := packet_eq p input s
  have check := decode (next.get p.again).down next
  have flag : feedback s.packet = (next.get p.again).down := (congrArg feedback packet).trans check.1
  have bankNext : nextBankOf s.packet = next := (congrArg nextBankOf packet).trans check.2
  have outerEq := Option.some.inj (read.symm.trans (firstOuter_eq p input s))
  have cfOuter := congrArg Prod.snd (packetsAt_cf p input inner outer old)
  refine ⟨?_, bankNext, flag.trans (congrArg (fun x : Bank (regs := regs) model =>
    (x.get p.again).down) bankNext.symm), ?_⟩
  · exact (congrArg (fun payload => (p.outerEdgeOccurrence (MLIR.CF.Phi.arrivalSide (p := p) old),
      SeaOfNodes.MLIR.Lowering.encodeValues payload)) outerEq).trans cfOuter
  · change MLIR.CF.latchSuccessor p input old = .inl (if feedback s.packet then
      Diamond.MLIR.CF.siteFrame p.header (nextBankOf s.packet) else
      Diamond.MLIR.CF.exitFrame ((nextBankOf s.packet).get p.result))
    rw [flag, bankNext]
    exact MLIR.CF.Comparison.latch_successor p input old

theorem recovered_agrees (inner : Shared.MLIR.CF.InnerPhi.Rows p.toRoutes) (outer : MLIR.CF.Phi.Rows p)
    (r : Recovered p input pre old roots) :
    ∀ seen ∈ r.observations p input, seen.Agrees p input inner outer := by
  induction r with
  | stop slice bank read _ _ _ _ =>
    intro seen mem
    have one : seen = slice.observation p input bank := List.mem_singleton.mp mem
    exact one.symm ▸ observation_agrees p input inner outer slice read
  | again slice bank read _ _ ih =>
    intro seen mem
    rcases List.mem_cons.mp mem with same | rest
    · exact same.symm ▸ observation_agrees p input inner outer slice read
    · exact ih seen rest

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Log.Proofs

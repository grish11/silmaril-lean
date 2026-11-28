module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Numbered.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.GuardedTheta.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Join.Finite.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Join.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Numbered.Proofs

open SeaOfNodes.Diamond (Model Signature Val ValueSort dataPorts sortValue)
open RVSDG (Tuple)
open RVSDG.NestedTheta (Term Graph iterate)
open Join (Block model)
open Join.Finite (Plan Stage lastBank lastBank_read)
open Tail.Diamond (bodyPorts thenBase thenBase_eval)
open Blocks (Bank)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data}
variable (p : Program Op regs out) (m : Model.{u, v, w} Op)

private theorem feedback_eval (bank : Bank (regs := regs) m) :
    (feedbackPlan p).eval m bank = (p.feedback (bank.get p.select).down).eval m bank := by
  cases selected : (bank.get p.select).down <;>
    simp [feedbackPlan, Plan.eval, Stage.eval, Stage.table, Join.Choice.eval, selected]

private theorem body_run (fuel : Nat) (bank : Bank (regs := regs) m) :
    (thetaBody p).run (model m) fuel bank =
      let next := p.header.eval m ((p.feedback (bank.get p.select).down).eval m bank)
      some (RVSDG.Theta.bodyResult (model m) (next.get p.again).down next) := by
  let packet (next : Bank (regs := regs) m) :=
    some (RVSDG.Theta.bodyResult (model m) (next.get p.again).down next)
  let observe (feedback : Bank (regs := regs) m) := packet (p.header.eval m feedback)
  change (thenBase _ _).eval _ _ _ _ = observe ((p.feedback (bank.get p.select).down).eval m bank)
  erw [thenBase_eval (observe := observe)]
  · have reads := Plan.lowerFrom_eval (past := []) (feedbackPlan p) m bank PUnit.unit (initial regs)
    rw [read_initial m] at reads
    exact congrArg observe (reads.trans (feedback_eval p m bank))
  · intro feedback locals
    erw [thenBase_eval (observe := packet)]
    · exact congrArg packet (Block.lowerFrom_eval p.header .jump m bank locals feedback)
    · intro wires locals'
      change some ((lastBank _ (bodyPorts regs)).read bank (locals'.snoc
        ((model m).run (.route (.test p.again (.take 1) (.take 0))) (wires.read bank locals')))) = _
      rw [lastBank_read m, GuardedTheta.test_packet p.again]

theorem packet_run (fuel : Nat) (bank : Bank (regs := regs) m) :
    (thetaBody p).toGraph.run (model m) fuel bank =
      let next := p.header.eval m ((p.feedback (bank.get p.select).down).eval m bank)
      some (RVSDG.Theta.bodyResult (model m) (next.get p.again).down next) := by
  rw [← Graph.run_toTerm, Term.toTerm_toGraph, body_run]

private def project (value : sortValue m.value out) : Tuple (Val m.value) [.value out] :=
  .cons value .nil

private def observeHeader (outer remaining : Nat) (current : Bank (regs := regs) m) :
    Option (Tuple (Val m.value) [.value out]) :=
  if (current.get p.again).down then
    (iterate ((thetaBody p).run (model m) outer) (fun tag => tag.down.val == 1) remaining current).map
      (fun bank => project m (bank.get p.result))
  else some (project m (current.get p.result))

private theorem header_run (outer remaining : Nat) (old : Bank (regs := regs) m) :
    observeHeader p m outer remaining (p.header.eval m old) =
      (p.source.runFrom m (3 * remaining + 1) 1 old).map (project m) := by
  induction remaining generalizing old with
  | zero =>
    rw [p.source_header]
    let current := p.header.eval m old
    by_cases test : (current.get p.again).down = true
    · rw [show p.step m old = .inr ((current.get p.select).down,
          (p.feedback (current.get p.select).down).eval m current) from ite_eq_left test]
      simp only [observeHeader, show ((p.header.eval m old).get p.again).down = true from test, ite_true]
      rfl
    · rw [show p.step m old = .inl (current.get p.result) from ite_eq_right test]
      simp only [observeHeader, ite_eq_right (show ¬ ((p.header.eval m old).get p.again).down = true from test)]
      rfl
  | succ remaining ih =>
    rw [p.source_header]
    let current := p.header.eval m old
    by_cases test : (current.get p.again).down = true
    · let feedback := (p.feedback (current.get p.select).down).eval m current
      rw [show p.step m old = .inr ((current.get p.select).down, feedback) from ite_eq_left test]
      have visits : 3 * (remaining + 1) - 2 = 3 * remaining + 1 := by omega
      change _ = (p.source.runFrom m (3 * (remaining + 1) - 2) 1 feedback).map (project m)
      rw [visits, ← ih feedback]
      simp only [observeHeader, show ((p.header.eval m old).get p.again).down = true from test,
        ite_true, iterate, body_run]
      let next := p.header.eval m feedback
      change (if ((if (next.get p.again).down then (1 : Fin 2) else 0).val == 1) then
          iterate ((thetaBody p).run (model m) outer) (fun tag => tag.down.val == 1) remaining next
          else some next).map (fun bank => project m (bank.get p.result)) =
        if (next.get p.again).down then
          (iterate ((thetaBody p).run (model m) outer) (fun tag => tag.down.val == 1) remaining next).map
            (fun bank => project m (bank.get p.result))
        else some (project m (next.get p.result))
      cases (next.get p.again).down <;> rfl
    · rw [show p.step m old = .inl (current.get p.result) from ite_eq_right test]
      simp only [observeHeader, ite_eq_right (show ¬ ((p.header.eval m old).get p.again).down = true from test)]
      rfl

theorem lower_run (fuel : Nat) (input : Bank (regs := regs) m) :
    (lower p).run (model m) fuel input =
      (p.source.runFrom m (3 * fuel + 2) 0 input).map
        (fun value => (Tuple.cons value .nil : Tuple (Val m.value) [.value out])) := by
  have entry : (entryBlock p).eval m input = p.header.eval m (p.preheader.eval m input) := List.foldl_append
  rw [lower, GuardedTheta.lower_run, entry, p.source_entry]
  exact header_run p m fuel fuel (p.preheader.eval m input)

theorem returns_iff (input : Bank (regs := regs) m) (value : sortValue m.value out) :
    (lower p).Returns (model m) input (.cons value .nil) ↔
      ∃ fuel, p.source.runFrom m fuel 0 input = some value := by
  constructor
  · rintro ⟨fuel, returned⟩
    have mapped := (lower_run p m fuel input).symm.trans returned
    obtain ⟨actual, native, equal⟩ := Option.map_eq_some_iff.mp mapped
    exact ⟨3 * fuel + 2, native.trans (congrArg (fun tuple : Tuple (Val m.value) [.value out] =>
      some (tuple.get .head)) equal)⟩
  · rintro ⟨fuel, returned⟩
    refine ⟨fuel, (lower_run p m fuel input).trans ?_⟩
    exact Option.map_eq_some_iff.mpr ⟨value, Tail.Source.runFrom_mono m (by omega) returned, rfl⟩

theorem noReturn_iff (input : Bank (regs := regs) m) :
    (∀ fuel, (lower p).run (model m) fuel input = none) ↔
      ¬ ∃ value fuel, p.source.runFrom m fuel 0 input = some value := by
  constructor
  · rintro absent ⟨value, returned⟩
    obtain ⟨fuel, observed⟩ := (returns_iff p m input value).mpr returned
    rw [absent fuel] at observed
    cases observed
  · intro absent fuel
    rw [lower_run]
    cases observed : p.source.runFrom m (3 * fuel + 2) 0 input with
    | none => rfl
    | some value => exact (absent ⟨value, _, observed⟩).elim

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Numbered.Proofs

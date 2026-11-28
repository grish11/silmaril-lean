module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.GuardedTheta.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Join.Finite.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Join.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.Proofs

open SeaOfNodes.Diamond (Model Signature Val ValueSort dataPorts sortValue)
open SeaOfNodes.Diamond.SCCP (Fact TupleCovers)
open SeaOfNodes.Loop.SCCP (BankDecidableEq)
open RVSDG (Tuple)
open RVSDG.NestedTheta (Term Graph iterate)
open Join (Block model)
open Join.Finite (lastBank lastBank_read)
open Tail.Diamond (bodyPorts thenBase thenBase_eval)
open Blocks (Bank)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data}
variable {m : Model.{u, v, w} Op} {p : Program Op regs out} [BankDecidableEq m.value (dataPorts regs)]
variable {facts : Tuple (Fact m.value) (dataPorts regs)}

omit [BankDecidableEq m.value (dataPorts regs)] in
private theorem entry_eval (input : Bank (regs := regs) m) :
    (entryBlock p).eval m input = p.header.eval m (p.preheader.eval m input) :=
  List.foldl_append

private theorem activation_eval (checked : Checked m p facts) (bank : Bank (regs := regs) m) :
    (activation checked).eval m bank = p.header.eval m ((bypass checked 2).body.eval m bank) :=
  List.foldl_append

theorem thetaBody_run (checked : Checked m p facts) (fuel : Nat) (bank : Bank (regs := regs) m) :
    (thetaBody checked).run (model m) fuel bank =
      let next := (activation checked).eval m bank
      some (RVSDG.Theta.bodyResult (model m) (next.get p.again).down next) := by
  let packet (next : Bank (regs := regs) m) :=
    some (RVSDG.Theta.bodyResult (model m) (next.get p.again).down next)
  change (thenBase _ _).eval _ _ _ _ = packet ((activation checked).eval m bank)
  erw [thenBase_eval (observe := packet)]
  · have reads := Block.lowerFrom_eval (past := []) (activation checked) .jump m bank
      PUnit.unit (initial regs)
    rw [read_initial m] at reads
    exact congrArg packet reads
  · intro wires locals
    change some ((lastBank _ (bodyPorts regs)).read bank (locals.snoc
      ((model m).run (.route (.test p.again (.take 1) (.take 0))) (wires.read bank locals)))) = _
    rw [lastBank_read m, GuardedTheta.test_packet p.again]

private theorem bypass_header (checked : Checked m p facts) (fuel : Nat) (old : Bank (regs := regs) m) :
    (bypass checked).runFrom m (fuel + 1) 1 old =
      let next := p.header.eval m old
      if (next.get p.again).down then (bypass checked).runFrom m fuel 2 next else some (next.get p.result) := by
  simp only [Tail.Source.runFrom,
    show bypass checked 1 = ⟨p.header, .branch p.again (.jump 2) (.ret p.result)⟩ from rfl,
    Tail.Terminator.select]
  by_cases test : ((p.header.eval m old).get p.again).down = true <;> simp [test]

private theorem iterate_feedback (checked : Checked m p facts) (fuel θFuel : Nat) (bank : Bank (regs := regs) m) :
    (iterate ((thetaBody checked).run (model m) θFuel) (fun tag => tag.down.val == 1) fuel bank).map
      (fun done => Tuple.cons (done.get p.result) .nil) =
      ((bypass checked).runFrom m (2 * fuel) 2 bank).map (fun value => .cons value .nil) := by
  induction fuel generalizing bank with
  | zero => rfl
  | succ fuel ih =>
    have visits : 2 * (fuel + 1) = (2 * fuel + 1) + 1 := by omega
    rw [visits]
    change (iterate _ _ (fuel + 1) bank).map _ =
      ((bypass checked).runFrom m (2 * fuel + 1) 1 ((bypass checked 2).body.eval m bank)).map _
    rw [bypass_header, iterate, thetaBody_run, activation_eval]
    let next := p.header.eval m ((bypass checked 2).body.eval m bank)
    change (if ((if (next.get p.again).down then (1 : Fin 2) else 0).val == 1) then
        iterate ((thetaBody checked).run (model m) θFuel) (fun tag => tag.down.val == 1) fuel next
        else some next).map _ =
      (if (next.get p.again).down then (bypass checked).runFrom m (2 * fuel) 2 next
        else some (next.get p.result)).map _
    cases (next.get p.again).down
    · rfl
    · exact ih next

theorem lower_run (checked : Checked m p facts) (fuel : Nat) (input : Bank (regs := regs) m) :
    (lower checked).run (model m) fuel input =
      ((bypass checked).runFrom m (2 * fuel + 2) 0 input).map (fun value => .cons value .nil) := by
  change (GuardedTheta.lowerTerm (entryBlock p) p.again p.result (thetaBody checked)).toGraph.run
    (model m) fuel input = _
  rw [GuardedTheta.lower_run, entry_eval (p := p)]
  change _ = ((bypass checked).runFrom m (2 * fuel + 1) 1 (p.preheader.eval m input)).map _
  rw [bypass_header]
  let next := p.header.eval m (p.preheader.eval m input)
  by_cases test : (next.get p.again).down = true
  · simpa only [show ((p.header.eval m (p.preheader.eval m input)).get p.again).down = true from test,
      ite_true] using iterate_feedback checked fuel fuel next
  · have stopped : ((p.header.eval m (p.preheader.eval m input)).get p.again).down ≠ true := test
    simp only [ite_eq_right stopped]
    rfl

theorem lower_run_original (checked : Checked m p facts) {input : Bank (regs := regs) m}
    (covered : TupleCovers facts input) (fuel : Nat) :
    (lower checked).run (model m) fuel input =
      (p.source.runFrom m (3 * fuel + 2) 0 input).map (fun value => .cons value .nil) :=
  (lower_run checked fuel input).trans
    (congrArg (Option.map (fun value => (Tuple.cons value .nil : Tuple (Val m.value) [.value out])))
      ((Bypass.feedback_budget_eq checked covered fuel).trans (DeleteRoute.runFrom_eq checked covered _)))

theorem packet_run (checked : Checked m p facts) (fuel : Nat) (bank : Bank (regs := regs) m) :
    (thetaBody checked).toGraph.run (model m) fuel bank =
      let next := p.header.eval m ((bypass checked 2).body.eval m bank)
      some (RVSDG.Theta.bodyResult (model m) (next.get p.again).down next) := by
  rw [← Graph.run_toTerm, Term.toTerm_toGraph, thetaBody_run, activation_eval]

theorem lower_exit (checked : Checked m p facts) (fuel : Nat) (input : Bank (regs := regs) m)
    (stop : ((p.header.eval m (p.preheader.eval m input)).get p.again).down = false) :
    (lower checked).run (model m) fuel input =
      some (.cons ((p.header.eval m (p.preheader.eval m input)).get p.result) .nil) := by
  change (GuardedTheta.lowerTerm (entryBlock p) p.again p.result (thetaBody checked)).toGraph.run
    (model m) fuel input = _
  rw [GuardedTheta.lower_run, entry_eval (p := p)]
  simp [stop]

theorem run_count_iff (checked : Checked m p facts) {input : Bank (regs := regs) m}
    (covered : TupleCovers facts input) (fuel : Nat) (value : sortValue m.value out) :
    (lower checked).run (model m) fuel input = some (.cons value .nil) ↔
      ∃ n, ReturnsAfter p m n (p.preheader.eval m input) value ∧ n ≤ fuel := by
  rw [lower_run]
  have observed := run_bypass_iff checked covered (2 * fuel + 2) value
  constructor
  · intro returned
    obtain ⟨actual, native, equal⟩ := Option.map_eq_some_iff.mp returned
    have values : actual = value :=
      congrArg (fun packet : Tuple (Val m.value) [.value out] => packet.get .head) equal
    obtain ⟨n, trace, budget⟩ := observed.mp (values ▸ native)
    exact ⟨n, trace, by omega⟩
  · rintro ⟨n, trace, budget⟩
    exact Option.map_eq_some_iff.mpr ⟨value, observed.mpr ⟨n, trace, by omega⟩, rfl⟩

theorem returns_iff_original (checked : Checked m p facts) {input : Bank (regs := regs) m}
    (covered : TupleCovers facts input) (value : sortValue m.value out) :
    (lower checked).Returns (model m) input (.cons value .nil) ↔
      ∃ fuel, p.source.runFrom m fuel 0 input = some value := by
  constructor
  · rintro ⟨fuel, returned⟩
    obtain ⟨n, trace, _⟩ := (run_count_iff checked covered fuel value).mp returned
    have native := (run_compact_iff checked covered (3 * n + 2) value).mpr ⟨n, trace, Nat.le_refl _⟩
    exact ⟨3 * n + 2, (DeleteRoute.runFrom_eq checked covered _).symm.trans native⟩
  · rintro ⟨fuel, returned⟩
    have native := (DeleteRoute.runFrom_eq checked covered fuel).trans returned
    obtain ⟨n, trace, _⟩ := (run_compact_iff checked covered fuel value).mp native
    exact ⟨n, (run_count_iff checked covered n value).mpr ⟨n, trace, Nat.le_refl _⟩⟩

theorem no_return_iff_original (checked : Checked m p facts) {input : Bank (regs := regs) m}
    (covered : TupleCovers facts input) :
    (∀ fuel, (lower checked).run (model m) fuel input = none) ↔
      ¬ ∃ value fuel, p.source.runFrom m fuel 0 input = some value := by
  constructor
  · rintro absent ⟨value, returned⟩
    obtain ⟨fuel, observed⟩ := (returns_iff_original checked covered value).mpr returned
    rw [absent fuel] at observed
    cases observed
  · intro absent fuel
    cases observed : (lower checked).run (model m) fuel input with
    | none => rfl
    | some values =>
      cases values with
      | cons value tail =>
        cases tail
        exact (absent ⟨value, (returns_iff_original checked covered value).mp ⟨fuel, observed⟩⟩).elim

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.Proofs

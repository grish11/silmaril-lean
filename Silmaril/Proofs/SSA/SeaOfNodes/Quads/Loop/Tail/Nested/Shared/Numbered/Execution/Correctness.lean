module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Numbered.Execution.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Join.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Numbered.Execution.Proofs

open SeaOfNodes.Diamond (Val)
open RVSDG (Tuple)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond (thenBase_eval iterateThenReturnWith_eval)

open SeaOfNodes.Diamond (Model ValueSort sortValue dataPorts)
open RVSDG.NestedTheta (Term iterate)
open Join (Block Opcode model)
open Blocks (Bank)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond (bodyPorts thenBase iterateThenReturnWith)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}
variable (control : Control src entry) (m : Model.{u, v, w} Op)
variable (merge : Bank (regs := regs) m → Bank (regs := regs) m)
variable (routeVisits : Bank (regs := regs) m → Nat)

variable {bodySigs : List (List (SeaOfNodes.Diamond.Ty Data))}
variable (body : Term (Opcode Op) (dataPorts regs) [] bodySigs (bodyPorts regs))

variable (reachesJoin : ∀ old fuel,
  src.runFrom m (fuel + routeVisits old) control.header old = src.runFrom m fuel control.join (merge old))
variable (activation : ∀ fuel old,
  body.run (model m) fuel old =
    let next := nextBank control m merge old
    some (RVSDG.Theta.bodyResult (model m) (next.get control.again).down next))

private abbrev iter (bodyFuel fuel : Nat) (old : Bank (regs := regs) m) :=
  iterate (body.run (model m) bodyFuel) (fun tag => tag.down.val == 1) fuel old

private theorem lower_iterate (fuel : Nat) (input : Bank (regs := regs) m) :
    (lower control body).run (model m) fuel input =
      (iter m body fuel fuel ((src entry).body.eval m input)).map (fun bank => .cons (bank.get control.result) .nil) := by
  rw [lower, ← RVSDG.NestedTheta.Graph.run_toTerm, Term.toTerm_toGraph]
  unfold lowerTerm Term.run
  erw [thenBase_eval (observe := fun bank =>
    (iter m body fuel fuel bank).map (fun done => .cons (done.get control.result) .nil))]
  · erw [Block.lowerFrom_eval, read_initial]
    rfl
  · intro wires locals
    exact iterateThenReturnWith_eval m body control.result wires fuel input locals

include activation in
private theorem iter_step (bodyFuel fuel : Nat) (old : Bank (regs := regs) m) :
    iter m body bodyFuel (fuel + 1) old =
      let next := nextBank control m merge old
      if (next.get control.again).down then iter m body bodyFuel fuel next else some next := by
  unfold iter
  rw [iterate, activation]
  by_cases h : ((nextBank control m merge old).get control.again).down = true <;>
    simp [RVSDG.Theta.bodyResult, h] <;> rfl

include reachesJoin in
private theorem source_step (old : Bank (regs := regs) m) (fuel : Nat) :
    src.runFrom m (fuel + (routeVisits old + 2)) control.header old =
      let next := nextBank control m merge old
      if (next.get control.again).down then src.runFrom m fuel control.header next else some (next.get control.result) := by
  rw [← Nat.add_assoc, Nat.add_right_comm fuel (routeVisits old), reachesJoin old (fuel + 2)]
  simp only [Tail.Source.runFrom, control.joinEdge, control.latchEdge, Tail.Terminator.select]
  have nextEq : nextBank control m merge old =
      (src control.latch).body.eval m ((src control.join).body.eval m (merge old)) :=
    List.foldl_append
  rw [← nextEq]
  by_cases h : ((nextBank control m merge old).get control.again).down = true
  · simp only [ite_eq_left h]
  · simp only [ite_eq_right h]

private theorem run_entry (input : Bank (regs := regs) m) (fuel : Nat) :
    src.runFrom m (fuel + 1) entry input =
      src.runFrom m fuel control.header ((src entry).body.eval m input) := by
  simp only [Tail.Source.runFrom, control.entryEdge, Tail.Terminator.select]

include reachesJoin activation in
private theorem source_at_activations (bodyFuel fuel : Nat) (old : Bank (regs := regs) m) :
    src.runFrom m (visitsFrom control m merge routeVisits fuel old) control.header old =
      (iter m body bodyFuel fuel old).map (fun bank => bank.get control.result) := by
  induction fuel generalizing old with
  | zero => rfl
  | succ fuel ih =>
    rw [visitsFrom, source_step control m merge routeVisits reachesJoin, iter_step control m merge body activation]
    by_cases h : ((nextBank control m merge old).get control.again).down = true
    · simpa only [ite_eq_left h] using ih (nextBank control m merge old)
    · simp only [ite_eq_right h]; rfl

include reachesJoin activation in
theorem lower_run (fuel : Nat) (input : Bank (regs := regs) m) :
    (lower control body).run (model m) fuel input =
      (src.runFrom m (sourceVisits control m merge routeVisits fuel input) entry input).map (fun value => .cons value .nil) := by
  rw [lower_iterate, sourceVisits, run_entry,
    source_at_activations control m merge routeVisits body reachesJoin activation (bodyFuel := fuel)]
  erw [Option.map_map]
  rfl

include reachesJoin in
private theorem source_short (old : Bank (regs := regs) m) (fuel : Nat)
    (short : fuel < (routeVisits old + 2)) : src.runFrom m fuel control.header old = none := by
  let beforeLatch := 1 + routeVisits old
  have atLimit : src.runFrom m beforeLatch control.header old = none := by
    unfold beforeLatch
    rw [reachesJoin old 1]
    simp only [Tail.Source.runFrom, control.joinEdge, Tail.Terminator.select]
  cases returned : src.runFrom m fuel control.header old with
  | none => rfl
  | some value =>
    have fits : fuel ≤ beforeLatch := by dsimp [beforeLatch] at *; omega
    have extended := Tail.Source.runFrom_mono m fits returned
    rw [atLimit] at extended
    cases extended

include reachesJoin activation in
private theorem iter_complete (old : Bank (regs := regs) m) (fuel : Nat) (value : sortValue m.value out)
    (returned : src.runFrom m fuel control.header old = some value) :
    ∃ bound, ∀ bodyFuel, (iter m body bodyFuel bound old).map (fun bank => bank.get control.result) = some value := by
  let cost := (routeVisits old + 2)
  by_cases enough : cost ≤ fuel
  · have stepped := source_step control m merge routeVisits reachesJoin old (fuel - cost)
    change src.runFrom m (fuel - cost + cost) control.header old = _ at stepped
    rw [Nat.sub_add_cancel enough] at stepped
    rw [stepped] at returned
    by_cases h : ((nextBank control m merge old).get control.again).down = true
    · simp only [ite_eq_left h] at returned
      obtain ⟨bound, rest⟩ := iter_complete (nextBank control m merge old) (fuel - cost) value returned
      exact ⟨bound + 1, fun bodyFuel => by simpa only [iter_step control m merge body activation, ite_eq_left h] using rest bodyFuel⟩
    · rw [ite_eq_right h] at returned
      refine ⟨1, ?_⟩
      intro bodyFuel
      rw [iter_step control m merge body activation, ite_eq_right h]
      exact returned
  · rw [source_short control m merge routeVisits reachesJoin old fuel (Nat.lt_of_not_ge enough)] at returned
    cases returned
termination_by fuel
decreasing_by
  unfold cost at *
  omega

include reachesJoin activation in
theorem returns_iff (input : Bank (regs := regs) m) (value : sortValue m.value out) :
    (lower control body).Returns (model m) input (.cons value .nil) ↔
      ∃ fuel, src.runFrom m fuel entry input = some value := by
  constructor
  · rintro ⟨bound, returned⟩
    rw [lower_run control m merge routeVisits body reachesJoin activation] at returned
    obtain ⟨word, run, same⟩ := Option.map_eq_some_iff.mp returned
    have sameWord := congrArg (fun packet : Tuple (Val m.value) [.value out] => packet.get .head) same
    exact ⟨_, run.trans (congrArg some sameWord)⟩
  · rintro ⟨_ | fuel, returned⟩
    · cases returned
    · rw [run_entry] at returned
      obtain ⟨bound, finished⟩ := iter_complete control m merge routeVisits body reachesJoin activation _ fuel value returned
      refine ⟨bound, ?_⟩
      rw [lower_iterate]
      have wrapped :=
        congrArg (Option.map (fun word => Tuple.cons (F := Val m.value) (t := .value out) word .nil)) (finished bound)
      rw [Option.map_map] at wrapped
      exact wrapped

include reachesJoin activation in
theorem noFiniteReturn_iff (input : Bank (regs := regs) m) :
    (∀ fuel, (lower control body).run (model m) fuel input = none) ↔
      ∀ fuel, src.runFrom m fuel entry input = none := by
  constructor
  · intro absent fuel
    cases returned : src.runFrom m fuel entry input with
    | none => rfl
    | some value =>
      obtain ⟨bound, native⟩ := (returns_iff control m merge routeVisits body reachesJoin activation input value).mpr ⟨fuel, returned⟩
      rw [absent] at native
      cases native
  · intro absent fuel
    rw [lower_run control m merge routeVisits body reachesJoin activation, absent]
    rfl

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Numbered.Execution.Proofs

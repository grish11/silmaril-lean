module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Numbered.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Prune.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Join.Finite.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Join.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Numbered.Proofs

open SeaOfNodes.Diamond (Model Ty Val ValueSort dataPorts sortValue)
open RVSDG (Locals Tuple Wires extend)
open RVSDG.NestedTheta (Term Kind iterate)
open Join (Block Opcode model)
open Join.Finite (Plan Stage lastBank lastBank_read)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond (bodyPorts thenBase_eval)
open Diamond.Prune (HeaderProjection lowerFlow_eval routeProjectedWith_eval thetaThenReturn_eval)
open Blocks (Bank)
open Blocks.Prune (Mask)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}
variable (p : Program src entry) (m : Model.{u, v, w} Op)

private theorem inner_run (fuel : Nat) (header : Bank (regs := regs) m) :
    (innerRegion p).run (model m) fuel header =
      some ((innerPlan p).eval m ((src p.inner).body.eval m header)) := by
  unfold innerRegion Term.run
  erw [thenBase_eval (observe := fun bank => some ((innerPlan p).eval m bank))]
  · erw [Block.lowerFrom_eval, read_initial]
    rfl
  · intro wires locals
    erw [thenBase_eval (observe := some), Plan.lowerFrom_eval]
    intro _ _
    rfl

theorem outerArm_run (fuel : Nat) (bank : Bank (regs := regs) m) :
    (outerArm p ((outerChoice p).eval bank)).run (model m) fuel bank =
      some (branchBank p m bank) := by
  by_cases yes : (bank.get p.outerTest).down = true
  · have chosen : (outerChoice p).eval bank = 0 := by simp [outerChoice, Join.Choice.eval, yes]
    rw [chosen, branchBank, ite_eq_left yes]
    exact inner_run p m fuel bank
  · have chosen : (outerChoice p).eval bank = 1 := by simp [outerChoice, Join.Choice.eval, yes]
    rw [chosen, branchBank, ite_eq_right yes]
    change (Term.ofBase (p.outerFalse.quads.lowerFrom (initial regs) .jump)).run (model m) fuel bank = _
    rw [Term.run_ofBase]
    unfold RVSDG.Term.run
    erw [Block.lowerFrom_eval, read_initial]
    rfl

theorem linkGamma_eval {args outputs results : List (Ty Data)} {past suffix : List (List (Ty Data))}
    (choice : Join.Choice regs 2) (sigs : Fin 2 → List (List (Ty Data)))
    (arms : (i : Fin 2) → Term (Opcode Op) (dataPorts regs) [] (sigs i) outputs)
    (current : Wires args past (dataPorts regs))
    (finish : Wires args (extend past [routePorts regs, outputs]) outputs →
      Term (Opcode Op) args (extend past [routePorts regs, outputs]) suffix results)
    (fuel : Nat) (input : Tuple (Val m.value) args) (locals : Locals (Val m.value) past)
    (selected : Bank (regs := regs) m → Tuple (Val m.value) outputs)
    (arm_agrees : ∀ bank, (arms (choice.eval bank)).run (model m) fuel bank = some (selected bank))
    (observe : Tuple (Val m.value) outputs → Option (Tuple (Val m.value) results))
    (agrees : ∀ wires locals', (finish wires).eval (model m) fuel input locals' =
      observe (wires.read input locals')) :
    (linkGamma choice sigs arms current finish).eval (model m) fuel input locals =
      observe (selected (current.read input locals)) := by
  let bank := current.read input locals
  let tagged := (model m).run (.route choice) bank
  let frames := locals.snoc tagged
  change (Kind.eval (model m) fuel (.base (.gamma 0) : Kind (Opcode Op) (routePorts regs) outputs)
    (fun i value => (arms i).run (model m) fuel value)
    ((lastBank past (routePorts regs)).read input frames)).bind
      (fun merged => (finish (lastBank (past ++ [routePorts regs]) outputs)).eval
        (model m) fuel input (frames.snoc merged)) = _
  rw [lastBank_read m]
  change ((arms (choice.eval bank)).run (model m) fuel bank).bind _ = _
  rw [arm_agrees]
  change (finish _).eval (model m) fuel input (frames.snoc (selected bank)) = _
  exact (agrees _ _).trans (congrArg observe (lastBank_read m input frames (selected bank)))

theorem afterOuterWith_eval {args outputs results : List (Ty Data)} {past suffix : List (List (Ty Data))}
    (arms : (i : Fin 2) → Term (Opcode Op) (dataPorts regs) [] (outerSigs p i) outputs)
    (current : Wires args past (dataPorts regs))
    (finish : Wires args (extend past [routePorts regs, outputs]) outputs →
      Term (Opcode Op) args (extend past [routePorts regs, outputs]) suffix results)
    (fuel : Nat) (input : Tuple (Val m.value) args) (locals : Locals (Val m.value) past)
    (selected : Bank (regs := regs) m → Tuple (Val m.value) outputs)
    (arm_agrees : ∀ bank, (arms ((outerChoice p).eval bank)).run (model m) fuel bank = some (selected bank))
    (observe : Tuple (Val m.value) outputs → Option (Tuple (Val m.value) results))
    (agrees : ∀ wires locals', (finish wires).eval (model m) fuel input locals' =
      observe (wires.read input locals')) :
    (afterOuterWith p arms current finish).eval (model m) fuel input locals =
      observe (selected (current.read input locals)) :=
  linkGamma_eval m (outerChoice p) (outerSigs p) arms current finish fuel input locals selected arm_agrees observe agrees

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
  afterOuterWith_eval p m (outerArm p) current finish fuel input locals
    (branchBank p m) (outerArm_run p m fuel) observe agrees

theorem branchBank_agrees (old : Bank (regs := regs) m) :
    branchBank p m ((src p.header).body.eval m old) =
      p.mergeBank m old (p.selected m old) := by
  let outer := (src p.header).body.eval m old
  let inner := (src p.inner).body.eval m outer
  have selection : p.selected m old =
      if (outer.get p.outerTest).down then
        if (inner.get p.innerTest).down then .innerTrue else .innerFalse
      else .outerFalse := rfl
  rw [p.merge_bank, selection]
  change (if (outer.get p.outerTest).down then (innerPlan p).eval m inner
    else p.outerFalse.quads.eval m outer) = _
  by_cases yes : (outer.get p.outerTest).down = true
  · simp only [ite_eq_left yes]
    by_cases innerYes : (inner.get p.innerTest).down = true
    · rw [ite_eq_left innerYes]
      simp only [innerPlan, Plan.eval, List.foldl_cons, List.foldl_nil, Stage.eval, Stage.table,
        Join.Choice.eval, ite_eq_left innerYes]
      simp only [Program.pathQuads, Program.arm, Block.eval, List.foldl_append, outer, inner]; rfl
    · rw [ite_eq_right innerYes]
      simp only [innerPlan, Plan.eval, List.foldl_cons, List.foldl_nil, Stage.eval, Stage.table,
        Join.Choice.eval, ite_eq_right innerYes]
      simp only [Program.pathQuads, Program.arm, Block.eval, List.foldl_append, outer, inner]; rfl
  · simp only [ite_eq_right yes]
    simp only [Program.pathQuads, Program.arm, Block.eval, List.foldl_append, outer]; rfl

variable {mask : Mask regs} (projected : HeaderProjection (src p.header).body mask)

theorem merge_run (fuel : Nat) (old : Bank (regs := regs) m) :
    (mergeRegion p projected).toGraph.run (model m) fuel (mask.project old) =
      some (p.mergeBank m old (p.selected m old)) := by
  rw [← RVSDG.NestedTheta.Graph.run_toTerm, Term.toTerm_toGraph]
  unfold mergeRegion Term.run
  erw [thenBase_eval (observe := fun bank => some (branchBank p m bank))]
  · erw [lowerFlow_eval]
    change some (branchBank p m (projected.headerBank m (mask.project old))) = _
    rw [projected.header_agrees, branchBank_agrees]
  · intro current locals
    exact afterOuter_eval p m current .ret fuel (mask.project old) locals some
      (fun _ _ => rfl)

theorem activation_run (fuel : Nat) (old : Bank (regs := regs) m) :
    (thetaBody p projected).run (model m) fuel (mask.project old) =
      let next := nextBank p m old
      some (RVSDG.Theta.bodyResult (model m) (next.get p.again).down (mask.project next)) := by
  let packet (bank : Bank (regs := regs) m) :=
    some (RVSDG.Theta.bodyResult (model m) (bank.get p.again).down (mask.project bank))
  unfold thetaBody Term.run
  erw [thenBase_eval (observe := fun bank => packet ((tail p).eval m (branchBank p m bank)))]
  · erw [lowerFlow_eval]
    change packet ((tail p).eval m (branchBank p m (projected.headerBank m (mask.project old)))) = _
    rw [projected.header_agrees, branchBank_agrees]
    rfl
  · intro current locals
    apply afterOuter_eval p m current _ fuel (mask.project old) locals
      (fun bank => packet ((tail p).eval m bank))
    intro merged locals'
    erw [thenBase_eval (observe := packet), Block.lowerFrom_eval]
    · rfl
    · intro wires later
      exact routeProjectedWith_eval m p.again wires fuel (mask.project old) later

private abbrev iterBody (old : Bank (regs := regs) m) :=
  let next := nextBank p m old
  some (RVSDG.Theta.bodyResult (model m) (next.get p.again).down next)

private abbrev iter (fuel : Nat) (old : Bank (regs := regs) m) :=
  iterate (iterBody p m) (fun tag => tag.down.val == 1) fuel old

private theorem iter_step (fuel : Nat) (old : Bank (regs := regs) m) :
    iter p m (fuel + 1) old =
      let next := nextBank p m old
      if (next.get p.again).down then iter p m fuel next else some next := by
  unfold iter
  rw [iterate]
  by_cases h : ((nextBank p m old).get p.again).down = true <;>
    simp [iterBody, RVSDG.Theta.bodyResult, h] <;> rfl

variable {bodySigs : List (List (Ty Data))}
variable (body : Term (Opcode Op) (dataPorts mask.kept) [] bodySigs (bodyPorts mask.kept))

private theorem iter_project
    (activation : ∀ fuel old, body.run (model m) fuel (mask.project old) =
      let next := nextBank p m old
      some (RVSDG.Theta.bodyResult (model m) (next.get p.again).down (mask.project next)))
    (bodyFuel fuel : Nat) (old : Bank (regs := regs) m) :
    iterate (body.run (model m) bodyFuel) (fun tag => tag.down.val == 1)
        fuel (mask.project old) =
      (iter p m fuel old).map mask.project := by
  induction fuel generalizing old with
  | zero => rfl
  | succ fuel ih =>
    rw [iter_step]
    simp only [iterate, activation, RVSDG.Theta.bodyResult]
    by_cases h : ((nextBank p m old).get p.again).down = true
    · simp [h]
      exact ih (nextBank p m old)
    · simp [h]; rfl

private theorem graph_iterate (result : KeptResult p (mask := mask))
    (fuel : Nat) (input : Bank (regs := regs) m) :
    (lowerWith p result body).run (model m) fuel input =
      (iterate (body.run (model m) fuel) (fun tag => tag.down.val == 1)
        fuel (mask.project ((src entry).body.eval m input))).map (fun bank => .cons (bank.get result.val) .nil) := by
  rw [lowerWith, ← RVSDG.NestedTheta.Graph.run_toTerm, Term.toTerm_toGraph]
  unfold lowerTermWith Term.run
  erw [thenBase_eval (observe := fun bank =>
    (iterate (body.run (model m) fuel) (fun tag => tag.down.val == 1)
      fuel (mask.project bank)).map (fun done => .cons (done.get result.val) .nil))]
  · erw [Block.lowerFrom_eval, read_initial]
    rfl
  · intro wires locals
    exact thetaThenReturn_eval m body result.val wires fuel input locals

private theorem lowerWith_iterate
    (activation : ∀ fuel old, body.run (model m) fuel (mask.project old) =
      let next := nextBank p m old
      some (RVSDG.Theta.bodyResult (model m) (next.get p.again).down (mask.project next)))
    (result : KeptResult p (mask := mask))
    (fuel : Nat) (input : Bank (regs := regs) m) :
    (lowerWith p result body).run (model m) fuel input =
      (iter p m fuel ((src entry).body.eval m input)).map (fun bank => .cons (bank.get p.result) .nil) := by
  rw [graph_iterate, iter_project _ _ _ activation]
  cases iter p m fuel ((src entry).body.eval m input) with
  | none => rfl
  | some bank =>
    exact congrArg (fun x => some (Tuple.cons (F := Val m.value) (t := .value out) x .nil))
      (mask.project_get bank p.result result.val result.property)

private theorem lower_iterate (result : KeptResult p (mask := mask))
    (fuel : Nat) (input : Bank (regs := regs) m) :
    (lower p projected result).run (model m) fuel input =
      (iter p m fuel ((src entry).body.eval m input)).map (fun bank => .cons (bank.get p.result) .nil) :=
  lowerWith_iterate p m (thetaBody p projected) (activation_run p m projected) result fuel input

private theorem source_step (old : Bank (regs := regs) m) (fuel : Nat) :
    src.runFrom m (fuel + (p.mergeVisits (p.selected m old) + 2)) p.header old =
      let next := nextBank p m old
      if (next.get p.again).down then src.runFrom m fuel p.header next else some (next.get p.result) := by
  rw [show fuel + (p.mergeVisits (p.selected m old) + 2) =
      (fuel + 2) + p.mergeVisits (p.selected m old) by omega, p.run_to_merge m old (fuel + 2)]
  simp only [Tail.Source.runFrom, p.joinEdge, p.latchEdge, Tail.Terminator.select]
  have nextEq : nextBank p m old =
      (src p.latch).body.eval m ((src p.join).body.eval m (p.mergeBank m old (p.selected m old))) :=
    List.foldl_append
  rw [← nextEq]
  by_cases h : ((nextBank p m old).get p.again).down = true
  · simp only [ite_eq_left h]
  · simp only [ite_eq_right h]

private theorem run_entry (input : Bank (regs := regs) m) (fuel : Nat) :
    src.runFrom m (fuel + 1) entry input =
      src.runFrom m fuel p.header ((src entry).body.eval m input) := by
  simp only [Tail.Source.runFrom, p.entryEdge, Tail.Terminator.select]

private theorem source_at_activations (old : Bank (regs := regs) m) (fuel : Nat) :
    src.runFrom m (visitsFrom p m fuel old) p.header old =
      (iter p m fuel old).map (fun bank => bank.get p.result) := by
  induction fuel generalizing old with
  | zero => rfl
  | succ fuel ih =>
    rw [visitsFrom, source_step, iter_step]
    by_cases h : ((nextBank p m old).get p.again).down = true
    · simpa only [ite_eq_left h] using ih (nextBank p m old)
    · simp only [ite_eq_right h]; rfl

theorem lowerWith_run
    (activation : ∀ fuel old, body.run (model m) fuel (mask.project old) =
      let next := nextBank p m old
      some (RVSDG.Theta.bodyResult (model m) (next.get p.again).down (mask.project next)))
    (result : KeptResult p (mask := mask)) (fuel : Nat) (input : Bank (regs := regs) m) :
    (lowerWith p result body).run (model m) fuel input =
      (src.runFrom m (sourceVisits p m fuel input) entry input).map (fun value => .cons value .nil) := by
  rw [lowerWith_iterate p m body activation, sourceVisits, run_entry, source_at_activations]
  erw [Option.map_map]
  rfl

theorem lower_run (result : KeptResult p (mask := mask)) (fuel : Nat) (input : Bank (regs := regs) m) :
    (lower p projected result).run (model m) fuel input =
      (src.runFrom m (sourceVisits p m fuel input) entry input).map (fun value => .cons value .nil) :=
  lowerWith_run p m (thetaBody p projected) (activation_run p m projected) result fuel input

private theorem extend_return (extra fuel : Nat) (id : Fin size) (old : Bank (regs := regs) m)
    (value : sortValue m.value out) (h : src.runFrom m fuel id old = some value) :
    src.runFrom m (fuel + extra) id old = some value := by
  induction fuel generalizing id old with
  | zero => cases h
  | succ fuel ih =>
    rw [Nat.succ_add]
    simp only [Tail.Source.runFrom] at h ⊢
    generalize (src id).terminator.select m ((src id).body.eval m old) = destination at h ⊢
    cases destination with
    | jump target => exact ih target _ h
    | ret port => exact h

private theorem source_short (old : Bank (regs := regs) m) (fuel : Nat)
    (short : fuel < p.mergeVisits (p.selected m old) + 2) :
    src.runFrom m fuel p.header old = none := by
  let beforeLatch := 1 + p.mergeVisits (p.selected m old)
  have atLimit : src.runFrom m beforeLatch p.header old = none := by
    unfold beforeLatch
    rw [p.run_to_merge m old 1]
    simp only [Tail.Source.runFrom, p.joinEdge, Tail.Terminator.select]
  cases returned : src.runFrom m fuel p.header old with
  | none => rfl
  | some value =>
    have extended := extend_return m (beforeLatch - fuel) fuel p.header old value returned
    have fits : fuel ≤ beforeLatch := by dsimp [beforeLatch]; omega
    rw [Nat.add_sub_of_le fits, atLimit] at extended
    cases extended

private theorem iter_complete (old : Bank (regs := regs) m) (fuel : Nat) (value : sortValue m.value out)
    (returned : src.runFrom m fuel p.header old = some value) :
    ∃ bound, (iter p m bound old).map (fun bank => bank.get p.result) = some value := by
  let cost := p.mergeVisits (p.selected m old) + 2
  by_cases enough : cost ≤ fuel
  · have stepped := source_step p m old (fuel - cost)
    change src.runFrom m (fuel - cost + cost) p.header old = _ at stepped
    rw [Nat.sub_add_cancel enough] at stepped
    rw [stepped] at returned
    by_cases h : ((nextBank p m old).get p.again).down = true
    · simp only [ite_eq_left h] at returned
      obtain ⟨bound, rest⟩ := iter_complete (nextBank p m old) (fuel - cost) value returned
      exact ⟨bound + 1, by simpa only [iter_step, ite_eq_left h] using rest⟩
    · rw [ite_eq_right h] at returned
      refine ⟨1, ?_⟩
      rw [iter_step, ite_eq_right h]
      exact returned
  · rw [source_short p m old fuel (Nat.lt_of_not_ge enough)] at returned
    cases returned
termination_by fuel
decreasing_by
  omega

theorem returns_iff (result : KeptResult p (mask := mask)) (input : Bank (regs := regs) m)
    (value : sortValue m.value out) :
    (lower p projected result).Returns (model m) input (.cons value .nil) ↔
      ∃ fuel, src.runFrom m fuel entry input = some value := by
  constructor
  · rintro ⟨bound, returned⟩
    rw [lower_run] at returned
    obtain ⟨word, run, same⟩ := Option.map_eq_some_iff.mp returned
    have sameWord := congrArg (fun packet : Tuple (Val m.value) [.value out] => packet.get .head) same
    exact ⟨_, run.trans (congrArg some sameWord)⟩
  · rintro ⟨_ | fuel, returned⟩
    · cases returned
    · rw [run_entry] at returned
      obtain ⟨bound, native⟩ := iter_complete p m _ fuel value returned
      refine ⟨bound, ?_⟩
      rw [lower_iterate]
      have wrapped :=
        congrArg (Option.map (fun word => Tuple.cons (F := Val m.value) (t := .value out) word .nil)) native
      rw [Option.map_map] at wrapped
      exact wrapped
end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Numbered.Proofs

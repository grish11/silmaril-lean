module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Join.Finite.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Chain.Segment.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Join.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Proofs

open SeaOfNodes.Diamond (Model ValueSort Ty Val dataPorts sortValue)
open RVSDG (Dialect PortType Wires Tuple Locals extend)
open RVSDG.NestedTheta (Term Kind iterate)
open Join (Block Opcode model)
open Join.Finite (Stage Plan Table lastBank lastBank_read)
open Blocks (Bank)

universe u v w

section Prefix

variable {V S : Type u} {Φ : Dialect.{u, v} V S}
variable {args bank outs : List (PortType V S)} {past frontSigs suffix : List (List (PortType V S))}

private theorem eval_base (m : RVSDG.Model.{u, v, w} Φ) (fuel : Nat)
    {ins head : List (PortType V S)} (shape : RVSDG.Shape Φ ins head)
    (sigs : Fin shape.regionCount → List (List (PortType V S)))
    (children : (i : Fin shape.regionCount) → RVSDG.Term Φ shape.entry [] (sigs i) shape.exit)
    (input : Tuple m.Val ins) :
    (Kind.base shape).eval m fuel (fun i x => (Term.ofBase (children i)).run m fuel x) input =
      some (shape.eval m (fun i x => (children i).run m x) input) := by
  cases shape with
  | simple => rfl
  | gamma n =>
    cases input with
    | cons tag args => exact Term.run_ofBase (children tag.down) m fuel args

theorem thenBase_eval (m : RVSDG.Model.{u, v, w} Φ) (fuel : Nat)
    (t : RVSDG.Term Φ args past frontSigs bank)
    (next : Wires args (extend past frontSigs) bank → Term Φ args (extend past frontSigs) suffix outs)
    (entry : Tuple m.Val args) (locals : Locals m.Val past)
    (observe : Tuple m.Val bank → Option (Tuple m.Val outs))
    (agrees : ∀ wires locals', (next wires).eval m fuel entry locals' = observe (wires.read entry locals')) :
    (thenBase t next).eval m fuel entry locals = observe (t.eval m entry locals) := by
  induction t with
  | ret wires => exact agrees wires locals
  | bind node children rest _ ih =>
    rw [thenBase, Term.eval, RVSDG.Term.eval]
    erw [eval_base m fuel node.shape node.childSigs children]
    exact ih next entry (locals.snoc (node.shape.eval m (fun i x => (children i).run m x)
      (node.inputs.read entry locals))) observe agrees

end Prefix

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}
variable (p : Program src entry) (m : Model.{u, v, w} Op)

theorem afterHeader_eval {args results : List (Ty Data)} {past suffix : List (List (Ty Data))}
    (current : Wires args past (dataPorts regs))
    (finish : Wires args (extend (extend past p.plan.producers) p.tail.producers) (dataPorts regs) →
      Term (Opcode Op) args (extend (extend past p.plan.producers) p.tail.producers) suffix results)
    (fuel : Nat) (input : Tuple (Val m.value) args) (locals : Locals (Val m.value) past)
    (observe : Bank (regs := regs) m → Option (Tuple (Val m.value) results))
    (agrees : ∀ wires locals', (finish wires).eval (model m) fuel input locals' =
      observe (wires.read input locals')) :
    (p.afterHeader current finish).eval (model m) fuel input locals =
      observe (p.tail.eval m (p.stage.eval m (current.read input locals))) := by
  unfold Program.afterHeader
  erw [thenBase_eval (observe := fun bank => observe (p.tail.eval m bank))]
  · erw [Plan.lowerFrom_eval]
    rfl
  · intro merged locals'
    erw [thenBase_eval (observe := observe) (agrees := agrees), Block.lowerFrom_eval]
    rfl

private theorem latch_model_with (again : RVSDG.Port (dataPorts regs) (.value .predicate))
    (bank : Bank (regs := regs) m) :
    (model m).run (.route (.test again (.take 1) (.take 0))) bank =
      RVSDG.Theta.bodyResult (model m) (bank.get again).down bank := by
  by_cases h : (bank.get again).down = true <;>
    simp [model, Join.Choice.eval, RVSDG.Theta.bodyResult, h]

theorem latch_model (bank : Bank (regs := regs) m) :
    (model m).run (.route (.test p.again (.take 1) (.take 0))) bank =
      RVSDG.Theta.bodyResult (model m) (bank.get p.again).down bank :=
  latch_model_with m p.again bank

theorem routeLatchWith_eval {args : List (Ty Data)} {past : List (List (Ty Data))}
    (again : RVSDG.Port (dataPorts regs) (.value .predicate)) (wires : Wires args past (dataPorts regs))
    (fuel : Nat) (input : Tuple (Val m.value) args) (locals : Locals (Val m.value) past) :
    (routeLatchWith again wires).eval (model m) fuel input locals =
      some (RVSDG.Theta.bodyResult (model m) ((wires.read input locals).get again).down
        (wires.read input locals)) := by
  let bank := wires.read input locals
  change some ((lastBank past (bodyPorts regs)).read input (locals.snoc
    ((model m).run (.route (.test again (.take 1) (.take 0))) bank))) = _
  rw [lastBank_read m, latch_model_with m]

theorem body_run (fuel : Nat) (old : Bank (regs := regs) m) :
    p.thetaBody.run (model m) fuel old =
      some (RVSDG.Theta.bodyResult (model m) ((p.nextBank m old).get p.again).down (p.nextBank m old)) := by
  let route (bank : Bank (regs := regs) m) :=
    some (RVSDG.Theta.bodyResult (model m) (bank.get p.again).down bank)
  change (thenBase _ _).eval _ _ _ _ = route (p.nextBank m old)
  erw [thenBase_eval (observe := fun bank => route (p.tail.eval m (p.stage.eval m bank)))]
  · erw [Block.lowerFrom_eval, read_initial]
    rfl
  · intro header locals
    exact afterHeader_eval p m header p.routeLatch fuel old locals route
      (fun wires locals' => routeLatchWith_eval m p.again wires fuel old locals')

theorem iterateThenReturnWith_eval {past sigs : List (List (Ty Data))}
    (body : Term (Opcode Op) (dataPorts regs) [] sigs (bodyPorts regs))
    (result : RVSDG.Port (dataPorts regs) (.value out)) (wires : Wires (dataPorts regs) past (dataPorts regs))
    (fuel : Nat) (input : Bank (regs := regs) m) (locals : Locals (Val m.value) past) :
    (iterateThenReturnWith body result wires).eval (model m) fuel input locals =
      (iterate (body.run (model m) fuel) (fun tag => tag.down.val == 1) fuel (wires.read input locals)).map
        (fun bank => .cons (bank.get result) .nil) := by
  let executed := iterate (body.run (model m) fuel) (fun tag => tag.down.val == 1) fuel (wires.read input locals)
  change executed.bind (fun bank => some
    (Tuple.cons (SeaOfNodes.Diamond.read m ((lastBank past (dataPorts regs)).get result)
      input (locals.snoc bank)) .nil)) = executed.map (fun bank => .cons (bank.get result) .nil)
  cases executed with
  | none => rfl
  | some bank =>
    change some (Tuple.cons (SeaOfNodes.Diamond.read m ((lastBank past (dataPorts regs)).get result)
      input (locals.snoc bank)) .nil) = _
    rw [← read_get, lastBank_read m]
    rfl

private abbrev iterateBody (old : Bank (regs := regs) m) :=
  some (RVSDG.Theta.bodyResult (model m) ((p.nextBank m old).get p.again).down (p.nextBank m old))

private theorem iterate_return_eval {past : List (List (Ty Data))}
    (wires : Wires (dataPorts regs) past (dataPorts regs))
    (fuel : Nat) (input : Bank (regs := regs) m) (locals : Locals (Val m.value) past) :
    (p.iterateThenReturn wires).eval (model m) fuel input locals =
      (iterate (iterateBody p m) (fun tag => tag.down.val == 1) fuel (wires.read input locals)).map
        (fun bank => .cons (bank.get p.result) .nil) := by
  rw [Program.iterateThenReturn, iterateThenReturnWith_eval,
    show p.thetaBody.run (model m) fuel = iterateBody p m from funext (body_run p m fuel)] <;> rfl

private theorem graph_run (fuel : Nat) (input : Bank (regs := regs) m) :
    p.lower.run (model m) fuel input =
      (iterate (iterateBody p m) (fun tag => tag.down.val == 1) fuel ((src entry).body.eval m input)).map
        (fun bank => .cons (bank.get p.result) .nil) := by
  rw [Program.lower, ← RVSDG.NestedTheta.Graph.run_toTerm, Term.toTerm_toGraph]
  unfold Program.lowerTerm Term.run
  erw [thenBase_eval (observe := fun bank =>
    (iterate (iterateBody p m) (fun tag => tag.down.val == 1) fuel bank).map
      (fun done => .cons (done.get p.result) .nil))]
  · erw [Block.lowerFrom_eval, read_initial]
    rfl
  · intro wires locals
    exact iterate_return_eval p m wires fuel input locals

theorem lower_iterate (fuel : Nat) (input : Bank (regs := regs) m) :
    p.lower.run (model m) fuel input =
      (iterate (p.thetaBody.run (model m) fuel) (fun tag => tag.down.val == 1)
        fuel ((src entry).body.eval m input)).map (fun bank => .cons (bank.get p.result) .nil) := by
  rw [show p.thetaBody.run (model m) fuel = iterateBody p m from funext (body_run p m fuel)]
  exact graph_run p m fuel input


theorem arm_body (occurrence : Fin 2) :
    p.stage.table.get occurrence = (p.armPath occurrence).quads := by
  refine Fin.cases rfl (fun i => ?_) occurrence
  have zero : i = 0 := Fin.ext (by
    have bound := i.isLt
    omega)
  subst i
  rfl

theorem selected_start (bank : Bank (regs := regs) m) :
    p.armStart (p.stage.choice.eval bank) =
      (if (bank.get p.condition).down then p.onTrue else p.onFalse) := by
  by_cases h : (bank.get p.condition).down = true <;>
    simp [Program.armStart, Program.stage, Join.Choice.eval, h] <;> rfl

theorem selected_predecessor (bank : Bank (regs := regs) m) :
    p.predecessor (p.stage.choice.eval bank) =
      (if (bank.get p.condition).down then p.trueArm.predecessor p.header
        else p.falseArm.predecessor p.header) := by
  by_cases h : (bank.get p.condition).down = true
  · have chosen : p.stage.choice.eval bank = (0 : Fin 2) := by
      simp [Program.stage, Join.Choice.eval, h]
    erw [chosen, ite_eq_left h]
    rfl
  · have chosen : p.stage.choice.eval bank = (1 : Fin 2) := by
      simp [Program.stage, Join.Choice.eval, h]
    erw [chosen, ite_eq_right h]
    rfl

private theorem run_jump {origin target : Fin size}
    (edge : (src origin).terminator = .transfer (.jump target))
    (fuel : Nat) (bank : Bank (regs := regs) m) :
    src.runFrom m (fuel + 1) origin bank = src.runFrom m fuel target ((src origin).body.eval m bank) := by
  simp only [Tail.Source.runFrom, edge, Tail.Terminator.select]

private theorem run_header (fuel : Nat) (old : Bank (regs := regs) m) :
    src.runFrom m (fuel + 1) p.header old =
      src.runFrom m fuel (p.armStart (p.selected m old)) ((src p.header).body.eval m old) := by
  simp only [Tail.Source.runFrom, p.splitEdge, Tail.Terminator.select, Program.selected, selected_start p m]
  by_cases h : (((src p.header).body.eval m old).get p.condition).down = true <;> simp [h]

private theorem run_step (fuel : Nat) (old : Bank (regs := regs) m) :
    src.runFrom m (fuel + p.activationCost (p.selected m old)) p.header old =
      let next := p.nextBank m old
      if (next.get p.again).down then src.runFrom m fuel p.header next else some (next.get p.result) := by
  let bank := (src p.header).body.eval m old
  let arm := p.armPath (p.selected m old)
  have visits : fuel + p.activationCost (p.selected m old) = fuel + 2 + arm.blocks.length + 1 := by
    unfold Program.activationCost
    dsimp only [arm]
    omega
  have latchBank : p.nextBank m old =
      (src p.latch).body.eval m ((src p.join).body.eval m (arm.quads.eval m bank)) := by
    unfold Program.nextBank Stage.eval
    erw [arm_body p (p.selected m old)]
    exact List.foldl_append
  rw [visits, run_header, arm.run_segment m (fuel + 2) bank,
    run_jump m p.joinEdge (fuel + 1), latchBank]
  simp only [Tail.Source.runFrom, p.latchEdge, Tail.Terminator.select]
  by_cases h : ((p.nextBank m old).get p.again).down = true
  all_goals
    rw [latchBank] at h
    dsimp only [bank] at h ⊢
    simp [h]

private theorem run_short (fuel : Nat) (old : Bank (regs := regs) m)
    (short : fuel < p.activationCost (p.selected m old)) :
    src.runFrom m fuel p.header old = none := by
  let bank := (src p.header).body.eval m old
  let arm := p.armPath (p.selected m old)
  cases fuel with
  | zero => rfl
  | succ fuel =>
    rw [run_header]
    by_cases enough : arm.blocks.length ≤ fuel
    · let spare := fuel - arm.blocks.length
      have fits : spare + arm.blocks.length = fuel := Nat.sub_add_cancel enough
      rw [← fits, arm.run_segment m spare bank]
      have tiny : spare = 0 ∨ spare = 1 := by
        change fuel + 1 < arm.blocks.length + 3 at short
        omega
      rcases tiny with zero | one
      · rw [zero]
        rfl
      · rw [one, run_jump m p.joinEdge 0]
        rfl
    · exact arm.run_short m fuel bank (Nat.lt_of_not_ge enough)

private abbrev traceVisits (fuel : Nat) (old : Bank (regs := regs) m) :=
  ((p.trace m fuel old).map p.activationCost).sum

private theorem traceVisits_step (fuel : Nat) (old : Bank (regs := regs) m) :
    traceVisits p m (fuel + 1) old =
      (if ((p.nextBank m old).get p.again).down then traceVisits p m fuel (p.nextBank m old) else 0) +
        p.activationCost (p.selected m old) := by
  by_cases h : ((p.nextBank m old).get p.again).down = true <;>
    simp [traceVisits, Program.trace, traceFrom, h, Nat.add_comm]

private abbrev runTheta (fuel : Nat) (old : Bank (regs := regs) m) :=
  iterate (iterateBody p m) (fun tag => tag.down.val == 1) fuel old

private theorem iterate_step (fuel : Nat) (old : Bank (regs := regs) m) :
    runTheta p m (fuel + 1) old =
      if ((p.nextBank m old).get p.again).down then runTheta p m fuel (p.nextBank m old)
      else some (p.nextBank m old) := by
  unfold runTheta
  rw [iterate]
  by_cases h : ((p.nextBank m old).get p.again).down = true <;>
    simp [iterateBody, RVSDG.Theta.bodyResult, h] <;> rfl

private theorem iterate_run (fuel : Nat) (old : Bank (regs := regs) m) :
    src.runFrom m (traceVisits p m fuel old) p.header old =
      (runTheta p m fuel old).map (fun bank => bank.get p.result) := by
  induction fuel generalizing old with
  | zero => rfl
  | succ fuel ih =>
    rw [traceVisits_step, iterate_step]
    by_cases h : ((p.nextBank m old).get p.again).down = true
    · simp only [ite_eq_left h]
      rw [run_step]
      simpa only [ite_eq_left h] using ih (p.nextBank m old)
    · simp only [ite_eq_right h]
      rw [run_step]
      simp [h] <;> rfl

/-- Once a native run has returned, its selected trace gives the exact
minimum source budget for that observation. -/
private theorem iterate_at (fuel sourceFuel : Nat) (old done : Bank (regs := regs) m)
    (returned : runTheta p m fuel old = some done) :
    src.runFrom m sourceFuel p.header old =
      if traceVisits p m fuel old ≤ sourceFuel then some (done.get p.result) else none := by
  induction fuel generalizing sourceFuel old with
  | zero => contradiction
  | succ fuel ih =>
    rw [iterate_step] at returned
    rw [traceVisits_step]
    let cost := p.activationCost (p.selected m old)
    by_cases enough : cost ≤ sourceFuel
    · have step := run_step p m (sourceFuel - cost) old
      change src.runFrom m (sourceFuel - cost + cost) p.header old = _ at step
      rw [Nat.sub_add_cancel enough] at step
      rw [step]
      by_cases h : ((p.nextBank m old).get p.again).down = true
      · simp only [ite_eq_left h] at returned ⊢
        have cutoff : traceVisits p m fuel (p.nextBank m old) + cost ≤ sourceFuel ↔
            traceVisits p m fuel (p.nextBank m old) ≤ sourceFuel - cost := by omega
        simpa only [← cutoff] using ih (sourceFuel - cost) (p.nextBank m old) returned
      · simp [h] at returned
        subst done
        simp [h, show p.activationCost (p.selected m old) ≤ sourceFuel from enough] <;> rfl
    · rw [run_short p m sourceFuel old (Nat.lt_of_not_ge enough)]
      apply (ite_eq_right _).symm
      change ¬ _ + cost ≤ sourceFuel
      omega

private theorem iterate_complete (sourceFuel : Nat) (old : Bank (regs := regs) m)
    {result : sortValue m.value out} (returned : src.runFrom m sourceFuel p.header old = some result) :
    ∃ fuel done, runTheta p m fuel old = some done ∧ done.get p.result = result := by
  let cost := p.activationCost (p.selected m old)
  by_cases enough : cost ≤ sourceFuel
  · have step := run_step p m (sourceFuel - cost) old
    change src.runFrom m (sourceFuel - cost + cost) p.header old = _ at step
    rw [Nat.sub_add_cancel enough] at step
    rw [step] at returned
    by_cases h : ((p.nextBank m old).get p.again).down = true
    · simp only [ite_eq_left h] at returned
      obtain ⟨fuel, done, rest, value⟩ := iterate_complete (sourceFuel - cost) (p.nextBank m old) returned
      exact ⟨fuel + 1, done, by simpa only [iterate_step, ite_eq_left h] using rest, value⟩
    · simp [h] at returned
      exact ⟨1, p.nextBank m old, by rw [iterate_step, ite_eq_right h], Option.some.inj returned⟩
  · rw [run_short p m sourceFuel old (Nat.lt_of_not_ge enough)] at returned
    contradiction
termination_by sourceFuel
decreasing_by
  have positive : 0 < cost := by
    unfold cost Program.activationCost
    omega
  omega

theorem lower_run (fuel : Nat) (input : Bank (regs := regs) m) :
    p.lower.run (model m) fuel input =
      (src.runFrom m (p.sourceVisits m fuel input) entry input).map (fun value => .cons value .nil) := by
  rw [graph_run, Program.sourceVisits, run_jump m p.entryEdge, iterate_run p m]
  erw [Option.map_map]
  rfl

theorem run_at (fuel sourceFuel : Nat) (input : Bank (regs := regs) m) (result : sortValue m.value out)
    (returned : p.lower.run (model m) fuel input = some (.cons result .nil)) :
    src.runFrom m sourceFuel entry input =
      if p.sourceVisits m fuel input ≤ sourceFuel then some result else none := by
  rw [graph_run] at returned
  obtain ⟨done, loop, packet⟩ := Option.map_eq_some_iff.mp returned
  have value := congrArg (fun bank : Tuple (Val m.value) [.value out] => bank.get .head) packet
  cases sourceFuel with
  | zero => simp [Program.sourceVisits, Tail.Source.runFrom]
  | succ sourceFuel =>
    rw [run_jump m p.entryEdge, iterate_at p m fuel sourceFuel _ done loop, Program.sourceVisits]
    change (if _ ≤ sourceFuel then some (done.get p.result) else none) = _
    rw [show done.get p.result = result from value]
    simp only [Nat.succ_le_succ_iff] <;> rfl

theorem source_bounded_iff (fuel : Nat) (input : Bank (regs := regs) m) (result : sortValue m.value out) :
    src.runFrom m fuel entry input = some result ↔
      ∃ activations, p.lower.run (model m) activations input = some (.cons result .nil) ∧
        p.sourceVisits m activations input ≤ fuel := by
  constructor
  · intro observed
    cases fuel with
    | zero => contradiction
    | succ fuel =>
      rw [run_jump m p.entryEdge] at observed
      obtain ⟨activations, done, native, value⟩ := iterate_complete p m fuel _ observed
      have returned : p.lower.run (model m) activations input = some (.cons result .nil) := by
        rw [graph_run]
        exact (congrArg (Option.map (fun bank : Bank (regs := regs) m =>
          Tuple.cons (bank.get p.result) .nil)) native).trans
          (congrArg (fun x => some (Tuple.cons (F := Val m.value) (t := .value out) x .nil)) value)
      refine ⟨activations, returned, ?_⟩
      have boundary := run_at p m activations (fuel + 1) input result returned
      rw [run_jump m p.entryEdge, observed] at boundary
      split at boundary
      · assumption
      · contradiction
  · rintro ⟨activations, returned, fits⟩
    rw [run_at p m activations fuel input result returned, ite_eq_left fits]

theorem returns_iff (input : Bank (regs := regs) m) (result : sortValue m.value out) :
    p.lower.Returns (model m) input (.cons result .nil) ↔
      ∃ fuel, src.runFrom m fuel entry input = some result := by
  constructor
  · rintro ⟨fuel, returned⟩
    exact ⟨_, (source_bounded_iff p m _ input result).mpr ⟨fuel, returned, Nat.le_refl _⟩⟩
  · rintro ⟨fuel, returned⟩
    obtain ⟨activations, native, _⟩ := (source_bounded_iff p m fuel input result).mp returned
    exact ⟨activations, native⟩

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Proofs

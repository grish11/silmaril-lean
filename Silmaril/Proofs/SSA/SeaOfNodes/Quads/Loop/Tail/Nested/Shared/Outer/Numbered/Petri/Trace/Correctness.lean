module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Activation
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Boundaries.Waiting
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Continuation.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Numbered.Execution.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Join.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF.InnerPhi.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi.Readback.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Proofs

open SeaOfNodes.Diamond (ValueSort sortValue)
open SeaOfNodes.Loop.MLIR.CF (Op model evalOp)
open SeaOfNodes.MLIR.Lowering (encodeValues valueWidth)
open Silmaril.MLIR.Arith (Width Env)
open Blocks (Bank)
open RVSDG.NestedTheta (Graph Term iterate)
open RVSDG.NestedTheta.Petri (Fire Marking finished pending Finishes finishes_term_iff finishes_iff)
open RVSDG.Petri (read colour collect)
open Relation (ReflTransGen)
open Join.Finite (lastBank)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond (iterateThenReturnWith)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} (p : Program src entry)
variable (input : Bank (regs := regs) model)

private theorem preheader_run :
    (Term.ofBase (entryCode (src := src) (entry := entry))).toGraph.run semantics 0 input =
      some ((src entry).body.eval model input) := by
  rw [← Graph.run_toTerm, Term.toTerm_toGraph, Term.run_ofBase]
  unfold RVSDG.Term.run entryCode
  erw [Join.Block.lowerFrom_eval, read_initial]
  rfl

private theorem windows_of_iterate (bodyFuel fuel : Nat) (old final : Bank (regs := regs) model)
    (run : iterate ((thetaBody p).run semantics bodyFuel) (fun tag => tag.down.val == 1) fuel old =
      some final) : ∃ packets, Nonempty (Windows p old packets final) := by
  induction fuel generalizing old with
  | zero => cases run
  | succ fuel ih =>
    let next := nextBank p model old
    have body : (thetaBody p).run semantics bodyFuel old =
        some (RVSDG.Theta.bodyResult semantics (next.get p.again).down next) := by
      rw [← Term.toTerm_toGraph (thetaBody p), Graph.run_toTerm]
      exact activation_run p model bodyFuel old
    rw [iterate, body] at run
    obtain ⟨window⟩ := activation p old
    cases guard : (next.get p.again).down with
    | false =>
      rw [guard] at run
      have same : next = final := Option.some.inj run
      have stopped : Activation p old (packetsAt p old) false next := guard ▸ window
      exact ⟨_, ⟨.stop (same ▸ stopped)⟩⟩
    | true =>
      rw [guard] at run
      obtain ⟨later, ⟨remaining⟩⟩ := ih next run
      have feedback : Activation p old (packetsAt p old) true next := guard ▸ window
      exact ⟨_, ⟨.again feedback remaining⟩⟩

private def stoppedAt
    (preheader : Marking semantics (.ofBase (entryCode (src := src) (entry := entry))))
    (bank : Bank (regs := regs) model) : Marking semantics (emitted p) :=
  (entryCut p).attach semantics preheader (.done bank, PUnit.unit)

private theorem lift_body
    (preheader : Marking semantics (.ofBase (entryCode (src := src) (entry := entry))))
    (old : Bank (regs := regs) model) {a b : Marking semantics (thetaBody p)}
    (steps : ReflTransGen (Fire semantics (thetaBody p) old PUnit.unit) a b) :
    ReflTransGen (Fire semantics (emitted p) input PUnit.unit) (atBody p preheader old a) (atBody p preheader old b) := by
  apply (entryCut p).tail_reaches semantics input PUnit.unit preheader
  let cut := entryCut p
  let tail := iterateThenReturnWith (thetaBody p) p.result (endWires (entryCode (src := src) (entry := entry)))
  exact steps.lift (p := Fire semantics tail input (cut.tokens semantics PUnit.unit preheader))
    (fun mark => (.waiting (0 : Fin 1) (old, mark), PUnit.unit)) (fun _ _ step => Fire.advance step)

private theorem visits_prepend {M : Type} {step : M → M → Prop}
    {first start last : M} {marks : List M}
    (earlier : ReflTransGen step first start) (visits : Visits step start marks last) :
    Visits step first marks last := by
  cases visits with
  | finish steps => exact .finish (earlier.trans steps)
  | visit steps rest => exact .visit (earlier.trans steps) rest

private theorem windows_visit
    (preheader : Marking semantics (.ofBase (entryCode (src := src) (entry := entry))))
    {old final : Bank (regs := regs) model} {packets : List (Packets regs size)}
    (windows : Windows p old packets final) :
    Visits (Fire semantics (emitted p) input PUnit.unit)
      (atBody p preheader old (pending semantics (thetaBody p))) (Windows.checkpoints p windows preheader)
      (stoppedAt p preheader final) := by
  induction windows with
  | stop window =>
    refine .visit (lift_body p input preheader _ window.entered)
      (.visit (lift_body p input preheader _ window.joined) (.finish ?_))
    refine (lift_body p input preheader _ window.continued).trans ?_
    apply (entryCut p).tail_reaches semantics input PUnit.unit preheader
    exact .single (.commit window.latched rfl)
  | @again old next final later window remaining ih =>
    refine .visit (lift_body p input preheader _ window.entered)
      (.visit (lift_body p input preheader _ window.joined) ?_)
    have restart : ReflTransGen (Fire semantics (emitted p) input PUnit.unit)
        (atBody p preheader old window.final) (atBody p preheader next (pending semantics (thetaBody p))) := by
      apply (entryCut p).tail_reaches semantics input PUnit.unit preheader
      exact .single (.restart window.latched rfl rfl)
    exact visits_prepend ((lift_body p input preheader _ window.continued).trans restart) ih

private theorem completed_prefix {bank : Bank (regs := regs) model}
    (preheader : Marking semantics (.ofBase (entryCode (src := src) (entry := entry))))
    (done : finished semantics (.ofBase (entryCode (src := src) (entry := entry))) input PUnit.unit preheader =
      some bank)
    (final : Bank (regs := regs) model) :
    finished semantics (emitted p) input PUnit.unit (stoppedAt p preheader final) =
      some (.cons (final.get p.result) .nil) := by
  refine ((entryCut p).finished_attach semantics input PUnit.unit preheader
    (.done final, PUnit.unit) done).trans ?_
  let tokens := (entryCut p).tokens semantics PUnit.unit preheader
  let fields := tokens.snoc (final.map fun _ => some)
  change collect (.cons (colour input fields ((lastBank _ _).get p.result)) .nil) =
    some (.cons (final.get p.result) .nil)
  have resultRead : colour input fields ((lastBank _ _).get p.result) = some (final.get p.result) := by
    rw [lastBank, get_tabulate]
    exact last_colour p.result tokens final
  rw [resultRead]
  rfl

theorem trace_of_windows {packets : List (Packets regs size)} {final : Bank (regs := regs) model}
    (windows : Windows p ((src entry).body.eval model input) packets final) :
    Nonempty (Trace p input packets final) := by
  let pre := Term.ofBase (entryCode (src := src) (entry := entry))
  let bank := (src entry).body.eval model input
  obtain ⟨mark, steps, done⟩ := (finishes_term_iff semantics pre input bank).mp
    ((finishes_iff semantics pre.toGraph input bank).mpr ⟨0, preheader_run (entry := entry) input⟩)
  let cut := entryCut p
  have ready := cut.read_after semantics input PUnit.unit mark bank done
  change RVSDG.Petri.read (baseCut (entryCode (src := src) (entry := entry)) _).wires _ _ = _ at ready
  rw [base_cut_wires] at ready
  have reachesStart :
      ReflTransGen (Fire semantics (emitted p) input PUnit.unit) (pending semantics (emitted p))
        (atBody p mark bank (pending semantics (thetaBody p))) :=
    (cut.prefix_reaches semantics input PUnit.unit steps).trans
      (cut.tail_reaches semantics input PUnit.unit mark (.single (.enter ready rfl)))
  exact ⟨⟨mark, windows, stoppedAt p mark final, visits_prepend reachesStart (windows_visit p input mark windows),
    completed_prefix p input mark done final⟩⟩

theorem trace_of_run (fuel : Nat) (value : sortValue model.value out)
    (run : (lower p).run semantics fuel input = some (.cons value .nil)) :
    ∃ packets final, final.get p.result = value ∧ Nonempty (Trace p input packets final) := by
  change (Shared.Numbered.Execution.lower p.toControl (thetaBody p)).run (Join.model model) fuel input = _ at run
  rw [Shared.Numbered.Execution.lower_iterate] at run
  obtain ⟨final, iterations, same⟩ := Option.map_eq_some_iff.mp run
  obtain ⟨packets, ⟨windows⟩⟩ := windows_of_iterate p _ _ _ _ iterations
  exact ⟨packets, final, congrArg (fun bank => RVSDG.Tuple.get bank .head) same,
    trace_of_windows p input windows⟩

theorem packetsAt_cf (inner : Shared.MLIR.CF.InnerPhi.Rows p.toRoutes) (outer : MLIR.CF.Phi.Rows p)
    (old : Bank (regs := regs) model) :
    (packetsAt p old).encode = cfPacketsAt p inner outer input old := by
  apply Prod.ext
  · by_cases entered : ((Shared.MLIR.CF.InnerPhi.headerBank p.toRoutes old).get p.outerTest).down = true
    · simp only [Packets.encode, packetsAt, cfPacketsAt, entered, ite_true, Option.map_some, inner.bank_eq]
    · simp only [Packets.encode, packetsAt, cfPacketsAt, entered, Bool.false_eq_true, ite_false, Option.map_none]
  · rw [show (cfPacketsAt p inner outer input old).2 =
      (p.outerEdgeOccurrence (MLIR.CF.Phi.arrivalSide (p := p) old), outer.selectedBank input old) by
      unfold cfPacketsAt MLIR.CF.Phi.Rows.selectedBank
      rw [MLIR.CF.Phi.Readback.readBank_eq]]
    rw [outer.selected_bank]
    rfl

theorem cf_latch {old next : Bank (regs := regs) model} {packets : Packets regs size} {again : Bool}
    (window : Activation p old packets again next) :
    MLIR.CF.latchSuccessor p input old =
      .inl (if again then Diamond.MLIR.CF.siteFrame p.header next
        else Diamond.MLIR.CF.exitFrame (next.get p.result)) := by
  let packet := RVSDG.Theta.bodyResult semantics again next
  have reaches := window.entered.trans (window.joined.trans window.continued)
  have done := (finishes_term_iff semantics (thetaBody p) old packet).mpr
    ⟨window.final, reaches, window.latched⟩
  obtain ⟨fuel, ran⟩ := (finishes_iff semantics (thetaBody p).toGraph old packet).mp done
  have agrees := MLIR.CF.Comparison.latch_successor_at_activation p input fuel old
  rw [ran] at agrees
  exact Option.some.inj (by cases again <;> exact agrees)

variable {p input}

theorem erase_visits {M : Type} {step : M → M → Prop}
    {start last : M} {marks : List M} (visits : Visits step start marks last) :
    ReflTransGen step start last := by
  induction visits with
  | finish steps => exact steps
  | visit steps _ remaining => exact steps.trans remaining

/-- Concatenation forgets checkpoints and replays as Step of the
original emitted graph. -/
theorem trace_replay {packets : List (Packets regs size)} {final : Bank (regs := regs) model}
    (trace : Trace p input packets final) :
    Finishes semantics (lower p) input (.cons (final.get p.result) .nil) :=
  (finishes_term_iff semantics (emitted p) input _).mpr ⟨trace.final, erase_visits trace.visits, trace.result⟩

variable (p input)

theorem trace_iff_source (value : sortValue model.value out) :
    (∃ packets final, final.get p.result = value ∧ Nonempty (Trace p input packets final)) ↔
      ∃ bound, src.runFrom model bound entry input = some value := by
  constructor
  · rintro ⟨_, final, callResult, ⟨trace⟩⟩
    simpa only [callResult] using (petri_finishes_iff p model input (final.get p.result)).mp (trace_replay trace)
  · intro returned
    obtain ⟨fuel, run⟩ := (returns_iff p model input value).mpr returned
    exact trace_of_run p input fuel value run

/-- Compare completion with the real emitted CF at an independent visit
bound. The left witness retains all coloured join checkpoints. -/
theorem trace_iff_cf (output : Env [valueWidth out]) :
    (∃ packets final, encodeValues (ins := [out]) (.cons (final.get p.result) .nil) = output ∧
      Nonempty (Trace p input packets final)) ↔
      ∃ bound, (MLIR.CF.lower p).run evalOp bound (encodeValues input) = some output :=
  ⟨fun ⟨_, _, same, ⟨trace⟩⟩ =>
    (MLIR.CF.Comparison.cf_finishes_iff p input output).mpr ⟨_, trace_replay trace, same⟩, by
    intro returned
    obtain ⟨fuel, mapped⟩ := (MLIR.CF.Comparison.cf_returns_iff p input output).mp returned
    obtain ⟨packet, ran, same⟩ := Option.map_eq_some_iff.mp mapped
    cases packet with
    | cons value tail =>
      cases tail
      obtain ⟨packets, final, exactWord, trace⟩ := trace_of_run p input fuel value ran
      exact ⟨packets, final, by rw [exactWord]; exact same, trace⟩⟩

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Proofs

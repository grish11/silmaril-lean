module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Thms
import Silmaril.SSA.SeaOfNodes.MLIR.Thms
import Mathlib.Tactic.FinCases

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Proofs

open SeaOfNodes.Diamond (ValueSort dataPorts)
open SeaOfNodes.Diamond.SCCP (Fact TupleCovers)
open SeaOfNodes.Loop.SCCP (BankDecidableEq)
open SeaOfNodes.Loop.MLIR.CF (Op model evalOp)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Tail.Diamond.MLIR.CF (JumpAgrees block_eval_with entryNames_agree blockNames_agree
  destinationFrameWith returnFrame runBlock_eq_of_frames_on Widths entryNames blockNames)
open Silmaril.MLIR.Arith (Width Env)
open Silmaril.MLIR.CF (Frame)
open RVSDG (Tuple)
open Blocks (Bank)

variable {regs : List (ValueSort Width)} {result : Width}

private theorem jump_agrees : JumpAgrees (jump (regs := regs) (result := result)) siteFrame :=
  fun ok versions id => congrArg (fun args => Frame.mk (siteLabel id) args) (ok.operands_eval (ins := regs) versions)

variable {p : Program Op regs (.data result)} [BankDecidableEq Word (dataPorts regs)]
variable {facts : Tuple (Fact Word) (dataPorts regs)}

private theorem closed (checked : Checked model p facts) (id : Fin 3)
    (bank : Bank (regs := regs) model) (next : Fin 3)
    (selected : (bypass checked id).terminator.select model bank = .jump next) : next ≠ 0 := by
  fin_cases id
  · change Tail.Destination.jump (1 : Fin 3) = .jump next at selected
    cases selected
    decide
  · change (if (bank.get p.again).down then Tail.Destination.jump (2 : Fin 3) else .ret p.result) =
      .jump next at selected
    by_cases test : (bank.get p.again).down = true
    · simp [test] at selected
      subst next
      decide
    · simp [test] at selected
  · change Tail.Destination.jump (1 : Fin 3) = .jump next at selected
    cases selected
    decide

private theorem entry_eval (checked : Checked model p facts) (input : Bank (regs := regs) model) :
    (lower checked).entry.eval evalOp (fun term env => term.eval env) (encodeValues input) =
      let next := (bypass checked 0).body.eval model input
      .inl (destinationFrameWith siteFrame (returnFrame .exit) next
        ((bypass checked 0).terminator.select model next)) :=
  block_eval_with (out := .data result) (jump := jump (regs := regs) (result := result))
    (exit := .exit) jump_agrees (bypass checked 0) ⟨entryNames regs, PUnit.unit⟩
    (encodeValues input) input (fun port => entryNames_agree input port)

private theorem site_eval (checked : Checked model p facts) (input : Bank (regs := regs) model)
    (id : Fin 3) (nonentry : id ≠ 0) (old : Bank (regs := regs) model) :
    ((lower checked).block (siteLabel id)).eval evalOp (fun term env => term.eval env)
        ((encodeValues old).append (encodeValues input)) =
      let next := (bypass checked id).body.eval model old
      .inl (destinationFrameWith siteFrame (returnFrame .exit) next
        ((bypass checked id).terminator.select model next)) := by
  fin_cases id
  · exact False.elim (nonentry rfl)
  all_goals
    exact block_eval_with (out := .data result) (jump := jump (regs := regs) (result := result))
      (exit := .exit) jump_agrees (bypass checked _) ⟨blockNames (Widths regs) regs, PUnit.unit⟩
      ((encodeValues old).append (encodeValues input)) old
      (fun port => blockNames_agree (encodeValues input) old port)

theorem entry_frame (checked : Checked model p facts) (input : Bank (regs := regs) model) :
    (lower checked).entry.eval evalOp (fun term env => term.eval env) (encodeValues input) =
      .inl ⟨.header, encodeValues (p.preheader.eval model input)⟩ :=
  entry_eval checked input

theorem header_frame (checked : Checked model p facts) (input old : Bank (regs := regs) model) :
    ((lower checked).block .header).eval evalOp (fun term env => term.eval env)
        ((encodeValues old).append (encodeValues input)) =
      let next := p.header.eval model old
      .inl (if (next.get p.again).down then ⟨.feedback, encodeValues next⟩
        else ⟨.exit, .cons (next.get p.result) .nil⟩) := by
  refine (site_eval checked input 1 (by decide) old).trans ?_
  change Sum.inl (destinationFrameWith siteFrame (returnFrame .exit) (p.header.eval model old)
    (if ((p.header.eval model old).get p.again).down then Tail.Destination.jump (2 : Fin 3)
      else .ret p.result)) = _
  change _ = Sum.inl (if ((p.header.eval model old).get p.again).down then
    Frame.mk (Label.feedback (regs := regs) (result := result)) (encodeValues (p.header.eval model old)) else
    Frame.mk Label.exit (.cons ((p.header.eval model old).get p.result) .nil))
  cases ((p.header.eval model old).get p.again).down <;> rfl

theorem feedback_frame (checked : Checked model p facts) (input old : Bank (regs := regs) model) :
    ((lower checked).block .feedback).eval evalOp (fun term env => term.eval env)
        ((encodeValues old).append (encodeValues input)) =
      .inl ⟨.header, encodeValues ((p.feedback checked.side).eval model old)⟩ := by
  refine (site_eval checked input 2 (by decide) old).trans ?_
  obtain ⟨side, marked, excluded⟩ := checked
  cases side <;> rfl

theorem lower_run (checked : Checked model p facts) (input : Bank (regs := regs) model) (fuel : Nat) :
    (lower checked).run evalOp (fuel + 1) (encodeValues input) =
      ((bypass checked).runFrom model fuel 0 input).map (fun value => Env.cons value .nil) :=
  runBlock_eq_of_frames_on (out := .data result) (src := bypass checked)
    (lower checked) (encodeValues input) siteFrame .exit (· ≠ 0)
    (closed checked) (site_eval checked input) rfl fuel 0 input
    (lower checked).entry (encodeValues input) (entry_eval checked input)

private theorem singleton_eq_iff {left right : Word result} :
    (Env.cons left .nil : Env [result]) = .cons right .nil ↔ left = right :=
  ⟨fun h => congrArg (fun env : Env [result] => env.get .here) h, fun h => h ▸ rfl⟩

private theorem lower_some (checked : Checked model p facts) (input : Bank (regs := regs) model)
    (fuel : Nat) (value : Word result) :
    (lower checked).run evalOp (fuel + 1) (encodeValues input) = some (.cons value .nil) ↔
      (bypass checked).runFrom model fuel 0 input = some value := by
  rw [lower_run]
  constructor
  · intro h
    obtain ⟨observed, ret, equal⟩ := Option.map_eq_some_iff.mp h
    exact ret.trans (congrArg some (singleton_eq_iff.mp equal))
  · intro h
    exact Option.map_eq_some_iff.mpr ⟨value, h, rfl⟩

theorem run_count_iff (checked : Checked model p facts) {input : Bank (regs := regs) model}
    (covered : TupleCovers facts input) (fuel : Nat) (value : Word result) :
    (lower checked).run evalOp fuel (encodeValues input) = some (.cons value .nil) ↔
      ∃ n, ReturnsAfter p model n (p.preheader.eval model input) value ∧ 2 * n + 3 ≤ fuel := by
  cases fuel with
  | zero =>
    constructor
    · intro returned
      cases returned
    · rintro ⟨n, _, budget⟩
      omega
  | succ fuel =>
    refine (lower_some checked input fuel value).trans
      ((run_bypass_iff checked covered fuel value).trans ?_)
    constructor <;> rintro ⟨n, trace, budget⟩ <;> exact ⟨n, trace, by omega⟩

theorem feedback_budget_eq (checked : Checked model p facts) {input : Bank (regs := regs) model}
    (covered : TupleCovers facts input) (limit : Nat) :
    (lower checked).run evalOp (2 * limit + 3) (encodeValues input) =
      (p.source.runFrom model (3 * limit + 2) 0 input).map (fun value => Env.cons value .nil) :=
  (lower_run checked input (2 * limit + 2)).trans
    (congrArg (Option.map (fun value : Word result => Env.cons value .nil))
      ((Bypass.feedback_budget_eq checked covered limit).trans (DeleteRoute.runFrom_eq checked covered _)))

theorem returns_iff_original (checked : Checked model p facts) {input : Bank (regs := regs) model}
    (covered : TupleCovers facts input) (value : Word result) :
    (∃ fuel, (lower checked).run evalOp fuel (encodeValues input) = some (.cons value .nil)) ↔
      ∃ fuel, p.source.runFrom model fuel 0 input = some value := by
  have native := Bypass.returns_iff checked covered value
  constructor
  · rintro ⟨fuel, returned⟩
    cases fuel with
    | zero => cases returned
    | succ fuel =>
      obtain ⟨visits, observed⟩ := native.mp ⟨fuel, (lower_some checked input fuel value).mp returned⟩
      exact ⟨visits, (DeleteRoute.runFrom_eq checked covered visits).symm.trans observed⟩
  · rintro ⟨visits, returned⟩
    obtain ⟨fuel, observed⟩ := native.mpr ⟨visits, (DeleteRoute.runFrom_eq checked covered visits).trans returned⟩
    exact ⟨fuel + 1, (lower_some checked input fuel value).mpr observed⟩

theorem diverges_iff_original (checked : Checked model p facts) {input : Bank (regs := regs) model}
    (covered : TupleCovers facts input) :
    (lower checked).Diverges evalOp (encodeValues input) ↔
      ¬ ∃ value fuel, p.source.runFrom model fuel 0 input = some value := by
  constructor
  · rintro diverges ⟨value, finite⟩
    obtain ⟨fuel, returned⟩ := (returns_iff_original checked covered value).mpr finite
    rw [diverges fuel] at returned
    cases returned
  · intro absent fuel
    cases observed : (lower checked).run evalOp fuel (encodeValues input) with
    | none => rfl
    | some env =>
      cases env with
      | cons value tail =>
        cases tail
        exact False.elim (absent ⟨value, (returns_iff_original checked covered value).mp ⟨fuel, observed⟩⟩)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Proofs

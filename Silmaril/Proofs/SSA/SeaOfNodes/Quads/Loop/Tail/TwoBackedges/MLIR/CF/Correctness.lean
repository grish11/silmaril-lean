module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.MLIR.CF.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.MLIR.CF.Proofs

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op model evalOp)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Tail.Diamond.MLIR.CF (siteFrame source_site_eval lowerSource_run)
open Silmaril.MLIR.Arith (Width Env)
open Blocks (Bank)

variable {regs : List (ValueSort Width)} {result : Width}
variable (p : Program Op regs (.data result)) (input : Bank (regs := regs) model)

theorem dispatch_frame (bank : Bank (regs := regs) model) :
    ((lower p).block (.site 2)).eval evalOp (fun term env => term.eval env)
        ((encodeValues bank).append (encodeValues input)) =
      .inl (siteFrame (out := .data result) (feedbackBlock (bank.get p.select).down) bank) := by
  refine (source_site_eval (src := p.source) (entry := 0) input bank 2).trans ?_
  change Sum.inl (Tail.Diamond.MLIR.CF.destinationFrame (out := .data result) bank
    (if (bank.get p.select).down then .jump (feedbackBlock true) else .jump (feedbackBlock false))) =
      Sum.inl (siteFrame (out := .data result) (feedbackBlock (bank.get p.select).down) bank)
  cases (bank.get p.select).down <;> rfl

theorem feedback_frame (side : Bool) (bank : Bank (regs := regs) model) :
    ((lower p).block (.site (feedbackBlock side))).eval evalOp (fun term env => term.eval env)
        ((encodeValues bank).append (encodeValues input)) =
      .inl (siteFrame (out := .data result) (1 : Fin 5) ((p.feedback side).eval model bank)) := by
  refine (source_site_eval (src := p.source) (entry := 0) input bank (feedbackBlock side)).trans ?_
  cases side <;> rfl

theorem lower_run (fuel : Nat) :
    (lower p).run evalOp (fuel + 1) (encodeValues input) =
      (p.source.runFrom model fuel 0 input).map (fun value => Env.cons value .nil) :=
  lowerSource_run (src := p.source) (entry := 0) fuel input

theorem returns_iff (value : Word result) :
    (∃ fuel, (lower p).run evalOp fuel (encodeValues input) = some (.cons value .nil)) ↔
      ∃ fuel, p.source.runFrom model fuel 0 input = some value := by
  constructor
  · rintro ⟨fuel, returned⟩
    cases fuel with
    | zero => cases returned
    | succ fuel =>
      rw [lower_run] at returned
      obtain ⟨word, native, equal⟩ := Option.map_eq_some_iff.mp returned
      exact ⟨fuel, native.trans (congrArg (fun env : Env [result] => some (env.get .here)) equal)⟩
  · rintro ⟨fuel, returned⟩
    exact ⟨fuel + 1, (lower_run p input fuel).trans (Option.map_eq_some_iff.mpr ⟨value, returned, rfl⟩)⟩

theorem diverges_iff :
    (lower p).Diverges evalOp (encodeValues input) ↔
      ¬ ∃ value fuel, p.source.runFrom model fuel 0 input = some value := by
  constructor
  · rintro absent ⟨value, returned⟩
    obtain ⟨fuel, observed⟩ := (returns_iff p input value).mpr returned
    rw [absent fuel] at observed
    cases observed
  · intro absent fuel
    cases observed : (lower p).run evalOp fuel (encodeValues input) with
    | none => rfl
    | some env =>
      cases env with
      | cons value tail =>
        cases tail
        exact (absent ⟨value, (returns_iff p input value).mp ⟨fuel, observed⟩⟩).elim

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.MLIR.CF.Proofs

module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Backends.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF.DeadProducer.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Split.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Backends.Proofs

open SeaOfNodes.Diamond (ValueSort sortValue)
open SeaOfNodes.Loop.MLIR.CF (Op evalOp model)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues valueBits valueWidth)
open Silmaril.MLIR.Arith (Width Env)
open Nested.Numbered (nextBank)
open Blocks (Bank)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} {p : Program src entry}
variable {targets : Targets src entry}

theorem compile_origin (success : compile src entry = .ok targets) :
    Nested.check src entry = some targets.program := by
  cases recognized : Nested.check src entry with
  | none => simp [compile, recognized] at success
  | some plan =>
    cases admitted : admit plan with
    | error reason => simp [compile, recognized, compileChecked, admitted, Except.map] at success
    | ok checked =>
      have equal := Except.ok.inj (by simpa only [compile, recognized, compileChecked, admitted, Except.map]
        using success)
      cases equal
      rfl

theorem checked_error_iff (reason : Refusal) :
    compileChecked p = .error reason ↔ admit p = .error reason := by
  cases accepted : admit p <;> simp [compileChecked, accepted, Except.map]

variable (targets)

theorem cf_activation_packet (input old : Bank (regs := regs) model) :
    let p := targets.program
    let afterMerge := (src p.join).body.eval model (p.mergeBank model old (p.selected model old))
    (targets.cf.block .latch).eval evalOp (fun term env => term.eval env)
        ((encodeValues ((atLatch p).project afterMerge)).append (encodeValues input)) =
      .inl (MLIR.CF.packetFrame p (observe p (carry p) (nextBank p model old))) := by
  dsimp only
  rw [targets.cf_eq, Iteration.cf_latch_packet, targets.checked.split.latch_agrees]
  simp only [nextBank, Nested.Numbered.tail, Join.Block.eval, List.foldl_append]

private theorem valueBits_injective (sort : ValueSort Width) : Function.Injective (@valueBits sort) := by
  cases sort with
  | data _ => exact fun _ _ same => same
  | predicate =>
    intro lhs rhs equal
    rcases lhs with ⟨lhs⟩
    rcases rhs with ⟨rhs⟩
    cases lhs <;> cases rhs <;> first | rfl | cases equal

private theorem map_return_iff (obs : Option (sortValue Word out)) (value : sortValue Word out) :
    obs.map (fun word => Env.cons (valueBits word) .nil) = some (.cons (valueBits value) .nil) ↔
      obs = some value := by
  constructor
  · intro encoded
    obtain ⟨other, got, same⟩ := Option.map_eq_some_iff.mp encoded
    have equal := valueBits_injective out (congrArg (fun env : Env [valueWidth out] => env.get .here) same)
    exact equal ▸ got
  · intro got
    rw [got]
    rfl

theorem cf_returns_iff (input : Bank (regs := regs) model) (value : sortValue Word out) :
    (∃ cfFuel, targets.cf.run evalOp cfFuel (encodeValues input) = some (.cons (valueBits value) .nil)) ↔
      ∃ sourceFuel, src.runFrom model sourceFuel entry input = some value := by
  have same := MLIR.CF.DeadProducer.lowerWith_run_agrees targets.program targets.checked.header targets.checked.split
    targets.prepared.final (targets.prepared.eval_eq model) input
  rw [targets.cf_eq, Iteration.lowerCF]
  simp only [same]
  exact (MLIR.CF.source_returns_iff targets.program targets.checked.header targets.checked.split input _).trans
    (exists_congr fun _ => map_return_iff _ value)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Backends.Proofs

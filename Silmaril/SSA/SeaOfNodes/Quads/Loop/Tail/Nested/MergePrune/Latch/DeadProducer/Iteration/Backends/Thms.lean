module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Backends.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Backends.Correctness
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Thms

/-! # Source-linked packets, finite returns and absence for the compiled pair -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Backends

open SeaOfNodes.Diamond (ValueSort sortValue)
open SeaOfNodes.Loop.MLIR.CF (Op evalOp model)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues valueBits)
open Silmaril.MLIR.Arith (Width Env)
open Nested.Numbered (nextBank sourceVisits)
open Blocks (Bank)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} {p : Program src entry}
variable {targets : Targets src entry}

/-- The existing recognizer's selected `Program` is used verbatim. -/
theorem compile_recognized (recognized : Nested.check src entry = some p) :
    compile src entry = compileChecked p := by
  simp only [compile, recognized]

theorem compile_shape_refusal (refused : Nested.check src entry = none) :
    compile src entry = .error .shape := by
  simp only [compile, refused]

theorem compileChecked_error_iff (reason : Refusal) :
    compileChecked p = .error reason ↔ admit p = .error reason :=
  Proofs.checked_error_iff reason

theorem compile_origin (success : compile src entry = .ok targets) :
    Nested.check src entry = some targets.program :=
  Proofs.compile_origin success

variable (targets)

/-- The emitted numbered prefix observes the selected original path's
complete packet, before θ extracts its tag and simultaneous feedback. -/
theorem Targets.numbered_packet (fuel : Nat) (old : Bank (regs := regs) model) :
    targets.packetRegion.run (Join.model model) fuel ((carry targets.program).project old) =
      some (observe targets.program (carry targets.program) (nextBank targets.program model old)) :=
  Iteration.numbered_packet_run targets.program model targets.checked.header targets.checked.split targets.prepared fuel old

/-- The actual CF latch chooses the source exit or feedback frame after
the selected source predecessor and merge have executed. -/
theorem Targets.cf_activation_packet (input old : Bank (regs := regs) model) :
    let p := targets.program
    let afterMerge := (src p.join).body.eval model (p.mergeBank model old (p.selected model old))
    (targets.cf.block .latch).eval evalOp (fun term env => term.eval env)
        ((encodeValues ((atLatch p).project afterMerge)).append (encodeValues input)) =
      .inl (MLIR.CF.packetFrame p (observe p (carry p) (nextBank p model old))) :=
  Proofs.cf_activation_packet targets input old

variable (input : Bank (regs := regs) model)

theorem Targets.cf_run (sourceFuel : Nat) :
    targets.cf.run evalOp (sourceFuel + 1) (encodeValues input) =
      (src.runFrom model sourceFuel entry input).map (fun word => Env.cons (valueBits word) .nil) := by
  rw [targets.cf_eq]
  exact Iteration.cf_run targets.program targets.checked.header targets.checked.split targets.prepared input sourceFuel

theorem Targets.numbered_run (activations : Nat) :
    targets.numbered.run (Join.model model) activations input =
      (src.runFrom model (sourceVisits targets.program model activations input) entry input).map
        (fun value => .cons value .nil) := by
  rw [targets.numbered_eq]
  exact Iteration.numbered_run targets.program model targets.checked.header targets.checked.split targets.prepared
    targets.checked.result input activations

/-- Each target returns the same value exactly when the original table
returns it. Each of the three bounds is quantified independently. -/
theorem Targets.returns_iff (value : sortValue Word out) :
    let source := ∃ sourceFuel, src.runFrom model sourceFuel entry input = some value
    ((∃ cfFuel, targets.cf.run evalOp cfFuel (encodeValues input) = some (.cons (valueBits value) .nil)) ↔ source) ∧
    (targets.numbered.Returns (Join.model model) input (.cons value .nil) ↔ source) :=
  ⟨Proofs.cf_returns_iff targets input value, targets.numbered_eq ▸ Iteration.numbered_returns_iff
    targets.program model targets.checked.header targets.checked.split targets.prepared targets.checked.result input value⟩

/-- Exhaustion at every finite bound is equivalent for the source and
each target. A single exhausted bound says nothing about this property. -/
theorem Targets.noFiniteReturn_iff :
    let absent := ∀ sourceFuel, src.runFrom model sourceFuel entry input = none
    (targets.cf.Diverges evalOp (encodeValues input) ↔ absent) ∧
    ((∀ activations, targets.numbered.run (Join.model model) activations input = none) ↔ absent) := by
  rw [targets.cf_eq, targets.numbered_eq]
  have numbered := Iteration.numbered_noFiniteReturn_iff targets.program model targets.checked.header
    targets.checked.split targets.prepared targets.checked.result input
  exact ⟨(Iteration.cf_noFiniteReturn_iff targets.program targets.checked.header targets.checked.split
    targets.prepared input targets.checked.result).trans numbered, numbered⟩

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Backends

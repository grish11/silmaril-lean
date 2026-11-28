module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Backends.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.Petri.Defs
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Backends.Petri.Correctness

/-! # Finite coloured completion of the compiled nested quad loop -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Backends

open SeaOfNodes.Diamond (ValueSort sortValue)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open SeaOfNodes.MLIR (Word)
open Silmaril.MLIR.Arith (Width)
open Relation (ReflTransGen)
open RVSDG.NestedTheta.Petri (Finishes Step result finishes_iff)
open Blocks (Bank)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}
variable (targets : Targets src entry) (input : Bank (regs := regs) model)

/-- The actual emitted numbered graph supplies the places and typed
colours. Completion preserves and reflects each finite source return. -/
theorem Targets.petri_finishes_iff (value : sortValue Word out) :
    Finishes (Join.model model) targets.numbered input (.cons value .nil) ↔
      ∃ sourceFuel, src.runFrom model sourceFuel entry input = some value :=
  (finishes_iff (Join.model model) targets.numbered input _).trans (targets.returns_iff input value).2

/-- Decode the one result port of a reachable completed marking. The
source bound is existential and the firing trace has its own length. -/
theorem Targets.petri_firing_iff (value : sortValue Word out) :
    (∃ final, ReflTransGen (Step (Join.model model) targets.numbered input)
        (RVSDG.NestedTheta.Petri.initial (Join.model model) targets.numbered) final ∧
      (result (Join.model model) targets.numbered input final).map (fun packet => packet.get .head) = some value) ↔
    ∃ sourceFuel, src.runFrom model sourceFuel entry input = some value :=
  (Petri.Proofs.decoded_iff_finishes targets input value).trans (targets.petri_finishes_iff input value)

/-- Absence of a finite completion at every output is exactly absence of
a source return at every finite source bound. -/
theorem Targets.petri_no_completion_iff :
    (∀ packet, ¬ Finishes (Join.model model) targets.numbered input packet) ↔
      ∀ sourceFuel, src.runFrom model sourceFuel entry input = none :=
  (Petri.Proofs.no_completion_iff_numbered targets input).trans (targets.noFiniteReturn_iff input).2

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Backends

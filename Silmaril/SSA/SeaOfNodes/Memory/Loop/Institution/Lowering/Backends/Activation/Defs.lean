module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Backends.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Petri.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF.Defs

/-! The typed boundary of one emitted ordered memory-loop activation. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Backends.Activation

open CategoryTheory
open RVSDG (Port)
open RVSDG.NestedTheta.Petri (Finishes)
open Silmaril.MLIR.Arith (Env)
open Silmaril.MLIR.CF (Frame)
open Silmaril.MLIR.CF.Ordered (Block)
open Silmaril.MLIR.MemRef (Buffer)
open MLIR.MemRef.CF (Label resultTypes)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {P Q : EntrySignature}

/-- Bind a leading address to a captured typed port and keep the supplied
wiring for the remaining operands. Two lanes use two applications. -/
def bindAddress (address : Port Q.args .address) (wiring : P ⟶ Q) :
    (⟨.address :: P.args⟩ : EntrySignature) ⟶ Q :=
  ⟨fun
    | .head => address
    | .tail p => EntrySignature.Hom.port wiring p⟩

/-- Observe the actual emitted block and its terminator from the header. -/
def memrefHeader (graph : Graph P.args) (model : EntryModel P) (initial : Heap model.cells) :
    (Frame Label ⊕ Env resultTypes) × Buffer model.cells :=
  Block.eval (MLIR.MemRef.CF.evalBody model.input)
    ((MLIR.MemRef.CF.lower model.cells graph).block Label.header) .nil ⟨initial⟩

/-- An exit exposes the word in its frame. A restart takes the header
edge. Both carry every cell as the post-store buffer. -/
def successor (graph : Graph P.args) (model : EntryModel P)
    (next : Heap model.cells) (restart : Bool) :
    (Frame Label ⊕ Env resultTypes) × Buffer model.cells :=
  (.inl (if restart then ⟨Label.header, .nil⟩
    else ⟨Label.exit, .cons (graph.stopWord model.input) .nil⟩), ⟨next⟩)

/-- A finite firing witness for the emitted activation's tag and full heap. -/
def petriActivation (graph : Graph P.args) (model : EntryModel P)
    (initial next : Heap model.cells) (restart : Bool) : Prop :=
  Finishes (thetaRuntime model.cells) graph.activation (Memory.encodeInput initial model.input)
    (.cons ⟨if restart then 1 else 0⟩ (Memory.encodeInput next model.input))

end Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Backends.Activation

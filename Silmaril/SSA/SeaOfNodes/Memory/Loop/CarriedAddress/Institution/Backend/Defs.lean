module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.Defs

/-! Observations of generated single-address-Phi backend equations. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution

open CategoryTheory Silmaril.Logic.Institution
open RVSDG (Tuple)
open Memory.Diamond.Institution (reduct)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

inductive Side where
  | lhs
  | rhs

variable {P Q : EntrySignature}

def Equation.graph (e : Equation P) : Side → Graph P.args
  | .lhs => e.lhs
  | .rhs => e.rhs

/-- An emitted equation family with retained source, exact encodings of the
initial heap and complete return, and a partial observer of its own execution.
The adequacy field compares complete finite results without aligning witnesses. -/
structure Backend where
  Sentence : EntrySignature → Type
  emit : {P : EntrySignature} → Equation P → Sentence P
  source : {P : EntrySignature} → Sentence P → Equation P
  source_emit : ∀ {P : EntrySignature} (e : Equation P), source (emit e) = e
  emit_source : ∀ {P : EntrySignature} (s : Sentence P), emit (source s) = s
  Initial : Nat → Type
  Result : Nat → Type
  initial : (cells : Nat) → Heap cells ≃ Initial cells
  result : (cells : Nat) → (Word × Heap cells) ≃ Result cells
  observe : {P : EntrySignature} → Sentence P → Side → (model : EntryModel P) →
    Initial model.cells → Part (Result model.cells)
  correct : ∀ {P : EntrySignature} (e : Equation P) (side : Side) (model : EntryModel P)
    (heap : Heap model.cells) (value : Word × Heap model.cells),
    observe (emit e) side model (initial model.cells heap) = Part.some (result model.cells value) ↔
      nativeReturns (e.graph side) model heap value.1 value.2

namespace Backend

/-- Translate generated equations via their retained native source. -/
def translate (sender receiver : Backend) (s : sender.Sentence P) : receiver.Sentence P :=
  receiver.emit (sender.source s)

/-- A port map re-emits in the destination signature. -/
def reemit (backend : Backend) (h : P ⟶ Q) (s : backend.Sentence P) : backend.Sentence Q :=
  backend.emit ((backend.source s).map h)

/-- Compare actual partial observations at every initialized backend state. -/
def Holds (backend : Backend) (s : backend.Sentence P) (model : EntryModel P) : Prop :=
  ∀ initial, backend.observe s .lhs model initial = backend.observe s .rhs model initial

def room (backend : Backend) (P : EntrySignature) : Room.{0, 0, 0} where
  Sen := backend.Sentence P
  Mod := (Institution.room P).Mod
  Sat model s := backend.Holds s model.as

/-- Source valuations obtained by pulling back target valuations at a fixed
cell count. Identifying source ports can give a proper model image. -/
def InReductImage (h : P ⟶ Q) (cells : Nat) (model : EntryModel P) : Prop :=
  ∃ input : Tuple (Val cells) Q.args, reduct h (⟨cells, input⟩ : EntryModel Q) = model

end Backend

end Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution

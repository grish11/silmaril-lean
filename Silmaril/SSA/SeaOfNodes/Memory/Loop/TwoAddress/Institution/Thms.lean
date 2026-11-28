module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Observation

/-! Satisfaction for actual emitted two-address loops at their canonical runtime model. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution

open CategoryTheory
open RVSDG.NestedTheta.Institution
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {P : EntrySignature}

theorem memrefReturns_iff_native (graph : Graph P.args) (model : EntryModel P)
    (initial : Heap model.cells) (word : Word) (final : Heap model.cells) :
    memrefReturns graph model initial word final ↔ nativeReturns graph model initial word final :=
  Proofs.memrefReturns_iff_native graph model initial word final

theorem petriReturns_iff_native (graph : Graph P.args) (model : EntryModel P)
    (initial : Heap model.cells) (word : Word) (final : Heap model.cells) :
    petriReturns graph model initial word final ↔ nativeReturns graph model initial word final :=
  Proofs.petriReturns_iff_native graph model initial word final

/-- The existing partial runtime observer returns the encoded word and all
cells exactly when the native loop has that finite return. -/
theorem runtimeObserve_eq_some_iff_native (graph : Graph P.args) (model : EntryModel P)
    (initial : Heap model.cells) (word : Word) (final : Heap model.cells) :
    runtimeObserve graph model initial = Part.some (encodeResult word final) ↔
      nativeReturns graph model initial word final :=
  Proofs.runtimeObserve_eq_some_iff_native graph model initial word final

/-- Equality of the canonical partial observations is equality of the
complete finite results. -/
theorem runtimeObserve_eq_iff_native (lhs rhs : Graph P.args) (model : EntryModel P)
    (initial : Heap model.cells) :
    runtimeObserve lhs model initial = runtimeObserve rhs model initial ↔
      ∀ word final, nativeReturns lhs model initial word final ↔ nativeReturns rhs model initial word final :=
  Proofs.runtimeObserve_eq_iff_native lhs rhs model initial

theorem runtimeObserve_dom_iff_native (graph : Graph P.args) (model : EntryModel P)
    (initial : Heap model.cells) :
    (runtimeObserve graph model initial).Dom ↔ ∃ word final, nativeReturns graph model initial word final :=
  Proofs.runtimeObserve_dom_iff_native graph model initial

/-- An absent partial value means that there is no finite return at this
entry. It makes no claim about infinite coloured firing schedules. -/
theorem runtimeObserve_eq_none_iff_native (graph : Graph P.args) (model : EntryModel P)
    (initial : Heap model.cells) :
    runtimeObserve graph model initial = Part.none ↔ (nativeReturns graph model).NoReturn initial :=
  Proofs.runtimeObserve_eq_none_iff_native graph model initial

theorem memref_satisfaction (s : Sentence P) (model : EntryModel P) :
    s.HoldsWith (memrefReturns · model) ↔ s.Holds model :=
  Proofs.memref_satisfaction s model

theorem petri_satisfaction (s : Sentence P) (model : EntryModel P) :
    s.HoldsWith (petriReturns · model) ↔ s.Holds model :=
  Proofs.petri_satisfaction s model

/-- The existing room quantifies over all typed valuations and initialized
heaps at the canonical runtime's cell count. -/
theorem numbered_satisfaction (s : Sentence P) (cells : Nat) :
    (RuntimeObservation.room.{0, 0, 0} target).Sat (Discrete.mk (thetaRuntime cells)) (translate s) ↔
      s.HoldsAt cells :=
  Proofs.numbered_satisfaction s cells

/-- Both native sentence forms preserve and reflect satisfaction in the
numbered room and under actual MemRef and coloured Petri observations.
The two backends may use independent finite witnesses at each entry. -/
theorem satisfaction (s : Sentence P) (cells : Nat) :
    ((RuntimeObservation.room.{0, 0, 0} target).Sat (Discrete.mk (thetaRuntime cells)) (translate s) ↔
      s.HoldsAt cells) ∧ (s.MemRefHolds cells ↔ s.HoldsAt cells) ∧ (s.PetriHolds cells ↔ s.HoldsAt cells) :=
  ⟨numbered_satisfaction s cells, forall_congr' fun input => memref_satisfaction s ⟨cells, input⟩,
    forall_congr' fun input => petri_satisfaction s ⟨cells, input⟩⟩

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution

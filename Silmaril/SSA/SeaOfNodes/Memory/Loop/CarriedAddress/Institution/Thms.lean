module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.Reindex
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.Runtime
import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Petri.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.Thms

/-! Typed reindexing and complete finite observations of the actual lowerings. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution

open CategoryTheory Silmaril.Logic.Institution
open SeaOfNodes.Loop (Incoming)
open Memory.Diamond.Institution (reduct reduct_id reduct_comp)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {P Q R : EntrySignature}

@[simp] theorem mapGraph_id (graph : Graph P.args) : mapGraph (𝟙 P) graph = graph :=
  Proofs.mapGraph_id graph

theorem mapGraph_comp (h : P ⟶ Q) (k : Q ⟶ R) (graph : Graph P.args) :
    mapGraph (h ≫ k) graph = mapGraph k (mapGraph h graph) :=
  Proofs.mapGraph_comp h k graph

/-- Both arrival columns and all invariant arguments commute with the
typed entry reduct, including at a post-store heap. -/
theorem step_mapGraph (h : P ⟶ Q) (graph : Graph P.args) (model : EntryModel Q)
    (arrival : Incoming) (heap : Heap model.cells) :
    (mapGraph h graph).step model.input arrival heap = graph.step (reduct h model).input arrival heap :=
  Proofs.step_mapGraph h graph model arrival heap

theorem evalWithin_mapGraph (h : P ⟶ Q) (graph : Graph P.args) (model : EntryModel Q)
    (budget : Nat) (arrival : Incoming) (heap : Heap model.cells) :
    (mapGraph h graph).evalWithin model.input budget arrival heap =
      graph.evalWithin (reduct h model).input budget arrival heap :=
  Proofs.evalWithin_mapGraph h graph model budget arrival heap

theorem nativeReturns_mapGraph (h : P ⟶ Q) (graph : Graph P.args) (model : EntryModel Q)
    (initial : Heap model.cells) (word : Word) (final : Heap model.cells) :
    nativeReturns (mapGraph h graph) model initial word final ↔
      nativeReturns graph (reduct h model) initial word final := by
  simp only [nativeReturns, evalWithin_mapGraph]
  rfl

@[simp] theorem Equation.map_id (e : Equation P) : e.map (𝟙 P) = e := by
  cases e
  simp only [Equation.map, mapGraph_id]

theorem Equation.map_comp (h : P ⟶ Q) (k : Q ⟶ R) (e : Equation P) :
    e.map (h ≫ k) = (e.map h).map k := by
  simp only [Equation.map, mapGraph_comp]

theorem Equation.satisfaction (h : P ⟶ Q) (e : Equation P) (model : EntryModel Q) :
    (e.map h).Holds model ↔ e.Holds (reduct h model) := by
  simp only [Equation.Holds, Equation.HoldsWith, Equation.map, nativeReturns_mapGraph]
  rfl

/-- The existing room interface reindexes each equation along a typed entry map. -/
@[expose] def corridor (h : P ⟶ Q) : room P ⟶ room Q :=
  ⟨Equation.map h, Discrete.functor (fun model => Discrete.mk (reduct h model)),
    fun model e => e.satisfaction h model.as⟩

theorem corridor_id (P : EntrySignature) : corridor (𝟙 P) = 𝟙 (room P) :=
  Room.hom_ext (funext Equation.map_id)
    (Discrete.functor_ext fun model => congrArg Discrete.mk (reduct_id model))

theorem corridor_comp (h : P ⟶ Q) (k : Q ⟶ R) : corridor (h ≫ k) = corridor h ≫ corridor k :=
  Room.hom_ext (funext (Equation.map_comp h k))
    (Discrete.functor_ext fun model => congrArg Discrete.mk (reduct_comp h k model))

/-- The address-Phi equations over the existing memory entry signatures and models. -/
@[expose] def inst : Inst.{0, 0, 0, 0, 0} where
  Sign := EntrySignature
  I := ⟨room, corridor, corridor_id, corridor_comp⟩

/-- The complete result has a finite coloured trace from the emitted entry
marking exactly when it has a finite native observation. -/
theorem petriReturns_iff_native (graph : Graph P.args) (model : EntryModel P)
    (initial : Heap model.cells) (word : Word) (final : Heap model.cells) :
    petriReturns graph model initial word final ↔ nativeReturns graph model initial word final :=
  Petri.lower_finishes_iff graph model.input initial word final

/-- The emitted MemRef CFG uses its own budget witness for the same observation. -/
theorem memrefReturns_iff_native (graph : Graph P.args) (model : EntryModel P)
    (initial : Heap model.cells) (word : Word) (final : Heap model.cells) :
    memrefReturns graph model initial word final ↔ nativeReturns graph model initial word final :=
  (Petri.finishes_iff_memref_run graph model.input initial word final).symm.trans
    (petriReturns_iff_native graph model initial word final)

theorem petri_no_return_iff_native (graph : Graph P.args) (model : EntryModel P) (initial : Heap model.cells) :
    (petriReturns graph model).NoReturn initial ↔ (nativeReturns graph model).NoReturn initial := by
  simp only [Observation.NoReturn, petriReturns_iff_native]

theorem memref_no_return_iff_native (graph : Graph P.args) (model : EntryModel P) (initial : Heap model.cells) :
    (memrefReturns graph model).NoReturn initial ↔ (nativeReturns graph model).NoReturn initial := by
  simp only [Observation.NoReturn, memrefReturns_iff_native]

/-- Equality of complete Petri observations preserves and reflects satisfaction. -/
theorem petri_satisfaction (e : Equation P) (model : EntryModel P) :
    petriHolds e model ↔ e.Holds model := by
  simp only [petriHolds, Equation.Holds, Equation.HoldsWith, petriReturns_iff_native]

/-- Equality of complete MemRef CFG observations preserves and reflects satisfaction. -/
theorem memref_satisfaction (e : Equation P) (model : EntryModel P) :
    memrefHolds e model ↔ e.Holds model := by
  simp only [memrefHolds, Equation.Holds, Equation.HoldsWith, memrefReturns_iff_native]

theorem petri_satisfaction_iff_memref (e : Equation P) (model : EntryModel P) :
    petriHolds e model ↔ memrefHolds e model :=
  (petri_satisfaction e model).trans (memref_satisfaction e model).symm

/-- Re-emission at renamed ports agrees with pulling back the typed valuation. -/
theorem petri_satisfaction_reindex (h : P ⟶ Q) (e : Equation P) (model : EntryModel Q) :
    petriHolds (e.map h) model ↔ petriHolds e (reduct h model) :=
  (petri_satisfaction _ _).trans ((e.satisfaction h model).trans (petri_satisfaction _ _).symm)

theorem memref_satisfaction_reindex (h : P ⟶ Q) (e : Equation P) (model : EntryModel Q) :
    memrefHolds (e.map h) model ↔ memrefHolds e (reduct h model) :=
  (memref_satisfaction _ _).trans ((e.satisfaction h model).trans (memref_satisfaction _ _).symm)

/-- The repository's existing nested RVSDG observer factors the finite
observation through the canonical runtime at the encoded entry. -/
theorem runtimeObserve_eq_some_iff_native (graph : Graph P.args) (model : EntryModel P)
    (initial : Heap model.cells) (word : Word) (final : Heap model.cells) :
    runtimeObserve graph model initial = Part.some (encodeResult word final) ↔
      nativeReturns graph model initial word final :=
  Proofs.runtimeObserve_eq_some_iff_native graph model initial word final

theorem runtime_no_return_iff_native (graph : Graph P.args) (model : EntryModel P) (initial : Heap model.cells) :
    runtimeObserve graph model initial = Part.none ↔ (nativeReturns graph model).NoReturn initial :=
  Proofs.runtime_no_return_iff_native graph model initial

/-- Compare the two actual nested graphs at the canonical encoded entry
for each heap, sharing the fixed typed valuation from the native model. -/
theorem runtime_satisfaction (e : Equation P) (model : EntryModel P) :
    (∀ initial, runtimeObserve e.lhs model initial = runtimeObserve e.rhs model initial) ↔ e.Holds model :=
  Proofs.runtime_satisfaction e model

end Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution

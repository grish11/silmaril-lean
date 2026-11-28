module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Reindex.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Reindex.Correctness
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.Thms

/-! The two-address native institution over typed capture-port maps. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution

open CategoryTheory Silmaril.Logic.Institution
open Memory.Diamond.Institution (pullInput reduct reduct_id reduct_comp)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {P Q R : EntrySignature}

@[simp] theorem mapGraph_id (graph : Graph P.args) : mapGraph (𝟙 P) graph = graph :=
  Proofs.mapGraph_id graph

theorem mapGraph_comp (h : P ⟶ Q) (k : Q ⟶ R) (graph : Graph P.args) :
    mapGraph (h ≫ k) graph = mapGraph k (mapGraph h graph) :=
  Proofs.mapGraph_comp h k graph

/-- Pull back the captured operands while retaining both live header addresses. -/
theorem pull_operands (h : P ⟶ Q) (model : EntryModel Q) (header : Header model.cells) :
    pullInput (liftAddresses h).port (header.operands model.input) = header.operands (reduct h model).input :=
  Proofs.pull_operands h model header

theorem step_mapGraph (h : P ⟶ Q) (graph : Graph P.args) (model : EntryModel Q)
    (header : Header model.cells) :
    (mapGraph h graph).step model.input header = graph.step (reduct h model).input header :=
  Proofs.step_mapGraph h graph model header

theorem nativeReturns_mapGraph (h : P ⟶ Q) (graph : Graph P.args) (model : EntryModel Q)
    (initial : Heap model.cells) (word : Word) (final : Heap model.cells) :
    nativeReturns (mapGraph h graph) model initial word final ↔
      nativeReturns graph (reduct h model) initial word final :=
  Proofs.nativeReturns_mapGraph h graph model initial word final

@[simp] theorem Sentence.map_id (s : Sentence P) : s.map (𝟙 P) = s := by
  cases s <;> simp only [Sentence.map, mapGraph_id]

theorem Sentence.map_comp (h : P ⟶ Q) (k : Q ⟶ R) (s : Sentence P) :
    s.map (h ≫ k) = (s.map h).map k := by
  cases s <;> simp only [Sentence.map, mapGraph_comp]

/-- Both sentence forms commute with the typed entry valuation reduct. -/
theorem Sentence.satisfaction_map (h : P ⟶ Q) (s : Sentence P) (model : EntryModel Q) :
    (s.map h).Holds model ↔ s.Holds (reduct h model) := by
  cases s <;> (simp only [Sentence.map, Sentence.Holds, Sentence.HoldsWith, nativeReturns_mapGraph]; rfl)

def corridor (h : P ⟶ Q) : room P ⟶ room Q :=
  ⟨Sentence.map h, Discrete.functor (fun m => Discrete.mk (reduct h m)),
    fun m s => s.satisfaction_map h m.as⟩

theorem corridor_id (P : EntrySignature) : corridor (𝟙 P) = 𝟙 (room P) :=
  Room.hom_ext (funext Sentence.map_id)
    (Discrete.functor_ext fun m => congrArg Discrete.mk (reduct_id m))

theorem corridor_comp (h : P ⟶ Q) (k : Q ⟶ R) : corridor (h ≫ k) = corridor h ≫ corridor k :=
  Room.hom_ext (funext (Sentence.map_comp h k))
    (Discrete.functor_ext fun m => congrArg Discrete.mk (reduct_comp h k m))

def inst : Inst.{0, 0, 0, 0, 0} where
  Sign := EntrySignature
  I := ⟨room, corridor, corridor_id, corridor_comp⟩

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution

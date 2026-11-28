module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction.Institution.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Boundary.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Reindex.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction.InstitutionProofs

open CategoryTheory
open RVSDG (Tuple)
open Memory.Diamond.Institution (reduct)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {P Q R : EntrySignature}

theorem program_map_id (p : Program P) : p.map (𝟙 P) = p := by
  rcases p with ⟨⟨next, first, second, firstWiring⟩, last, third, secondWiring⟩
  simp only [Program.map, Linked.Satisfaction.Program.map]
  rw [mapGraph_id (P := P) first]
  exact congrArg (fun wiring => Program.mk ⟨next, first, second, wiring⟩ last third secondWiring) firstWiring.map_id

theorem program_map_comp (h : P ⟶ Q) (k : Q ⟶ R) (p : Program P) :
    p.map (h ≫ k) = (p.map h).map k := by
  rcases p with ⟨⟨next, first, second, firstWiring⟩, last, third, secondWiring⟩
  simp only [Program.map, Linked.Satisfaction.Program.map]
  rw [mapGraph_comp h k first]
  exact congrArg (fun wiring =>
    Program.mk ⟨next, mapGraph k (mapGraph h first), second, wiring⟩ last third secondWiring)
      (firstWiring.map_comp (EntrySignature.Hom.port h) (EntrySignature.Hom.port k))

theorem modelReduct_surjective_iff (backend : Backend) (h : P ⟶ Q) :
    Function.Surjective (modelReduct backend h).obj ↔
      ∀ cells (input : Tuple (Val cells) P.args), Linked.Satisfaction.InReductImage h input := by
  constructor
  · intro onto cells input
    obtain ⟨target, equal⟩ := onto (Discrete.mk ⟨cells, input⟩)
    change Discrete (EntryModel Q) at target
    rcases target with ⟨⟨targetCells, targetInput⟩⟩
    have pulled : reduct h ⟨targetCells, targetInput⟩ = ⟨cells, input⟩ := congrArg Discrete.as equal
    have sameCells : targetCells = cells := congrArg EntryModel.cells pulled
    subst targetCells
    exact ⟨targetInput, pulled⟩
  · intro covers source
    obtain ⟨input, equal⟩ := covers source.as.cells source.as.input
    exact ⟨Discrete.mk ⟨source.as.cells, input⟩, congrArg Discrete.mk equal⟩

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction.InstitutionProofs

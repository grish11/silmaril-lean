module

public import Silmaril.Semantics.Region.Tree.Examples.Defs
public import Silmaril.Semantics.Region.Tree.CFG.Thms
public import Silmaril.Semantics.Region.Tree.Finite.Thms
import Silmaril.Proofs.Semantics.Region.TreeExamples

@[expose] public section
namespace Silmaril.Semantics.Region.Tree.Examples

theorem sparse_rooted : sparse.shape.Rooted := Proofs.sparse_rooted

theorem sparse_terminal : sparse.TerminalLeaves := Proofs.sparse_terminal

theorem sparse_completeLeaves : sparse.CompleteLeaves := Proofs.sparse_completeLeaves

def sparseStrict : LabelLeafTree (Fin 3) Unit Nat :=
  ⟨sparse, sparse_rooted, sparse_terminal, sparse_completeLeaves⟩

theorem sparse_incomplete : ¬ FullyAnnotated sparse := Proofs.sparse_incomplete

theorem sparse_contracts : sparse.frontier.child 0 2 := Proofs.sparse_contracts

theorem sparse_leaf_not_exit : 2 ∈ sparse.leafLabels ∧ 2 ∉ sparseRow.exits := ⟨⟨2, rfl⟩, by simp [sparseRow]⟩

/-- Incomplete optional labels cannot be lifted to a fully annotated tree. -/
theorem sparse_not_full_image : ¬ ∃ full, embedFull full = sparse :=
  fun h => sparse_incomplete ((fullyAnnotated_iff sparse).mpr h)

theorem anonymous_edge_not_exported : 42 ∈ sparseCFG.successors 1 ∧
    ∀ a, 42 ∉ sparseCFG.flatten.successors a := Proofs.anonymous_edge_not_exported

end Silmaril.Semantics.Region.Tree.Examples

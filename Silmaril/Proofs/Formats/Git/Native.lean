module

public import Silmaril.Formats.Git.Native.Defs

public section

namespace Silmaril.Proofs.Formats.Git

open Silmaril.Formats.Git Silmaril.Formats.Git.Native
open Silmaril.Formats.Dasl.Prolly (ByteKey)

theorem native_tree_order {Name : Type} (entries : List (ByteKey × Entry Name)) :
    (treeOrder entries).Pairwise (fun left right => orderKey left ≤ orderKey right) := by
  have transitive (first middle last : ByteKey × Entry Name) :
      decide (orderKey first ≤ orderKey middle) → decide (orderKey middle ≤ orderKey last) →
      decide (orderKey first ≤ orderKey last) := by
    simpa only [decide_eq_true_eq] using (le_trans (a := orderKey first) (b := orderKey middle) (c := orderKey last))
  have total (left right : ByteKey × Entry Name) :
      decide (orderKey left ≤ orderKey right) || decide (orderKey right ≤ orderKey left) := by
    simpa only [Bool.or_eq_true, decide_eq_true_eq] using le_total (orderKey left) (orderKey right)
  simpa only [treeOrder, decide_eq_true_eq] using List.pairwise_mergeSort transitive total entries

theorem native_embedding {algorithm : Algorithm} {Name : Type} (profile : Profile algorithm String Name)
    (tree : Tree) : renderObject profile tree.toObject = renderTree profile tree := by
  induction tree with
  | file => rfl
  | dir keys children ih =>
    simp only [Tree.toObject, renderObject, renderTree]
    rw [funext ih]

end Silmaril.Proofs.Formats.Git

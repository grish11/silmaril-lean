module

public import Silmaril.Formats.Git.Defs
import Silmaril.Proofs.Formats.Git.Basic

public section

namespace Silmaril.Formats.Git

@[simp] theorem Tree.erase_indexed (tree : Tree) : tree.indexed.erase = tree :=
  Proofs.Formats.Git.erase_indexed tree

@[simp] theorem Indexed.indexed_erase {tag : Tag} (tree : Indexed tag) :
    (⟨tree.erase.tag, tree.erase.indexed⟩ : Sigma Indexed) = ⟨tag, tree⟩ :=
  Proofs.Formats.Git.indexed_erase tree

def treeEquiv : Tree ≃ Sigma Indexed where
  toFun tree := ⟨tree.tag, tree.indexed⟩
  invFun tree := tree.2.erase
  left_inv := Tree.erase_indexed
  right_inv tree := tree.2.indexed_erase

namespace Directory

variable {Key Item Out : Type} [DecidableEq Key]

theorem eq_of_lookup {left right : Directory Key Item} (same : ∀ key, left.lookup key = right.lookup key) :
    left = right := Proofs.Formats.Git.directory_ext same

theorem lookup_insert (dir : Directory Key Item) (key query : Key) (value : Item) :
    (dir.insert key value).lookup query = if query = key then some value else dir.lookup query :=
  Proofs.Formats.Git.lookup_insert dir key query value

theorem lookup_remove (dir : Directory Key Item) (key query : Key) :
    (dir.remove key).lookup query = if query = key then none else dir.lookup query :=
  Proofs.Formats.Git.lookup_remove dir key query

@[simp] theorem lookup_map (dir : Directory Key Item) (convert : Item → Out) (key : Key) :
    (dir.map convert).lookup key = (dir.lookup key).map convert := by
  by_cases hit : key ∈ dir.keys <;> simp [lookup, map, hit]

end Directory

@[simp] theorem Commit.map_id {Root Parent Meta : Type} (commit : Commit Root Parent Meta) :
    commit.map id id id = commit := by cases commit; simp [Commit.map]

@[simp] theorem ShallowTree.mapTargets_id {Key Target : Type} (tree : ShallowTree Key Target) :
    tree.mapTargets id = tree := by cases tree; rfl

end Silmaril.Formats.Git

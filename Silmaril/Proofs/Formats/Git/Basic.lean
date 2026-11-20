module

public import Silmaril.Formats.Git.Defs

public section

namespace Silmaril.Proofs.Formats.Git

open Silmaril.Formats.Git

theorem erase_indexed (tree : Tree) : tree.indexed.erase = tree := by
  induction tree with
  | file => rfl
  | dir names children ih => exact congrArg (Tree.dir names) (funext ih)

theorem indexed_erase {tag : Tag} (tree : Indexed tag) :
    (⟨tree.erase.tag, tree.erase.indexed⟩ : Sigma Indexed) = ⟨tag, tree⟩ := by
  induction tree with
  | blob => rfl
  | tree names modes children ih =>
    exact congrArg (fun entries : ↥names → Sigma Indexed =>
      (⟨.directory, .tree names (fun name => (entries name).1) (fun name => (entries name).2)⟩ : Sigma Indexed))
      (funext ih)

theorem directory_ext {Key Item : Type} [DecidableEq Key] {left right : Directory Key Item}
    (same : ∀ key, left.lookup key = right.lookup key) : left = right := by
  cases left with | mk left getLeft =>
  cases right with | mk right getRight =>
    have keys : left = right := Finset.ext fun key => by
      specialize same key
      by_cases inLeft : key ∈ left <;> by_cases inRight : key ∈ right <;>
        simp_all [Directory.lookup]
    subst right
    congr
    funext key
    exact Option.some.inj (by simpa [Directory.lookup, key.property] using same key.val)

theorem lookup_insert {Key Item : Type} [DecidableEq Key] (dir : Directory Key Item)
    (key query : Key) (value : Item) :
    (dir.insert key value).lookup query = if query = key then some value else dir.lookup query := by
  by_cases same : query = key
  · subst query; simp [Directory.lookup, Directory.insert]
  · by_cases hit : query ∈ dir.keys <;> simp [Directory.lookup, Directory.insert, same, hit]

theorem lookup_remove {Key Item : Type} [DecidableEq Key] (dir : Directory Key Item)
    (key query : Key) : (dir.remove key).lookup query = if query = key then none else dir.lookup query := by
  by_cases same : query = key
  · subst query; simp [Directory.lookup, Directory.remove]
  · by_cases hit : query ∈ dir.keys <;> simp [Directory.lookup, Directory.remove, same, hit]

end Silmaril.Proofs.Formats.Git

module

public import Silmaril.Formats.Git.Native.Defs
import Silmaril.Proofs.Formats.Git.Native

public section

namespace Silmaril.Formats.Git.Native

variable {algorithm : Algorithm} {Key Name : Type}

@[simp] theorem loose_size (kind : Kind) (payload : ByteArray) :
    (loose kind payload).size = (header kind payload.size).size + payload.size := by simp [loose]

theorem treeOrder_sorted (entries : List (Formats.Dasl.Prolly.ByteKey × Entry Name)) :
    (treeOrder entries).Pairwise (fun left right => orderKey left ≤ orderKey right) :=
  Proofs.Formats.Git.native_tree_order entries

theorem View.target_matches {profile : Profile algorithm Key Name}
    {rel : Semantics.Naming.Relation Name ByteArray} (compatible : profile.Compatible rel) (view : View Name) :
    view.Matches rel (view.target profile.assign) := by
  match view with | .opaque _ => rfl | .encoded bytes => exact compatible bytes

@[simp] theorem renderObject_toObject (profile : Profile algorithm String Name) (tree : Tree) :
    renderObject profile tree.toObject = renderTree profile tree := Proofs.Formats.Git.native_embedding profile tree

/-- Equality holds for every filesystem and every relation on native bytes,
including inputs rejected by the common profile. It does not assert uniqueness. -/
theorem names_toObject (profile : Profile algorithm String Name) (rel : Semantics.Naming.Relation Name ByteArray) :
    names rel (fun tree : Tree => renderObject profile tree.toObject) = names rel (renderTree profile) := by
  unfold names; simp only [renderObject_toObject]

end Silmaril.Formats.Git.Native

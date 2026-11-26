module

public import Silmaril.Semantics.ITree.Signature.Thms
import Silmaril.Proofs.Semantics.ITree.Signature.Execution

public section

namespace Silmaril.Elgot.ITree.Signature

open CategoryTheory

universe u v
variable {S T : Signature.{u}} {A B : Type v}

@[simp] theorem Hom.tree_diverge (f : S ⟶ T) :
    f.tree id (diverge : Tree S.Event A) = diverge := by
  apply out_injective
  simp [f.out_tree, out_diverge, Part.map_none]

@[simp] theorem Hom.tree_pure (f : S ⟶ T) (a : A) :
    f.tree id (pure a : Tree S.Event A) = pure a :=
  f.tree_ret id a

theorem Hom.tree_bind (f : S ⟶ T) (t : Tree S.Event A) (k : A → Tree S.Event B) :
    f.tree id (t >>= k) = (f.tree id t >>= fun a => f.tree id (k a)) :=
  Proofs.tree_bind_reindex f t k

theorem Hom.tree_iter (f : S ⟶ T) (step : A → Tree S.Event (B ⊕ A)) (x : A) :
    f.tree id (Elgot.iter step x) = Elgot.iter (fun a => f.tree id (step a)) x :=
  Proofs.tree_iter_reindex f step x

end Silmaril.Elgot.ITree.Signature

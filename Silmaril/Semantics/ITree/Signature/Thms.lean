module

public import Silmaril.Semantics.ITree.Signature.Tree.Defs
import Silmaril.Proofs.Semantics.ITree.Signature.Translation

public section

namespace Silmaril.Elgot.ITree.Signature

open CategoryTheory

universe u v w z

variable {S T U : Signature.{u}} {A : Type v} {B : Type w} {C : Type z}

/-- Compare the request and its backward reply map together, without casts. -/
theorem Hom.ext (f g : S ⟶ T)
    (h : ∀ q, (⟨f.request q, f.reply q⟩ : (p : Request T.Event) × (p.1 → q.1)) =
      ⟨g.request q, g.reply q⟩) : f = g :=
  congrArg (fun (k : (q : Request S.Event) → (p : Request T.Event) × (p.1 → q.1)) =>
    (⟨fun q => (k q).1, fun q => (k q).2⟩ : S ⟶ T)) (funext h)

@[simp] theorem ofEquiv_refl (S : Signature.{u}) :
    ofEquiv (S := S) (T := S) (SignatureEquiv.refl S.Event) = 𝟙 S := rfl

theorem ofEquiv_trans (e : SignatureEquiv S.Event T.Event) (f : SignatureEquiv T.Event U.Event) :
    ofEquiv (S := S) (T := U) (e.trans f) =
      ofEquiv (S := S) (T := T) e ≫ ofEquiv (S := T) (T := U) f := rfl

@[simp] theorem inl_desc (f : S ⟶ U) (g : T ⟶ U) : inl S T ≫ desc f g = f := rfl

@[simp] theorem inr_desc (f : S ⟶ U) (g : T ⟶ U) : inr S T ≫ desc f g = g := rfl

theorem desc_eta (f : S.sum T ⟶ U) : desc (inl S T ≫ f) (inr S T ≫ f) = f :=
  Hom.ext _ _ fun ⟨_, ev⟩ => by cases ev <;> rfl

@[simp] theorem Hom.tree_id (t : Tree S.Event A) : (𝟙 S : S ⟶ S).tree id t = t :=
  Tree.ext fun n => Proofs.approx_id n (t.observe n)

theorem Hom.tree_comp (f : S ⟶ T) (g : T ⟶ U) (a : A → B) (b : B → C) (t : Tree S.Event A) :
    (f ≫ g).tree (b ∘ a) t = g.tree b (f.tree a t) :=
  Tree.ext fun n => Proofs.approx_comp f g a b n (t.observe n)

theorem ofEquiv_tree {B : Type v} (e : SignatureEquiv S.Event T.Event) (a : A ≃ B) (t : Tree S.Event A) :
    (ofEquiv (S := S) (T := T) e).tree a t = e.tree a t :=
  Tree.ext fun n => Proofs.approx_ofEquiv e a n (t.observe n)

theorem Hom.out_tree (f : S ⟶ T) (a : A → B) (t : Tree S.Event A) :
    out (f.tree a t) = Part.map (f.visible a (f.tree a)) (out t) :=
  Proofs.out_tree f a t

@[simp] theorem Hom.tree_ret (f : S ⟶ T) (a : A → B) (b : A) :
    f.tree a (ret b) = ret (a b) := by
  apply out_injective
  rw [f.out_tree, out_ret, out_ret, Part.map_some]
  rfl

@[simp] theorem Hom.tree_vis (f : S ⟶ T) (a : A → B)
    {R : Type u} (ev : S.Event R) (k : R → Tree S.Event A) :
    f.tree a (vis ev k) = vis (f.request ⟨R, ev⟩).2
      (fun r => f.tree a (k (f.reply ⟨R, ev⟩ r))) := by
  apply out_injective
  rw [f.out_tree, out_vis, out_vis, Part.map_some]
  rfl

end Silmaril.Elgot.ITree.Signature

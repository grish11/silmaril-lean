module

public import Silmaril.SSA.Isotope.LetIter.Monadic.Reindex.Defs
public import Silmaril.Semantics.ITree.Reindex.Thms

public section

namespace Silmaril.Proofs.LetIter.Reindex

open Silmaril.Isotope Silmaril.Isotope.Semantics Silmaril.Elgot
open Silmaril.Isotope.LetIter.LocallyNameless Silmaril.Isotope.LetIter.Reindex

universe u v w r q

variable {α : Type u} {V W : α → Type v}

theorem boundEnvEquiv_snoc (e : ∀ a, V a ≃ W a) {n : Nat} {β : BoundCtx (Ty α) n}
    {A : Ty α} (ρ : BoundEnv (Ty.denote V) β) (a : Ty.denote V A) :
    boundEnvEquiv e (.snoc β A) (ρ.snoc a) =
      (boundEnvEquiv e β ρ).snoc (typeEquiv e A a) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl

variable {V W : α → Type (max (r + 1) v)}
  {E F : Type r → Type r} {Φ : Type q} [HasTy Φ (Ty α)]
  {ν : Type w} [DecidableEq ν]

set_option backward.isDefEq.respectTransparency false in
theorem denote_natural (e : ∀ a, V a ≃ W a) (sig : ITree.SignatureEquiv E F)
    (M : InstructionModel (Ty.denote V) Φ (ITree.Tree E))
    (N : InstructionModel (Ty.denote W) Φ (ITree.Tree F))
    (primitive : ∀ f x, sig.tree (typeEquiv e (instrTrg f)) (M.eval f x) =
      N.eval f (typeEquiv e (instrSrc f) x))
    {Γ : Ctx ν (Ty α)} {n : Nat} {β : BoundCtx (Ty α) n} {t : Tm ν Φ n} {A : Ty α}
    (d : Derivation Φ Γ β t A) (γ : FreeEnv (Ty.denote V) Γ) (ρ : BoundEnv (Ty.denote V) β) :
    sig.tree (typeEquiv e A) (d.denote (Ty.denote V) M γ ρ) =
      d.denote (Ty.denote W) N (freeEnvEquiv e Γ γ) (boundEnvEquiv e β ρ) := by
  have pure_natural {X Y : Type (max (r + 1) v)} (a : X ≃ Y) (x : X) :
      sig.tree a (pure x) = pure (a x) := sig.tree_ret a x
  have sequence {X X' Y Y' : Type (max (r + 1) v)} (a : X ≃ X') (b : Y ≃ Y')
      {t : ITree.Tree E X} {t' : ITree.Tree F X'} {k : X → ITree.Tree E Y}
      {l : X' → ITree.Tree F Y'} (ht : sig.tree a t = t')
      (hk : ∀ x, sig.tree b (k x) = l (a x)) :
      sig.tree b (t >>= k) = (t' >>= l) := by
    rw [sig.tree_bind a b t k l hk, ht]
  have coprodValue (U : α → Type (max (r + 1) v)) (A B : Ty α)
      (s : Ty.denote U (Ty.coprod A B)) :
      CoproductModel.coprodEquiv (D := Ty.denote U) A B s = s := rfl
  have bindPure {G : Type r → Type r} {X : Type (max (r + 1) v)} (t : ITree.Tree G X) :
      (t >>= pure) = t := bind_pure t
  induction d with
  | fv h => exact pure_natural _ _
  | bv => exact pure_natural _ _
  | op da ih =>
    simp only [Derivation.denote]
    exact sequence _ _ (ih ρ) (primitive _)
  | let₁ da db iha ihb =>
    simp only [Derivation.denote]
    apply sequence _ _ (iha ρ)
    intro a
    simpa only [boundEnvEquiv_snoc] using ihb (ρ.snoc a)
  | unit => exact pure_natural _ _
  | pair da db iha ihb =>
    simp only [Derivation.denote]
    apply sequence _ _ (iha ρ)
    intro a
    apply sequence _ _ (ihb ρ)
    intro b
    exact pure_natural _ _
  | let₂ da dc iha ihc =>
    simp only [Derivation.denote]
    apply sequence _ _ (iha ρ)
    intro ab
    exact (ihc ((ρ.snoc ab.1).snoc ab.2)).trans
      (by rw [boundEnvEquiv_snoc, boundEnvEquiv_snoc]; rfl)
  | inl da ih =>
    simp only [Derivation.denote]
    apply sequence _ _ (ih ρ)
    intro a
    exact pure_natural _ _
  | inr db ih =>
    simp only [Derivation.denote]
    apply sequence _ _ (ih ρ)
    intro b
    exact pure_natural _ _
  | case de dl dr ihe ihl ihr =>
    simp only [Derivation.denote, coprodValue]
    apply sequence _ _ (ihe ρ)
    intro s
    cases s with
    | inl a => exact (ihl (ρ.snoc a)).trans (by rw [boundEnvEquiv_snoc]; rfl)
    | inr b => exact (ihr (ρ.snoc b)).trans (by rw [boundEnvEquiv_snoc]; rfl)
  | abort da ih =>
    simp only [Derivation.denote]
    apply sequence _ _ (ih ρ)
    intro z
    cases z
  | iter da db iha ihb =>
    simp only [Derivation.denote, coprodValue, bindPure]
    apply sequence _ _ (iha ρ)
    intro a
    apply sig.tree_iter
    intro x
    have h := ihb (ρ.snoc x)
    rw [boundEnvEquiv_snoc] at h
    exact h

theorem denoteClosed_natural (e : ∀ a, V a ≃ W a) (sig : ITree.SignatureEquiv E F)
    (M : InstructionModel (Ty.denote V) Φ (ITree.Tree E))
    (N : InstructionModel (Ty.denote W) Φ (ITree.Tree F))
    (primitive : ∀ f x, sig.tree (typeEquiv e (instrTrg f)) (M.eval f x) =
      N.eval f (typeEquiv e (instrSrc f) x))
    {t : Tm Empty Φ 0} {A : Ty α} (d : Derivation Φ (.nil : Ctx Empty (Ty α)) .nil t A) :
    sig.tree (typeEquiv e A) (d.denoteClosed (Ty.denote V) M) =
      d.denoteClosed (Ty.denote W) N := by
  unfold Derivation.denoteClosed
  rw [denote_natural e sig M N primitive]
  congr 1
  · funext x
    exact x.elim
  · funext i
    exact Fin.elim0 i

end Silmaril.Proofs.LetIter.Reindex

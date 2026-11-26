module

public import Silmaril.SSA.Isotope.LetIter.Monadic.Reindex.Defs
public import Silmaril.Semantics.ITree.Reindex.Thms

import Silmaril.Proofs.SSA.Isotope.LetIter.Monadic.Reindex.Evaluation

/-! # Representation naturality of native LetIter evaluation -/

public section

namespace Silmaril.Isotope.LetIter.Reindex

open Silmaril.Isotope.Semantics Silmaril.Elgot
open LocallyNameless

universe u v w q r

variable {α : Type u} {V W : α → Type v}

/-- Extending a bound valuation commutes with transport. -/
@[simp] theorem boundEnvEquiv_snoc (e : ∀ a, V a ≃ W a) {n : Nat} {β : BoundCtx (Ty α) n}
    {A : Ty α} (ρ : BoundEnv (Ty.denote V) β) (a : Ty.denote V A) :
    boundEnvEquiv e (.snoc β A) (ρ.snoc a) =
      (boundEnvEquiv e β ρ).snoc (typeEquiv e A a) :=
  Silmaril.Proofs.LetIter.Reindex.boundEnvEquiv_snoc e ρ a

variable {V W : α → Type (max (r + 1) v)}
  {E F : Type r → Type r} {Φ : Type q} [HasTy Φ (Ty α)]
  {ν : Type w} [DecidableEq ν]

/-- Evaluate the same native derivation in both representations. Only the
primitive interpretations must be shown to commute. Tree transport already
preserves returns, sequencing and general iteration. -/
theorem denote_natural (e : ∀ a, V a ≃ W a) (sig : ITree.SignatureEquiv E F)
    (M : InstructionModel (Ty.denote V) Φ (ITree.Tree E))
    (N : InstructionModel (Ty.denote W) Φ (ITree.Tree F))
    (primitive : ∀ f x, sig.tree (typeEquiv e (instrTrg f)) (M.eval f x) =
      N.eval f (typeEquiv e (instrSrc f) x))
    {Γ : Ctx ν (Ty α)} {n : Nat} {β : BoundCtx (Ty α) n} {t : Tm ν Φ n} {A : Ty α}
    (d : Derivation Φ Γ β t A) (γ : FreeEnv (Ty.denote V) Γ) (ρ : BoundEnv (Ty.denote V) β) :
    sig.tree (typeEquiv e A) (d.denote (Ty.denote V) M γ ρ) =
      d.denote (Ty.denote W) N (freeEnvEquiv e Γ γ) (boundEnvEquiv e β ρ) :=
  Silmaril.Proofs.LetIter.Reindex.denote_natural e sig M N primitive d γ ρ

theorem denoteClosed_natural (e : ∀ a, V a ≃ W a) (sig : ITree.SignatureEquiv E F)
    (M : InstructionModel (Ty.denote V) Φ (ITree.Tree E))
    (N : InstructionModel (Ty.denote W) Φ (ITree.Tree F))
    (primitive : ∀ f x, sig.tree (typeEquiv e (instrTrg f)) (M.eval f x) =
      N.eval f (typeEquiv e (instrSrc f) x))
    {t : Tm Empty Φ 0} {A : Ty α} (d : Derivation Φ (.nil : Ctx Empty (Ty α)) .nil t A) :
    sig.tree (typeEquiv e A) (d.denoteClosed (Ty.denote V) M) =
      d.denoteClosed (Ty.denote W) N :=
  Silmaril.Proofs.LetIter.Reindex.denoteClosed_natural e sig M N primitive d

end Silmaril.Isotope.LetIter.Reindex

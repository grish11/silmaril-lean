module

public import Silmaril.SSA.Isotope.LetIter.Heap.Thms
public import Silmaril.SSA.Isotope.LetIter.Monadic.Reindex.Thms

/-! # Reindexing native LetIter heap evaluations and their finite traces -/

public section

namespace Silmaril.Isotope.LetIter.Heap

open Silmaril.Isotope.Semantics Silmaril.Elgot LocallyNameless

universe u

variable {I J : Type} {ν : Type u} [DecidableEq ν]
  {Γ : Ctx ν (Ty Unit)} {n : Nat} {β : BoundCtx (Ty Unit) n} {t : Tm ν Prim n} {A : Ty Unit}

/-- Native heap evaluation commutes with reindexing, including in open terms
and arbitrary iteration bodies. -/
theorem denote_natural (e : I ≃ J) (d : Derivation Prim Γ β t A)
    (γ : FreeEnv (EvalType I) Γ) (ρ : BoundEnv (EvalType I) β) :
    (signatureEquiv e).tree (resultEquiv e A) (d.denote (EvalType I) (instructions I) γ ρ) =
      d.denote (EvalType J) (instructions J)
        (Reindex.freeEnvEquiv (Reindex.Structured.liftedEquiv (fun _ => e)) Γ γ)
        (Reindex.boundEnvEquiv (Reindex.Structured.liftedEquiv (fun _ => e)) β ρ) :=
  Reindex.denote_natural.{0, 0, u, 0, 0} _ _ _ _ (Reindex.Structured.call_natural (fun _ => e)) d γ ρ

theorem denoteClosed_natural (e : I ≃ J)
    {t : Tm Empty Prim 0} (d : Derivation Prim (.nil : Ctx Empty (Ty Unit)) .nil t A) :
    (signatureEquiv e).tree (resultEquiv e A) (d.denoteClosed (EvalType I) (instructions I)) =
      d.denoteClosed (EvalType J) (instructions J) :=
  Reindex.denoteClosed_natural.{0, 0, 0, 0} _ _ _ _ (Reindex.Structured.call_natural (fun _ => e)) d

/-- Transport the valuation, initial store and finite observation together,
and compare membership under native evaluation in the two representations. -/
theorem denote_trace_equivariant (e : I ≃ J) (d : Derivation Prim Γ β t A)
    (γ : FreeEnv (EvalType I) Γ) (ρ : BoundEnv (EvalType I) β)
    (s : Store I) (p : ITree.Trace (Event I) (EvalType I A)) :
    ITree.HandledTrace step (storeEquiv e s)
      (d.denote (EvalType J) (instructions J)
        (Reindex.freeEnvEquiv (Reindex.Structured.liftedEquiv (fun _ => e)) Γ γ)
        (Reindex.boundEnvEquiv (Reindex.Structured.liftedEquiv (fun _ => e)) β ρ))
      ((signatureEquiv e).trace (resultEquiv e A) p) ↔
    ITree.HandledTrace step s (d.denote (EvalType I) (instructions I) γ ρ) p := by
  rw [← denote_natural e d γ ρ]
  exact trace_equivariant e (resultEquiv e A) s _ p

/-- The full finite trace language of a closed native term in the new
representation is the image of its language in the original representation. -/
theorem denoteClosed_trace_image (e : I ≃ J)
    {t : Tm Empty Prim 0} (d : Derivation Prim (.nil : Ctx Empty (Ty Unit)) .nil t A)
    (s : Store I) (p' : ITree.Trace (Event J) (EvalType J A)) :
    ITree.HandledTrace step (storeEquiv e s) (d.denoteClosed (EvalType J) (instructions J)) p' ↔
      ∃ p, ITree.HandledTrace step s (d.denoteClosed (EvalType I) (instructions I)) p ∧
        (signatureEquiv e).trace (resultEquiv e A) p = p' := by
  rw [← denoteClosed_natural e d]
  exact trace_image e (resultEquiv e A) s _ p'

/-- A closed native term started in the empty store admits exactly the
same finite observations after any permutation of pointer names. -/
theorem denoteClosed_trace_rename_iff (e : Equiv.Perm I)
    {t : Tm Empty Prim 0} (d : Derivation Prim (.nil : Ctx Empty (Ty Unit)) .nil t A)
    (p : ITree.Trace (Event I) (EvalType I A)) :
    ITree.HandledTrace step (emptyStore I) (d.denoteClosed (EvalType I) (instructions I))
      ((signatureEquiv e).trace (resultEquiv e A) p) ↔
    ITree.HandledTrace step (emptyStore I) (d.denoteClosed (EvalType I) (instructions I)) p :=
  trace_fixed_iff e (resultEquiv e A) (emptyStore I) _ (storeEquiv_empty e)
    (denoteClosed_natural e d) p

end Silmaril.Isotope.LetIter.Heap

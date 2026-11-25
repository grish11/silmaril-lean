module

public import Silmaril.Raw.SSA.Thesis.LambdaIter.Models.SynElgot
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

public section

universe u w q

namespace Silmaril.Thesis.LambdaIter

open LocallyNameless CategoryTheory CategoryTheory.Limits

namespace Syn.SynCat

private theorem instantiate_lift {ν : Type w} {Φ : Type q} {n : Nat}
    (t a : Tm ν Φ n) :
    Tm.instantiate (Tm.lift t) a = t := by
  simp only [Tm.lift, Tm.instantiate, Syntax.bsubst_rename]
  change Tm.bsubst (fun i => Tm.bv i) t = t
  rw [Syntax.bsubst_bv_eq_rename, Syntax.rename_id]

variable {S : Sig.{u}}

private theorem bindAbort_ignored {A : SynCat S} {t : Tm Empty S.Instr 1}
    (ht : HasType S.Instr Ctx.nil (BoundCtx.nil.snoc (empty : S.Ty)) t A.ty) :
    Eqv (Φ := S.Instr) S.pureEff Ctx.nil (BoundCtx.nil.snoc (empty : S.Ty))
      (.let₁ (.abort (.bv 0)) (Tm.lift t)) t A.ty := by
  refine Eqv.ax (.structural ?_)
    (HasType.let₁ (HasType.abort (C := (empty : S.Ty)) HasType.newest) (ht.rename (TypedRenaming.succ _ _))) ht
  have beta := StructuralAxiom.letBeta (pureEff := S.pureEff)
    (a := (.abort (.bv 0) : Tm Empty S.Instr 1)) (b := Tm.lift t) (.abort .bv)
  rwa [instantiate_lift] at beta

theorem fromEmpty_unique_proof (A : SynCat S)
    (f g : of (S := S) (empty : S.Ty) ⟶ A) : f = g := by
  induction f using Syn.ind with
  | H tf hf =>
    induction g using Syn.ind with
    | H tg hg =>
      apply Quotient.sound
      refine (bindAbort_ignored hf).symm.trans ((Eqv.ax (.structural ?_) ?_ ?_).trans
        (bindAbort_ignored hg))
      · exact StructuralAxiom.emptyInitial (.bv 0) (Tm.lift tf) (Tm.lift tg)
      · exact HasType.let₁ (HasType.abort (C := (empty : S.Ty)) HasType.newest) (hf.rename (TypedRenaming.succ _ _))
      · exact HasType.let₁ (HasType.abort (C := (empty : S.Ty)) HasType.newest) (hg.rename (TypedRenaming.succ _ _))

end Syn.SynCat

end Silmaril.Thesis.LambdaIter

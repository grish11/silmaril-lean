module

public import Silmaril.SSA.Isotope.Institution.Parallel.Defs
public import Silmaril.Proofs.SSA.Isotope.Institution.Parallel.Relabel

@[expose] public section

namespace Silmaril.Isotope.Parallel.InstitutionProofs

open Silmaril.Isotope.Institution Parallel.Institution CategoryTheory Semantics

universe u v q

section Transport

variable {τ : Type u} {D : τ → Type q} {m m' : Type q → Type q}
  {A A' B B' : τ}

private theorem cast_eval_reduct (h₁ : A' = A) (h₂ : B' = B) {A'' B'' : τ}
    (h₃ : A'' = A') (h₄ : B'' = B') (f : D A'' → m (D B'')) (x : D A) :
    (h₂ ▸ (h₄ ▸ f (h₃.symm ▸ (h₁.symm ▸ x)) : m (D B')) : m (D B)) =
      ((h₄.trans h₂) ▸ f ((h₃.trans h₁).symm ▸ x) : m (D B)) := by
  cases h₁
  cases h₂
  cases h₃
  cases h₄
  rfl

private theorem cast_bind [Monad m] (h₁ : A' = A) (h₂ : B' = B)
    (x : m (D A)) (k : D A' → m (D B')) :
    (h₂ ▸ ((h₁.symm ▸ x : m (D A')) >>= k) : m (D B)) =
      x >>= fun a => (h₂ ▸ k (h₁.symm ▸ a) : m (D B)) := by
  cases h₁
  cases h₂
  rfl

end Transport

variable {τ ε : Type u} {S S' S'' : InstrSig τ ε} {D : τ → Type q}

theorem primitive_reduct_comp {m : Type q → Type q} (f : S ⟶ S') (g : S' ⟶ S'')
    (I : InstructionModel D S''.Instr m) :
    Primitive.reduct f (Primitive.reduct g I) = Primitive.reduct (f ≫ g) I := by
  unfold Primitive.reduct
  apply congrArg (fun ev => (⟨ev⟩ : InstructionModel D S.Instr m))
  funext op x
  exact cast_eval_reduct (f.source op) (f.target op) (g.source (f.instr op))
    (g.target (f.instr op)) _ x

theorem model_reduct_comp (f : S ⟶ S') (g : S' ⟶ S'') (X : Model D S'') :
    (X.reduct g).reduct f = X.reduct (f ≫ g) := by
  unfold Model.reduct
  exact congrArg (fun I => @Model.mk _ _ D S X.M X.monad X.lawful X.par I)
    (primitive_reduct_comp f g X.instr)

private theorem hom_heq {X X' Y Y' : Model D S} (hx : X = X') (hy : Y = Y')
    {f : Model.Hom X Y} {g : Model.Hom X' Y'} (h : HEq (@f.app) (@g.app)) : HEq f g := by
  subst X' Y'
  exact heq_of_eq (Model.Hom.ext (eq_of_heq h))

theorem reductFunctor_id (S : InstrSig τ ε) :
    (Model.reductFunctor (D := D) (𝟙 S)) = 𝟭 (Model D S) :=
  CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => HEq.rfl)

theorem reductFunctor_comp (f : S ⟶ S') (g : S' ⟶ S'') :
    Model.reductFunctor (D := D) (f ≫ g) = Model.reductFunctor g ⋙ Model.reductFunctor f := by
  refine CategoryTheory.Functor.hext (fun X => (model_reduct_comp f g X).symm) ?_
  intro X Y h
  exact hom_heq (model_reduct_comp f g X).symm (model_reduct_comp f g Y).symm HEq.rfl

section Evaluation

variable {tier : Tier} {ν : Type v} [HasProduct τ] [HasUnit τ] [CaseTypes tier τ]
  [DecidableEq ν] [ProductModel D] [UnitModel D]
  {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {t : Parallel.Tm tier ν S.Instr n} {A : τ}
  {m : Type q → Type q} [Monad m] (I : InstructionModel D S'.Instr m) (P : ParOp m)
  (C : Control tier D m)

private theorem denote_cast {I : InstructionModel D S'.Instr m} {B B' : τ}
    (h : B = B') {l : Parallel.Tm tier ν S'.Instr n} (d : Derivation S'.Instr Γ β l B)
    (γ : FreeEnv D Γ) (ρ : BoundEnv D β) :
    (Derivation.castResult h d).denote D I P C γ ρ =
      (h ▸ d.denote D I P C γ ρ : m (D B')) := by
  cases h
  rfl

theorem denote_mapInstr (f : S ⟶ S') (d : Derivation S.Instr Γ β t A)
    (γ : FreeEnv D Γ) (ρ : BoundEnv D β) :
    (d.mapInstr f).denote D I P C γ ρ =
      d.denote D (Primitive.reduct f I) P C γ ρ := by
  induction d with
  | @op _ _ _ op d ih =>
      simp only [Derivation.mapInstr, Parallel.Tm.mapInstr, denote_cast, Derivation.denote, Primitive.reduct]
      rw [cast_bind (f.source op) (f.target op), ih]
      rfl
  | case _ _ _ ie il ir =>
      simp only [Derivation.mapInstr, Parallel.Tm.mapInstr, Derivation.denote, ie, il, ir]
  | fv | bv | unit => rfl
  | let₁ _ _ ia ib | pair _ _ ia ib | let₂ _ _ ia ib | iter _ _ ia ib | par _ _ ia ib =>
      simp only [Derivation.mapInstr, Parallel.Tm.mapInstr, Derivation.denote, ia, ib]
  | inl _ ia | inr _ ia | abort _ ia =>
      simp only [Derivation.mapInstr, Parallel.Tm.mapInstr, Derivation.denote, ia]

/-- Strict model morphisms commute with every lower-tier exact computation. -/
theorem denote_hom {X Y : Model D S} (H : Model.Hom X Y) (h : tier ≠ .iter)
    (K : Control tier D Id) (d : Derivation S.Instr Γ β t A)
    (γ : FreeEnv D Γ) (ρ : BoundEnv D β) :
    H.app (d.denote D X.instr X.par (lowerControl h K X.M) γ ρ) =
      d.denote D Y.instr Y.par (lowerControl h K Y.M) γ ρ := by
  induction d with
  | fv | bv | unit => exact H.monadHom.map_pure _
  | op _ ih => simp only [Derivation.denote, H.monadHom.map_bind, H.map_instr, ih]
  | let₁ _ _ ia ib | let₂ _ _ ia ib =>
      simp only [Derivation.denote, H.monadHom.map_bind, ia, ib]
  | pair _ _ ia ib =>
      simp only [Derivation.denote, H.monadHom.map_bind, H.monadHom.map_pure, ia, ib]
  | par _ _ ia ib =>
      simp only [Derivation.denote, H.monadHom.map_bind, H.monadHom.map_pure, H.map_par, ia, ib]
  | inl _ ih | inr _ ih =>
      simp only [lowerControl] at ih
      simp only [Derivation.denote, H.monadHom.map_bind, H.monadHom.map_pure, lowerControl, ih]
  | abort _ ih =>
      simp only [lowerControl] at ih
      simp only [Derivation.denote, H.monadHom.map_bind, lowerControl, ih]
      congr 1
      funext z
      exact (K.zero _ z).elim
  | case _ _ _ ie il ir =>
      simp only [lowerControl] at ie il ir
      simp only [Derivation.denote, H.monadHom.map_bind, lowerControl, ie]
      congr 1
      funext e
      split <;> simp only [il, ir]
  | iter => exact (h ‹tier.HasIter›).elim

end Evaluation

end Silmaril.Isotope.Parallel.InstitutionProofs

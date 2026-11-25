module

public import Silmaril.SSA.Thesis.SyntacticCategory.Packing.Defs

public section

universe u

namespace Silmaril.Thesis.LambdaIter.Syn.SynCat

open CategoryTheory
open LocallyNameless LocallyNameless.Tm LocallyNameless.Syntax

variable {S : Sig.{u}}

private theorem packTermPure : {n : Nat} → (β : BoundCtx S.Ty n) →
    Pure S.pureEff (packTerm β)
  | _, .nil => .unit
  | _, .snoc β _ => .pair ((packTermPure β).rename Fin.succ) .bv

private theorem projectPure {m : Nat} {p : Tm Empty S.Instr m} (hp : Pure S.pureEff p) :
    {n : Nat} → (β : BoundCtx S.Ty n) → (i : Fin n) → Pure S.pureEff (project β p i)
  | _, .nil, i => Fin.elim0 i
  | _, .snoc β _, i => Fin.cases (.let₂ hp .bv) (projectPure (.let₂ hp .bv) β) i

private def packingSubst {n : Nat} (β : BoundCtx S.Ty n) :
    PureTypedSubst (Γ := Ctx.nil) (pureEff := S.pureEff)
      β (.snoc .nil (packType β)) (project β (.bv 0)) :=
  ⟨projectTyping β HasType.newest, projectPure .bv β⟩

private def unpackingSubst {n : Nat} (β : BoundCtx S.Ty n) :
    PureTypedSubst (Γ := Ctx.nil) (pureEff := S.pureEff)
      (.snoc .nil (packType β)) β (fun _ => packTerm β) :=
  ⟨fun i => Fin.cases (packTermTyping β) (fun j => j.elim0) i, fun _ => packTermPure β⟩

private theorem upSub_eqv {n m : Nat} {β : BoundCtx S.Ty n} {γ : BoundCtx S.Ty m}
    {σ θ : Fin n → Tm Empty S.Instr m}
    (e : ∀ i, Eqv S.pureEff Ctx.nil γ (σ i) (θ i) (β.get i)) (A : S.Ty) :
    ∀ i, Eqv S.pureEff Ctx.nil (.snoc γ A) (upSub σ i) (upSub θ i) ((β.snoc A).get i) :=
  Fin.cases (.refl HasType.newest) (fun i => (e i).rename (TypedRenaming.succ γ A))

private theorem subst_eqv {n : Nat} {β : BoundCtx S.Ty n} {t : Tm Empty S.Instr n}
    {A : S.Ty} (h : HasType S.Instr Ctx.nil β t A)
    {m : Nat} {γ : BoundCtx S.Ty m} {σ θ : Fin n → Tm Empty S.Instr m}
    (e : ∀ i, Eqv S.pureEff Ctx.nil γ (σ i) (θ i) (β.get i)) :
    Eqv S.pureEff Ctx.nil γ (bsubst σ t) (bsubst θ t) A := by
  induction h generalizing m with
  | fv h => exact .refl (.fv h)
  | bv => exact e _
  | op _ ih => exact .op (ih e)
  | unit => exact .unit
  | let₁ _ _ ih₁ ih₂ => exact .let₁ (ih₁ e) (ih₂ (upSub_eqv e _))
  | pair _ _ ih₁ ih₂ => exact .pair (ih₁ e) (ih₂ e)
  | let₂ _ _ ih₁ ih₂ => exact .let₂ (ih₁ e) (ih₂ (upSub_eqv (upSub_eqv e _) _))
  | inl _ ih => exact .inl (ih e)
  | inr _ ih => exact .inr (ih e)
  | case _ _ _ ih₁ ih₂ ih₃ => exact .case (ih₁ e) (ih₂ (upSub_eqv e _)) (ih₃ (upSub_eqv e _))
  | abort _ ih => exact .abort (ih e)
  | iter _ _ ih₁ ih₂ => exact .iter (ih₁ e) (ih₂ (upSub_eqv e _))

private theorem project_congr {m : Nat} {γ : BoundCtx S.Ty m} {p q : Tm Empty S.Instr m} :
    {n : Nat} → (β : BoundCtx S.Ty n) → Eqv S.pureEff Ctx.nil γ p q (packType β) →
      (i : Fin n) → Eqv S.pureEff Ctx.nil γ (project β p i) (project β q i) (β.get i)
  | _, .nil, _, i => Fin.elim0 i
  | _, .snoc β _, e, i => Fin.cases
      (.let₂ e (.refl HasType.newest))
      (project_congr β (.let₂ e (.refl (.bv (ι := 1))))) i

private theorem project_rename {n m k : Nat} (β : BoundCtx S.Ty n)
    (ρ : Fin m → Fin k) (p : Tm Empty S.Instr m) (i : Fin n) :
    rename ρ (project β p i) = project β (rename ρ p) i := by
  induction β generalizing p with
  | nil => exact Fin.elim0 i
  | snoc β _ ih =>
      refine Fin.cases rfl (fun j => ?_) i
      exact ih (.let₂ p (.bv 1)) j

private theorem project_bsubst {n m k : Nat} (β : BoundCtx S.Ty n)
    (σ : Fin m → Tm Empty S.Instr k) (p : Tm Empty S.Instr m) (i : Fin n) :
    bsubst σ (project β p i) = project β (bsubst σ p) i := by
  induction β generalizing p with
  | nil => exact Fin.elim0 i
  | snoc β _ ih =>
      refine Fin.cases rfl (fun j => ?_) i
      exact ih (.let₂ p (.bv 1)) j

private theorem project_packTerm {n : Nat} (β : BoundCtx S.Ty n) (i : Fin n) :
    Eqv S.pureEff Ctx.nil β (project β (packTerm β) i) (.bv i) (β.get i) := by
  induction β with
  | nil => exact Fin.elim0 i
  | snoc β B ih =>
      refine Fin.cases (second_beta (packTermTyping β).lift HasType.newest
        ((packTermPure β).rename Fin.succ)) (fun j => ?_) i
      have head := first_beta (S := S) (packTermTyping β).lift
        (HasType.newest (A := B)) .bv
      refine (project_congr β head j).trans ?_
      rw [show project β (lift (packTerm β)) j = lift (project β (packTerm β) j) from
        (project_rename β Fin.succ (packTerm β) j).symm]
      exact (ih j).rename (TypedRenaming.succ β B)

theorem unpacked_packed_proof {n : Nat} {β : BoundCtx S.Ty n}
    {t : Tm Empty S.Instr n} {A : S.Ty} (h : HasType S.Instr Ctx.nil β t A) :
    Eqv S.pureEff Ctx.nil β (unpackedTerm β (packedTerm β t)) t A := by
  rw [unpackedTerm, packedTerm, Syntax.bsubst_comp]
  have e := subst_eqv h (γ := β) (θ := Tm.bv)
    (σ := fun i => bsubst (fun _ : Fin 1 => packTerm β) (project β (.bv 0) i)) (fun i => by
      rw [project_bsubst, bsubst_bv]
      exact project_packTerm β i)
  rwa [Syntax.bsubst_bv_eq_rename, Syntax.rename_id] at e

private theorem packTerm_project {n m : Nat} (β : BoundCtx S.Ty n)
    {γ : BoundCtx S.Ty m} {p : Tm Empty S.Instr m}
    (h : HasType S.Instr Ctx.nil γ p (packType β)) (hp : Pure S.pureEff p) :
    Eqv S.pureEff Ctx.nil γ (bsubst (project β p) (packTerm β)) p (packType β) := by
  induction β generalizing p with
  | nil =>
      have hlet := HasType.let₁ h (HasType.unit (Φ := S.Instr))
      exact (Eqv.ax (.structural (.letBeta hp)) hlet .unit).symm.trans
        (Eqv.ax (.structural (.unitEta p)) hlet h)
  | snoc β B ih =>
      simp only [packTerm, bsubst_pair, bsubst_bv, lift, bsubst_rename]
      exact (Eqv.pair (ih (.let₂ h HasType.previous) (.let₂ hp .bv))
        (.refl (.let₂ h HasType.newest))).trans (pair_projections_eta h hp)

theorem packed_unpacked_proof {n : Nat} (β : BoundCtx S.Ty n)
    {t : Tm Empty S.Instr 1} {A : S.Ty}
    (h : HasType S.Instr Ctx.nil (.snoc .nil (packType β)) t A) :
    Eqv S.pureEff Ctx.nil (.snoc .nil (packType β))
      (packedTerm β (unpackedTerm β t)) t A := by
  rw [packedTerm, unpackedTerm, Syntax.bsubst_comp]
  have e := subst_eqv h (γ := .snoc .nil (packType β)) (θ := Tm.bv)
    (σ := fun _ => bsubst (project β (.bv 0)) (packTerm β))
    (Fin.cases (packTerm_project β HasType.newest .bv) (fun i => i.elim0))
  rwa [Syntax.bsubst_bv_eq_rename, Syntax.rename_id] at e

def packedHomEquiv_proof {n : Nat} (β : BoundCtx S.Ty n) (A : S.Ty) :
    El S β A ≃ (of (packType β) ⟶ of A) where
  toFun := Quotient.map
    (fun a => ⟨packedTerm β a.1, a.2.map packedTyping⟩)
    (fun _ _ e => Eqv.bsubst (packingSubst β) e)
  invFun := Quotient.map
    (fun a => ⟨unpackedTerm β a.1, a.2.map (HasType.bsubst (unpackingSubst β).typed)⟩)
    (fun _ _ e => Eqv.bsubst (unpackingSubst β) e)
  left_inv q := by
    induction q using Syn.ind with
    | H t h => exact Quotient.sound (unpacked_packed_proof h)
  right_inv q := by
    induction q using Syn.ind with
    | H t h => exact Quotient.sound (packed_unpacked_proof β h)

theorem packedHomEquiv_mk_proof {n : Nat} {β : BoundCtx S.Ty n}
    {t : Tm Empty S.Instr n} {A : S.Ty} (h : HasType S.Instr Ctx.nil β t A) :
    packedHomEquiv_proof β A (mk h) = packedArrow h := by rfl

private theorem instantiate_underBinder_one {t a : Tm Empty S.Instr 1} :
    instantiate (underBinder t) a = bsubst (fun _ : Fin 1 => a) t := by
  rw [instantiate, underBinder, bsubst_rename]
  apply bsubst_congr
  exact Fin.cases rfl (fun i => i.elim0)

theorem packedSubst_comp_proof {n m : Nat} {β : BoundCtx S.Ty n} {γ : BoundCtx S.Ty m}
    {σ : Fin n → Tm Empty S.Instr m}
    (s : PureTypedSubst (Γ := Ctx.nil) (pureEff := S.pureEff) β γ σ)
    {t : Tm Empty S.Instr n} {A : S.Ty} (h : HasType S.Instr Ctx.nil β t A) :
    packedSubst s ≫ packedArrow h = packedArrow (h.bsubst s.typed) := by
  let p := packedTerm γ (bsubst σ (packTerm β))
  let hp := packedTyping ((packTermTyping β).bsubst s.typed)
  have pp : Pure S.pureEff p := ((packTermPure β).bsubst s.pure).bsubst (packingSubst γ).pure
  have ht := (packedTyping h).underBinder (X := packType γ)
  apply Quotient.sound
  refine (Eqv.ax (.structural (.letBeta pp)) (.let₁ hp ht) (ht.instantiate hp)).trans ?_
  rw [instantiate_underBinder_one]
  change Eqv S.pureEff Ctx.nil (.snoc .nil (packType γ))
    (bsubst (fun _ : Fin 1 => p) (bsubst (project β (.bv 0)) t))
    (bsubst (project γ (.bv 0)) (bsubst σ t)) A
  rw [bsubst_comp, bsubst_comp]
  apply subst_eqv h
  intro i
  rw [project_bsubst, bsubst_bv]
  have e := ((project_packTerm β i).bsubst s).bsubst (packingSubst γ)
  rw [project_bsubst, project_bsubst, bsubst_bv] at e
  exact e

theorem packedSubst_isPureMor_proof {n m : Nat} {β : BoundCtx S.Ty n} {γ : BoundCtx S.Ty m}
    {σ : Fin n → Tm Empty S.Instr m}
    (s : PureTypedSubst (Γ := Ctx.nil) (pureEff := S.pureEff) β γ σ) :
    IsPureMor (packedSubst s) :=
  ⟨_, packedTyping ((packTermTyping β).bsubst s.typed),
    ((packTermPure β).bsubst s.pure).bsubst (packingSubst γ).pure, rfl⟩

end Silmaril.Thesis.LambdaIter.Syn.SynCat

module

public import Silmaril.SSA.Thesis.SyntacticCategory.Tensor.Iteration.Thms
public import Silmaril.SSA.Thesis.SyntacticCategory.Packing.Thms
import Silmaril.Proofs.SSA.Thesis.SyntacticCategory.Tensor.Associator
import Silmaril.Proofs.SSA.Thesis.SyntacticCategory.Tensor.Laws
import Silmaril.Proofs.SSA.Thesis.SyntacticCategory.Tensor.Distributivity

public section

universe u

namespace Silmaril.Thesis.LambdaIter.Syn.SynCat

open CategoryTheory CategoryTheory.Limits
open LocallyNameless LocallyNameless.Tm LocallyNameless.Syntax
open scoped MonoidalCategory

variable {S : Sig.{u}}

private theorem bsubst_closed_body {n m : Nat} (σ : Fin (n + 1) → Tm Empty S.Instr (m + 1))
    (h : σ 0 = .bv 0) (t : Tm Empty S.Instr 1) :
    bsubst σ (onNewest t) = onNewest t := by
  rw [onNewest, bsubst_rename]
  exact (bsubst_congr (fun _ => h) _).trans (bsubst_bv_eq_rename (fun _ => 0) t)

private def threadedBody {n : Nat} (f : Tm Empty S.Instr 1) : Tm Empty S.Instr (n + 2) :=
  .case (onNewest f) (.inl (.pair (.bv 2) (.bv 0))) (.inr (.pair (.bv 2) (.bv 0)))

private def threadedStep (f : Tm Empty S.Instr 1) : Tm Empty S.Instr 1 :=
  .let₂ (.bv 0) (threadedBody f)

private def threadedBodyTyping {n : Nat} {β : BoundCtx S.Ty n} {R A X Y : S.Ty}
    {f : Tm Empty S.Instr 1} (hf : HasType S.Instr Ctx.nil (.snoc .nil A) f (coprod Y X)) :
    HasType S.Instr Ctx.nil ((β.snoc R).snoc A) (threadedBody f)
      (coprod (tensor R Y) (tensor R X)) :=
  .case (onNewestTyping hf)
    (.inl (.pair (.bv (ι := 2)) HasType.newest))
    (.inr (.pair (.bv (ι := 2)) HasType.newest))

private def threadedStepTyping {R A X Y : S.Ty} {f : Tm Empty S.Instr 1}
    (hf : HasType S.Instr Ctx.nil (.snoc .nil A) f (coprod Y X)) :
    HasType S.Instr Ctx.nil (.snoc .nil (tensor R A)) (threadedStep f)
      (coprod (tensor R Y) (tensor R X)) :=
  .let₂ HasType.newest (threadedBodyTyping hf)

private theorem apply_threaded_step {n : Nat} {β : BoundCtx S.Ty n} {R A X Y : S.Ty}
    {f : Tm Empty S.Instr 1} (hf : HasType S.Instr Ctx.nil (.snoc .nil A) f (coprod Y X))
    {i : Fin n} {a : Tm Empty S.Instr n} (hu : HasType S.Instr (Ctx.nil : Ctx Empty S.Ty) β (.bv i) R)
    (ha : HasType S.Instr (Ctx.nil : Ctx Empty S.Ty) β a A) (pa : Pure S.pureEff a) :
    Eqv S.pureEff (Ctx.nil : Ctx Empty S.Ty) β (bsubst (fun _ : Fin 1 => .pair (.bv i) a) (threadedStep f))
      (.case (bsubst (fun _ : Fin 1 => a) f)
        (.inl (.pair (.bv i.succ) (.bv 0))) (.inr (.pair (.bv i.succ) (.bv 0))))
      (coprod (tensor R Y) (tensor R X)) := by
  let body := threadedBodyTyping (β := β) (R := R) hf
  let body' := body.instantiate ha.lift
  have expand : bsubst (fun _ : Fin 1 => .pair (.bv i) a) (threadedStep f) =
      .let₂ (.pair (.bv i) a) (threadedBody f) := by
    simp only [threadedStep, threadedBody, bsubst_let₂, bsubst_case, bsubst_bv, bsubst_pair,
      bsubst_inl, bsubst_inr]
    rw [bsubst_closed_body (upSub (upSub (fun _ : Fin 1 => .pair (.bv i) a))) rfl]
    rfl
  rw [expand]
  refine (Eqv.ax (.structural (.pairBeta _ _ _)) (.let₂ (.pair hu ha) body)
    (.let₁ hu (.let₁ ha.lift body))).trans ?_
  refine (Eqv.let₁ (.refl hu)
    (.ax (.structural (.letBeta (pa.rename _))) (.let₁ ha.lift body) body')).trans ?_
  have e := Eqv.ax (.structural (.letBeta (pureEff := S.pureEff) .bv))
    (.let₁ hu body') (body'.instantiate hu)
  have opened : instantiate (instantiate (threadedBody f) (lift a)) (.bv i) =
      .case (bsubst (fun _ : Fin 1 => a) f)
        (.inl (.pair (.bv i.succ) (.bv 0))) (.inr (.pair (.bv i.succ) (.bv 0))) := by
    simp only [threadedBody, instantiate, bsubst_case, bsubst_bv, bsubst_pair, bsubst_inl,
      bsubst_inr, bsubst_comp, onNewest, bsubst_rename, lift, Fin.cases_zero, Fin.cases_succ]
    have id : bsubst (fun j => .bv j) a = a := by rw [bsubst_bv_eq_rename, rename_id]
    rw [id]
    rfl
  rwa [opened] at e

-- The first branch has already been paired with the parameter by naturality.
-- The continuation branch pairs with the same parameter via uniformity.
private theorem thread_square_left {n : Nat} {β : BoundCtx S.Ty n} {R X Y : S.Ty}
    {f : Tm Empty S.Instr 1} (hf : HasType S.Instr Ctx.nil (.snoc .nil X) f (coprod Y X)) :
    let γ := ((β.snoc R).snoc X).snoc X
    Eqv S.pureEff (Ctx.nil : Ctx Empty S.Ty) γ
      (.case (.case (onNewest f) (.inl (.pair (.bv 3) (.bv 0))) (.inr (.bv 0)))
        (.inl (.bv 0)) (.inr (.pair (.bv 3) (.bv 0))))
      (.case (onNewest f) (.inl (.pair (.bv 3) (.bv 0))) (.inr (.pair (.bv 3) (.bv 0))))
      (coprod (tensor R Y) (tensor R X)) := by
  let U := tensor R Y
  let W := tensor R X
  let γ := ((β.snoc R).snoc X).snoc X
  let scrut := onNewestTyping (β := (β.snoc R).snoc X) hf
  let left := HasType.pair (HasType.bv (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty))
    (β := γ.snoc Y) (ι := 3)) HasType.newest
  let right := HasType.newest (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty)) (β := γ) (A := X)
  let a := HasType.inl (B := X) left
  let b := HasType.inr (A := U) right
  let kL := HasType.inl (B := W) (HasType.newest (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty))
    (β := γ) (A := U))
  let kR := HasType.inr (A := U) (HasType.pair
    (HasType.bv (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty)) (β := γ.snoc X) (ι := 3))
    HasType.newest)
  let k := HasType.case HasType.newest kL.underBinder kR.underBinder
  have seq₁ := Eqv.ax (pureEff := S.pureEff) (.sequencing (.bindCase _ _ _))
    (.case (.case scrut a b) kL kR) (.let₁ (.case scrut a b) k)
  have seq₂ := Eqv.ax (pureEff := S.pureEff) (.sequencing (.bindLetCase _ _ _ _))
    (.let₁ (.case scrut a b) k) (.case scrut (.let₁ a k.underBinder) (.let₁ b k.underBinder))
  have leftStep : Eqv (Φ := S.Instr) S.pureEff (Ctx.nil : Ctx Empty S.Ty) (γ.snoc Y)
      (.let₁ (.inl (.pair (.bv 3) (.bv 0))) (underBinder (n := n + 3) (.case (.bv 0)
        (underBinder (.inl (.bv 0))) (underBinder (.inr (.pair (.bv 3) (.bv 0)))))))
      (.inl (.pair (.bv 3) (.bv 0))) (coprod U W) := by
    let l := HasType.inl (B := W) (HasType.newest (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty))
      (β := γ.snoc Y) (A := U))
    let r := HasType.inr (A := U) (HasType.pair
      (HasType.bv (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty)) (β := (γ.snoc Y).snoc X) (ι := 4))
      HasType.newest)
    have beta := Eqv.ax (.structural (.letBeta (pureEff := S.pureEff) (.inl (.pair .bv .bv))))
      (.let₁ a k.underBinder) (k.underBinder.instantiate a)
    change Eqv S.pureEff (Ctx.nil : Ctx Empty S.Ty) _
      (.let₁ (.inl (.pair (.bv 3) (.bv 0))) _) (.case (.inl (.pair (.bv 3) (.bv 0))) _ _) _ at beta
    exact beta.trans ((Eqv.ax (.structural (.caseBetaL _ _ _)) (.case a l r) (.let₁ left l)).trans
      (Eqv.ax (.structural (.letBeta (.pair .bv .bv))) (.let₁ left l) (l.instantiate left)))
  have rightStep : Eqv (Φ := S.Instr) S.pureEff (Ctx.nil : Ctx Empty S.Ty) (γ.snoc X)
      (.let₁ (.inr (.bv 0)) (underBinder (n := n + 3) (.case (.bv 0)
        (underBinder (.inl (.bv 0))) (underBinder (.inr (.pair (.bv 3) (.bv 0)))))))
      (.inr (.pair (.bv 3) (.bv 0))) (coprod U W) := by
    let l := HasType.inl (B := W) (HasType.newest (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty))
      (β := γ.snoc X) (A := U))
    let r := HasType.inr (A := U) (HasType.pair
      (HasType.bv (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty)) (β := (γ.snoc X).snoc X) (ι := 4))
      HasType.newest)
    have beta := Eqv.ax (.structural (.letBeta (pureEff := S.pureEff) (.inr .bv)))
      (.let₁ b k.underBinder) (k.underBinder.instantiate b)
    change Eqv S.pureEff (Ctx.nil : Ctx Empty S.Ty) _ (.let₁ (.inr (.bv 0)) _) (.case (.inr (.bv 0)) _ _) _ at beta
    exact beta.trans ((Eqv.ax (.structural (.caseBetaR _ _ _)) (.case b l r) (.let₁ right r)).trans
      (Eqv.ax (.structural (.letBeta .bv)) (.let₁ right r) (r.instantiate right)))
  exact seq₁.trans (seq₂.trans (.case (.refl scrut) leftStep rightStep))

private theorem context_iter_strength {n : Nat} {β : BoundCtx S.Ty n} {R X Y : S.Ty}
    {f : Tm Empty S.Instr 1} (hf : HasType S.Instr Ctx.nil (.snoc .nil X) f (coprod Y X)) :
    let γ := (β.snoc R).snoc X
    Eqv S.pureEff (Ctx.nil : Ctx Empty S.Ty) γ
      (.iter (.pair (.bv 1) (.bv 0)) (onNewest (threadedStep f)))
      (.let₁ (.iter (.bv 0) (onNewest f)) (.pair (.bv 2) (.bv 0))) (tensor R Y) := by
  let U := tensor R Y
  let W := tensor R X
  let γ := (β.snoc R).snoc X
  let x := HasType.newest (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty))
    (β := β.snoc R) (A := X)
  let p := HasType.pair (HasType.previous (B := X)
    (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty)) (β := β) (A := R)) x
  let f' := onNewestTyping (β := γ) hf
  let g := threadedStepTyping (R := R) hf
  let g' := onNewestTyping (β := γ) g
  let exit := HasType.pair (HasType.bv (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty))
    (β := γ.snoc Y) (ι := 2)) HasType.newest
  let step := HasType.case f' (HasType.inl (B := X) exit.underBinder)
    (HasType.inr (A := U) HasType.newest)
  let carry := HasType.pair (HasType.bv (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty))
    (β := γ.snoc X) (ι := 2)) HasType.newest
  have natural := Eqv.ax (pureEff := S.pureEff) (.iteration (.naturality _ _ _))
    (.let₁ (.iter x f') exit) (.iter x step)
  have applyStep := apply_threaded_step hf
    (HasType.bv (β := γ.snoc X) (ι := 2)) (HasType.newest (β := γ) (A := X)) .bv
  rw [bsubst_bv_eq_rename (fun _ => 0) f] at applyStep
  have sq := (thread_square_left (β := β) (R := R) hf).trans applyStep.symm
  have openStep : instantiate (underBinder (onNewest (n := n + 2) (threadedStep f)))
      (.pair (.bv 2) (.bv 0)) =
      bsubst (fun _ : Fin 1 => .pair (.bv (2 : Fin (n + 3))) (.bv 0)) (threadedStep f) := by
    rw [underBinder_onNewest, subst_onNewest]
  rw [← openStep] at sq
  have uniform := Eqv.uniformity x carry (.pair .bv .bv) step g' sq
  have beta : Eqv (Φ := S.Instr) S.pureEff (Ctx.nil : Ctx Empty S.Ty) γ (.let₁ (.bv 0) (.pair (.bv 2) (.bv 0)))
      (.pair (.bv 1) (.bv 0)) W :=
    Eqv.ax (.structural (.letBeta .bv)) (.let₁ x carry) p
  exact (natural.trans (uniform.trans (.iter beta (.refl g')))).symm

private def rawDistributorTyping (R X Y : SynCat S) :
    HasType S.Instr Ctx.nil (.snoc .nil (productObj R (cop Y X)).ty) (threadedStep (.bv 0))
      (cop (productObj R Y) (productObj R X)).ty :=
  threadedStepTyping HasType.newest

private theorem tensor_then_distribute {R A X Y : SynCat S} {f : Tm Empty S.Instr 1}
    (hf : HasType S.Instr Ctx.nil (.snoc .nil A.ty) f (cop Y X).ty) :
    tensorLeft R (mk hf : A ⟶ cop Y X) ≫ mk (rawDistributorTyping R X Y) =
      (mk (threadedStepTyping hf) : productObj R A ⟶ cop (productObj R Y) (productObj R X)) := by
  apply Quotient.sound
  let γ := BoundCtx.nil.snoc (productObj R A).ty
  let δ := (γ.snoc R.ty).snoc A.ty
  let p := HasType.newest (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty)) (β := .nil)
    (A := (productObj R A).ty)
  let ht := tensorLeftBodyTyping (β := γ) (R := R.ty) hf
  let hd := rawDistributorTyping R X Y
  let d := onNewestTyping (β := δ) hd
  let f' := onNewestTyping (β := γ.snoc R.ty) hf
  let r := HasType.bv (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty))
    (β := δ.snoc (cop Y X).ty) (ι := 2)
  let x := HasType.newest (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty))
    (β := δ) (A := (cop Y X).ty)
  let q := HasType.pair r x
  have outer := after_destructuring p ht hd
  have e := Eqv.ax (pureEff := S.pureEff) (.sequencing (.bindLet _ _ _))
    (.let₁ ht d) (.let₁ f' (.let₁ q d.underBinder))
  rw [underBinder_onNewest] at e
  let k := onNewestTyping (β := δ.snoc (cop Y X).ty) hd
  have beta := Eqv.ax (.structural (.letBeta (pureEff := S.pureEff) (.pair .bv .bv)))
    (.let₁ q k) (k.instantiate q)
  rw [subst_onNewest] at beta
  have opened := apply_threaded_step (R := R.ty) (X := X.ty) (Y := Y.ty)
    (HasType.newest (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty)) (β := .nil)
      (A := (cop Y X).ty)) r x .bv
  let lh := HasType.inl (B := (productObj R X).ty) (HasType.pair
    (HasType.bv (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty)) (β := δ.snoc Y.ty) (ι := 2))
    HasType.newest)
  let rh := HasType.inr (A := (productObj R Y).ty) (HasType.pair
    (HasType.bv (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty)) (β := δ.snoc X.ty) (ι := 2))
    HasType.newest)
  have fuse := Eqv.ax (pureEff := S.pureEff) (.sequencing (.bindCase _ _ _))
    (.case f' lh rh) (.let₁ f' (.case x lh.underBinder rh.underBinder))
  have inner := e.trans ((Eqv.let₁ (.refl f') (beta.trans opened)).trans fuse.symm)
  change Eqv S.pureEff Ctx.nil γ (.let₁ (.let₂ (.bv 0) (tensorLeftBody f))
    (underBinder (threadedStep (.bv 0)))) (threadedStep f) _
  rw [underBinder_eq_onNewest]
  exact outer.trans (.let₂ (.refl p) inner)

private theorem threaded_inl (R X Y : SynCat S) :
    tensorLeft R (injl Y X) ≫ mk (rawDistributorTyping R X Y) =
      injl (productObj R Y) (productObj R X) := by
  refine (tensor_then_distribute (R := R) (A := Y) (X := X) (Y := Y)
    (HasType.inl (B := X.ty) HasType.newest)).trans ?_
  apply Quotient.sound
  let P := productObj R Y
  let Q := productObj R X
  let γ := BoundCtx.nil.snoc P.ty
  let δ := (γ.snoc R.ty).snoc Y.ty
  let x := HasType.newest (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty)) (β := γ.snoc R.ty) (A := Y.ty)
  let l := HasType.inl (B := Q.ty) (HasType.pair
    (HasType.bv (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty)) (β := δ.snoc Y.ty) (ι := 2))
    HasType.newest)
  let r := HasType.inr (A := P.ty) (HasType.pair
    (HasType.bv (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty)) (β := δ.snoc X.ty) (ι := 2))
    HasType.newest)
  let h := HasType.inl (B := Q.ty) (HasType.newest (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty))
    (β := .nil) (A := P.ty))
  have beta := Eqv.ax (pureEff := S.pureEff) (.structural (.caseBetaL _ _ _))
    (.case (.inl (B := X.ty) x) l r) (.let₁ x l)
  have reduce := Eqv.ax (.structural (.letBeta (pureEff := S.pureEff) .bv))
    (.let₁ x l) (l.instantiate x)
  exact (Eqv.let₂ (.refl (HasType.newest (A := P.ty))) (beta.trans reduce)).trans
    (rebuildProduct (R := R) (A := Y) (D := cop P Q) h).symm

private theorem threaded_inr (R X Y : SynCat S) :
    tensorLeft R (injr Y X) ≫ mk (rawDistributorTyping R X Y) =
      injr (productObj R Y) (productObj R X) := by
  refine (tensor_then_distribute (R := R) (A := X) (X := X) (Y := Y)
    (HasType.inr (A := Y.ty) HasType.newest)).trans ?_
  apply Quotient.sound
  let P := productObj R Y
  let Q := productObj R X
  let γ := BoundCtx.nil.snoc Q.ty
  let δ := (γ.snoc R.ty).snoc X.ty
  let x := HasType.newest (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty)) (β := γ.snoc R.ty) (A := X.ty)
  let l := HasType.inl (B := Q.ty) (HasType.pair
    (HasType.bv (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty)) (β := δ.snoc Y.ty) (ι := 2))
    HasType.newest)
  let r := HasType.inr (A := P.ty) (HasType.pair
    (HasType.bv (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty)) (β := δ.snoc X.ty) (ι := 2))
    HasType.newest)
  let h := HasType.inr (A := P.ty) (HasType.newest (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty))
    (β := .nil) (A := Q.ty))
  have beta := Eqv.ax (pureEff := S.pureEff) (.structural (.caseBetaR _ _ _))
    (.case (.inr (A := Y.ty) x) l r) (.let₁ x r)
  have reduce := Eqv.ax (.structural (.letBeta (pureEff := S.pureEff) .bv))
    (.let₁ x r) (r.instantiate x)
  exact (Eqv.let₂ (.refl (HasType.newest (A := Q.ty))) (beta.trans reduce)).trans
    (rebuildProduct (R := R) (A := X) (D := cop P Q) h).symm

-- Identify the syntax distributor by its effect on the two coproduct injections.
private theorem chosenDistributor_eq (R X Y : SynCat S) :
    tensorLeft R (copIso Y X).hom ≫ DistributivePremonoidalCategory.leftInv R Y X ≫
      (copIso (productObj R Y) (productObj R X)).inv = mk (rawDistributorTyping R X Y) := by
  let d := DistributiveTensor.leftIso R Y X
  have dl : tensorLeft R (coprod.inl : Y ⟶ Y ⨿ X) ≫ d.inv =
      (coprod.inl : productObj R Y ⟶ productObj R Y ⨿ productObj R X) := by
    change (R ◁ (coprod.inl : Y ⟶ Y ⨿ X)) ≫ d.inv = _
    rw [← DistributiveTensor.inl_leftHom R Y X, Category.assoc]
    change _ ≫ d.hom ≫ d.inv = _
    rw [d.hom_inv_id, Category.comp_id]
    rfl
  have dr : tensorLeft R (coprod.inr : X ⟶ Y ⨿ X) ≫ d.inv =
      (coprod.inr : productObj R X ⟶ productObj R Y ⨿ productObj R X) := by
    change (R ◁ (coprod.inr : X ⟶ Y ⨿ X)) ≫ d.inv = _
    rw [← DistributiveTensor.inr_leftHom R Y X, Category.assoc]
    change _ ≫ d.hom ≫ d.inv = _
    rw [d.hom_inv_id, Category.comp_id]
    rfl
  apply tensorLeft_coprod_hom_ext R Y X
  · rw [← Category.assoc, ← tensorLeft_comp, injl_copIso_hom, ← Category.assoc]
    change (_ ≫ d.inv) ≫ _ = _
    rw [dl, coprod_inl_copIso_inv, threaded_inl]
  · rw [← Category.assoc, ← tensorLeft_comp, injr_copIso_hom, ← Category.assoc]
    change (_ ≫ d.inv) ≫ _ = _
    rw [dr, coprod_inr_copIso_inv, threaded_inr]

private theorem apply_closed_iter {n : Nat} (a : Tm Empty S.Instr n) (f : Tm Empty S.Instr 1) :
    bsubst (fun _ : Fin 1 => a) (.iter (.bv 0) (underBinder f)) =
      .iter a (onNewest f) := by
  rw [bsubst_iter, bsubst_bv, underBinder_eq_onNewest]
  rw [bsubst_closed_body (upSub (fun _ : Fin 1 => a)) rfl]

private theorem iterate_threadedStep {R X Y : SynCat S} {f : Tm Empty S.Instr 1}
    (hf : HasType S.Instr Ctx.nil (.snoc .nil X.ty) f (cop Y X).ty) :
    iterate (A := productObj R X) (B := productObj R Y) (mk (threadedStepTyping hf)) =
      tensorLeft R (iterate (A := X) (B := Y) (mk hf)) := by
  apply eq_of_product_test R X
  intro γ r x
  let g := threadedStepTyping (R := R.ty) hf
  let gl := HasType.iter (A := (productObj R X).ty) (B := (productObj R Y).ty)
    HasType.newest g.underBinder
  let fl := HasType.iter (A := X.ty) (B := Y.ty) HasType.newest hf.underBinder
  let fr := tensorLeftTyping (R := R.ty) fl
  change packedArrow (.pair r x) ≫ (mk gl : productObj R X ⟶ productObj R Y) =
    packedArrow (.pair r x) ≫ (mk fr : productObj R X ⟶ productObj R Y)
  rw [packedArrow_apply (.pair r x) (.pair .bv .bv) gl,
    packedArrow_apply (.pair r x) (.pair .bv .bv) fr]
  apply (packedArrow_eq_iff _ _).mpr
  change Eqv S.pureEff Ctx.nil _
    (bsubst (fun _ : Fin 1 => .pair (.bv 1) (.bv 0)) (.iter (.bv 0) (underBinder (threadedStep f))))
    (bsubst (fun _ : Fin 1 => .pair (.bv 1) (.bv 0)) (tensorLeftTm (.iter (.bv 0) (underBinder f)))) _
  rw [apply_closed_iter, bsubst_tensorLeftTm]
  have right := left_on_pair fl r x .bv .bv
  rw [apply_closed_iter] at right
  exact (context_iter_strength (β := γ) (R := R.ty) hf).trans right.symm

private theorem raw_iterate_strength (R : SynCat S) {X Y : SynCat S} (f : X ⟶ cop Y X) :
    iterate (tensorLeft R f ≫ mk (rawDistributorTyping R X Y)) = tensorLeft R (iterate f) := by
  induction f using Syn.ind with
  | H f hf =>
    rw [tensor_then_distribute hf]
    exact iterate_threadedStep hf

theorem iterate'_strength_proof (R : SynCat S) {X Y : SynCat S} (f : X ⟶ Y ⨿ X) :
    iterate' ((R ◁ f) ≫ DistributivePremonoidalCategory.leftInv R Y X) =
      R ◁ iterate' f := by
  let g := f ≫ (copIso Y X).inv
  let d := DistributivePremonoidalCategory.leftInv R Y X
  let i := (copIso (productObj R Y) (productObj R X)).inv
  have gf : g ≫ (copIso Y X).hom = f := by
    dsimp only [g]
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have comparison : (tensorLeft R f ≫ d) ≫ i = tensorLeft R g ≫ mk (rawDistributorTyping R X Y) :=
    calc
      (tensorLeft R f ≫ d) ≫ i = (tensorLeft R (g ≫ (copIso Y X).hom) ≫ d) ≫ i := by rw [gf]
      _ = tensorLeft R g ≫ (tensorLeft R (copIso Y X).hom ≫ d ≫ i) := by
        rw [tensorLeft_comp]
        simp only [Category.assoc]
      _ = _ := by rw [chosenDistributor_eq]
  change iterate ((tensorLeft R f ≫ d) ≫ i) = tensorLeft R (iterate g)
  rw [comparison, raw_iterate_strength]

end Silmaril.Thesis.LambdaIter.Syn.SynCat

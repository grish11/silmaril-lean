module

public import Silmaril.SSA.Thesis.SyntacticCategory.Tensor.Centrality.Thms
public import Silmaril.SSA.Thesis.SyntacticCategory.Packing.Thms
import Silmaril.Proofs.SSA.Thesis.SyntacticCategory.Tensor.Associator

public section

universe u

namespace Silmaril.Thesis.LambdaIter.Syn.SynCat

open CategoryTheory CategoryTheory.Limits
open LocallyNameless LocallyNameless.Tm LocallyNameless.Syntax
open scoped MonoidalCategory

variable {S : Sig.{u}}

private theorem specialize_underCase {n : Nat} (t : Tm Empty S.Instr (n + 1))
    (p : Tm Empty S.Instr (n + 2)) :
    instantiate (underBinder (underBinder t)) p =
      bsubst (Fin.cases p (fun i => .bv i.succ.succ)) t := by
  rw [instantiate, underBinder, underBinder, bsubst_rename, bsubst_rename]
  exact bsubst_congr (Fin.cases rfl (fun i => rfl)) _

/-- An arbitrary computation in a context ending in a sum is determined by
its two pure specializations. -/
theorem splitSum_proof {n : Nat} {β : BoundCtx S.Ty n} {A B D : S.Ty}
    {t : Tm Empty S.Instr (n + 1)}
    (h : HasType S.Instr Ctx.nil (.snoc β (coprod A B)) t D) :
    Eqv S.pureEff Ctx.nil (.snoc β (coprod A B)) t
      (.case (.bv 0)
        (bsubst (Fin.cases (.inl (.bv 0)) (fun i => .bv i.succ.succ)) t)
        (bsubst (Fin.cases (.inr (.bv 0)) (fun i => .bv i.succ.succ)) t)) D := by
  let γ := β.snoc (coprod A B)
  let x : HasType S.Instr (Ctx.nil : Ctx Empty S.Ty) γ (.bv 0) (coprod A B) :=
    HasType.newest
  let l := HasType.inl (B := B) (HasType.newest (Φ := S.Instr)
    (Γ := (Ctx.nil : Ctx Empty S.Ty)) (β := γ) (A := A))
  let r := HasType.inr (A := A) (HasType.newest (Φ := S.Instr)
    (Γ := (Ctx.nil : Ctx Empty S.Ty)) (β := γ) (A := B))
  let c := HasType.case x l r
  have cEta := Eqv.ax (pureEff := S.pureEff) (.structural (.caseEta _)) c x
  have e := Eqv.let₁ cEta (Eqv.refl h.underBinder)
  have varBeta := Eqv.ax (.structural (.letBeta (pureEff := S.pureEff) .bv))
    (.let₁ x h.underBinder) (h.underBinder.instantiate x)
  rw [Tm.instantiate_underBinder_bv_zero] at varBeta
  have seq := Eqv.ax (pureEff := S.pureEff) (.sequencing (.bindLetCase _ _ _ _))
    (.let₁ c h.underBinder)
    (.case x (.let₁ l h.underBinder.underBinder) (.let₁ r h.underBinder.underBinder))
  have lb := Eqv.ax (.structural (.letBeta (pureEff := S.pureEff) (.inl .bv)))
    (.let₁ l h.underBinder.underBinder) (h.underBinder.underBinder.instantiate l)
  have rb := Eqv.ax (.structural (.letBeta (pureEff := S.pureEff) (.inr .bv)))
    (.let₁ r h.underBinder.underBinder) (h.underBinder.underBinder.instantiate r)
  rw [specialize_underCase] at lb rb
  exact (e.trans varBeta).symm.trans (seq.trans (.case (.refl x) lb rb))

private theorem rebuildProduct {R A D : SynCat S} {t : Tm Empty S.Instr 1}
    (h : HasType S.Instr Ctx.nil (.snoc .nil (tensor R.ty A.ty)) t D.ty) :
    Eqv S.pureEff Ctx.nil (.snoc .nil (tensor R.ty A.ty)) t
      (.let₂ (.bv 0) (bsubst (fun _ => .pair (.bv 1) (.bv 0)) t)) D.ty := by
  let P := tensor R.ty A.ty
  let x := HasType.newest (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty)) (β := .nil) (A := P)
  let p := HasType.pair (HasType.previous (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty)) (β := .snoc .nil P) (A := R.ty) (B := A.ty)) HasType.newest
  let a := HasType.let₂ x p
  have eta := Eqv.ax (pureEff := S.pureEff) (.structural (.pairEta _)) a x
  have h₁ := Eqv.let₁ eta (Eqv.refl h.underBinder)
  have id : Eqv S.pureEff Ctx.nil (.snoc .nil P) (.let₁ (.bv 0) (underBinder t)) t D.ty := by
    have e := Eqv.ax (.structural (.letBeta (pureEff := S.pureEff) .bv))
      (.let₁ x h.underBinder) (h.underBinder.instantiate x)
    rwa [Tm.instantiate_underBinder_bv_zero] at e
  have seq := Eqv.ax (pureEff := S.pureEff) (.sequencing (.bindLetPair _ _ _))
    (.let₁ a h.underBinder) (.let₂ x (.let₁ p h.underBinder.underBinder.underBinder))
  have shift : underBinder (underBinder (underBinder t)) = onNewest t := by
    rw [underBinder, underBinder, underBinder, rename_comp, rename_comp]
    exact rename_congr (Fin.cases rfl (fun i => i.elim0)) _
  rw [shift] at seq
  let k := onNewestTyping (β := ((BoundCtx.nil.snoc P).snoc R.ty).snoc A.ty) h
  have beta := Eqv.ax (.structural (.letBeta (pureEff := S.pureEff) (.pair .bv .bv)))
    (.let₁ p k) (k.instantiate p)
  rw [subst_onNewest] at beta
  exact (h₁.trans id).symm.trans (seq.trans (.let₂ (.refl x) beta))

private theorem tensorLeft_injl_specialization {n : Nat} {β : BoundCtx S.Ty n}
    {R A B D : SynCat S} {r a : Tm Empty S.Instr n} {t : Tm Empty S.Instr 1}
    (hr : HasType S.Instr Ctx.nil β r R.ty) (ha : HasType S.Instr Ctx.nil β a A.ty)
    (pr : Pure S.pureEff r) (pa : Pure S.pureEff a)
    (ht : HasType S.Instr Ctx.nil (.snoc .nil (productObj R (cop A B)).ty) t D.ty) :
    packedArrow (.pair hr ha) ≫ tensorLeft R (injl A B) ≫ (mk ht : productObj R (cop A B) ⟶ D) =
      packedArrow (applyTyping (.pair hr (.inl (B := B.ty) ha)) ht) := by
  have inj : packedArrow ha ≫ injl A B = packedArrow (.inl (B := B.ty) ha) :=
    packedArrow_apply ha pa (HasType.inl HasType.newest)
  let k : productObj R (cop A B) ⟶ D := mk ht
  have step : packedArrow (.pair hr ha) ≫ tensorLeft R (injl A B) =
      packedArrow (.pair hr (.inl ha)) := by
    change pairArrows (packedArrow hr) (packedArrow ha) ≫ tensorLeft R (injl A B) = _
    rw [tensorLeft_pair (R := R) (packedArrow_isPureMor hr pr) (packedArrow_isPureMor ha pa), inj]
    rfl
  exact (Category.assoc _ _ k).symm.trans
    ((congrArg (fun g => g ≫ k) step).trans
      (packedArrow_apply (A := productObj R (cop A B)) (B := D)
        (.pair hr (.inl ha)) (.pair pr (.inl pa)) ht))

private theorem tensorLeft_injr_specialization {n : Nat} {β : BoundCtx S.Ty n}
    {R A B D : SynCat S} {r b : Tm Empty S.Instr n} {t : Tm Empty S.Instr 1}
    (hr : HasType S.Instr Ctx.nil β r R.ty) (hb : HasType S.Instr Ctx.nil β b B.ty)
    (pr : Pure S.pureEff r) (pb : Pure S.pureEff b)
    (ht : HasType S.Instr Ctx.nil (.snoc .nil (productObj R (cop A B)).ty) t D.ty) :
    packedArrow (.pair hr hb) ≫ tensorLeft R (injr A B) ≫ (mk ht : productObj R (cop A B) ⟶ D) =
      packedArrow (applyTyping (.pair hr (.inr (A := A.ty) hb)) ht) := by
  have inj : packedArrow hb ≫ injr A B = packedArrow (.inr (A := A.ty) hb) :=
    packedArrow_apply hb pb (HasType.inr HasType.newest)
  let k : productObj R (cop A B) ⟶ D := mk ht
  have step : packedArrow (.pair hr hb) ≫ tensorLeft R (injr A B) =
      packedArrow (.pair hr (.inr hb)) := by
    change pairArrows (packedArrow hr) (packedArrow hb) ≫ tensorLeft R (injr A B) = _
    rw [tensorLeft_pair (R := R) (packedArrow_isPureMor hr pr) (packedArrow_isPureMor hb pb), inj]
    rfl
  exact (Category.assoc _ _ k).symm.trans
    ((congrArg (fun g => g ≫ k) step).trans
      (packedArrow_apply (A := productObj R (cop A B)) (B := D)
        (.pair hr (.inr hb)) (.pair pr (.inr pb)) ht))

theorem tensorLeft_coprod_hom_ext_proof (R A B : SynCat S) {D : SynCat S}
    {f g : productObj R (cop A B) ⟶ D}
    (left : tensorLeft R (injl A B) ≫ f = tensorLeft R (injl A B) ≫ g)
    (right : tensorLeft R (injr A B) ≫ f = tensorLeft R (injr A B) ≫ g) : f = g := by
  induction f using Syn.ind with
  | H f hf =>
    induction g using Syn.ind with
    | H g hg =>
      let P := (productObj R (cop A B)).ty
      let δ := BoundCtx.nil.snoc P
      let γ := (δ.snoc R.ty).snoc (cop A B).ty
      let l := HasType.bv (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty)) (β := γ) (ι := 1)
      let r := HasType.newest (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty))
        (β := δ.snoc R.ty) (A := (cop A B).ty)
      let a := HasType.newest (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty)) (β := γ) (A := A.ty)
      let b := HasType.newest (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty)) (β := γ) (A := B.ty)
      let lA := HasType.bv (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty)) (β := γ.snoc A.ty) (ι := 2)
      let lB := HasType.bv (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty)) (β := γ.snoc B.ty) (ι := 2)
      have hl := congrArg (fun k => packedArrow (.pair lA a) ≫ k) left
      have hr := congrArg (fun k => packedArrow (.pair lB b) ≫ k) right
      have hleft := (tensorLeft_injl_specialization (R := R) (A := A) (B := B) (D := D)
        lA a .bv .bv hf).symm.trans (hl.trans
          (tensorLeft_injl_specialization (R := R) (A := A) (B := B) (D := D) lA a .bv .bv hg))
      have hright := (tensorLeft_injr_specialization (R := R) (A := A) (B := B) (D := D)
        lB b .bv .bv hf).symm.trans (hr.trans
          (tensorLeft_injr_specialization (R := R) (A := A) (B := B) (D := D) lB b .bv .bv hg))
      have collapse {m : Nat} (σ : Fin 3 → Tm Empty S.Instr m) (t : Tm Empty S.Instr 1) :
          bsubst σ (bsubst (fun _ : Fin 1 => .pair (.bv 1) (.bv 0)) t) =
            bsubst (fun _ : Fin 1 => .pair (σ 1) (σ 0)) t :=
        bsubst_comp σ _ t
      have sf := splitSum_proof (A := A.ty) (B := B.ty) (applyTyping (.pair l r) hf)
      have sg := splitSum_proof (A := A.ty) (B := B.ty) (applyTyping (.pair l r) hg)
      simp only [collapse] at sf sg
      have e := sf.trans ((Eqv.case (.refl r)
        ((packedArrow_eq_iff _ _).mp hleft) ((packedArrow_eq_iff _ _).mp hright)).trans sg.symm)
      apply Quotient.sound
      let x := HasType.newest (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty)) (β := .nil) (A := P)
      exact (rebuildProduct (R := R) (A := cop A B) hf).trans
        ((Eqv.let₂ (.refl x) e).trans (rebuildProduct (R := R) (A := cop A B) hg).symm)

private def copairBodyTyping {n : Nat} {β : BoundCtx S.Ty n} {R A B D : SynCat S}
    {l r : Tm Empty S.Instr 1}
    (hl : HasType S.Instr Ctx.nil (.snoc .nil (productObj R A).ty) l D.ty)
    (hr : HasType S.Instr Ctx.nil (.snoc .nil (productObj R B).ty) r D.ty) :
    HasType S.Instr Ctx.nil ((β.snoc R.ty).snoc (cop A B).ty)
      (.case (.bv 0) (bsubst (fun _ => .pair (.bv 2) (.bv 0)) l)
        (bsubst (fun _ => .pair (.bv 2) (.bv 0)) r)) D.ty :=
  .case HasType.newest
    (applyTyping (.pair (.bv (ι := 2)) HasType.newest) hl)
    (applyTyping (.pair (.bv (ι := 2)) HasType.newest) hr)

private def copairTyping {R A B D : SynCat S}
    {l r : Tm Empty S.Instr 1}
    (hl : HasType S.Instr Ctx.nil (.snoc .nil (productObj R A).ty) l D.ty)
    (hr : HasType S.Instr Ctx.nil (.snoc .nil (productObj R B).ty) r D.ty) :
    HasType S.Instr Ctx.nil (.snoc .nil (productObj R (cop A B)).ty)
      (.let₂ (.bv 0) (.case (.bv 0) (bsubst (fun _ => .pair (.bv 2) (.bv 0)) l)
        (bsubst (fun _ => .pair (.bv 2) (.bv 0)) r))) D.ty :=
  .let₂ HasType.newest (copairBodyTyping (R := R) (A := A) (B := B) (D := D) hl hr)

private theorem open_copair_body {n : Nat} {β : BoundCtx S.Ty n} {R A B D : SynCat S}
    {l r : Tm Empty S.Instr 1}
    (hl : HasType S.Instr Ctx.nil (.snoc .nil (productObj R A).ty) l D.ty)
    (hr : HasType S.Instr Ctx.nil (.snoc .nil (productObj R B).ty) r D.ty)
    {u s : Tm Empty S.Instr n}
    (hu : HasType S.Instr Ctx.nil β u R.ty) (hs : HasType S.Instr Ctx.nil β s (cop A B).ty)
    (pu : Pure S.pureEff u) (ps : Pure S.pureEff s) :
    Eqv S.pureEff Ctx.nil β
      (bsubst (fun _ : Fin 1 => .pair u s)
        (.let₂ (.bv 0) (.case (.bv 0) (bsubst (fun _ => .pair (.bv 2) (.bv 0)) l)
          (bsubst (fun _ => .pair (.bv 2) (.bv 0)) r))))
      (.case s (bsubst (fun _ => .pair (lift u) (.bv 0)) l)
        (bsubst (fun _ => .pair (lift u) (.bv 0)) r)) D.ty := by
  let p := HasType.pair hu hs
  let body := copairBodyTyping (β := β) (R := R) (A := A) (B := B) (D := D) hl hr
  -- The original input is unused once its components have been bound.
  have bodyEq : bsubst (fun _ : Fin 1 => .pair u s)
      (.let₂ (.bv 0) (.case (.bv 0) (bsubst (fun _ => .pair (.bv 2) (.bv 0)) l)
        (bsubst (fun _ => .pair (.bv 2) (.bv 0)) r))) =
      .let₂ (.pair u s)
        (.case (.bv 0) (bsubst (fun _ => .pair (.bv 2) (.bv 0)) l)
          (bsubst (fun _ => .pair (.bv 2) (.bv 0)) r)) := by
    simp only [bsubst_let₂, bsubst_case, bsubst_bv, bsubst_comp, bsubst_pair]
    rfl
  rw [bodyEq]
  let inner := body.instantiate hs.lift
  let final := inner.instantiate hu
  have step := Eqv.ax (pureEff := S.pureEff) (.structural (.pairBeta _ _ _))
    (.let₂ p body) (.let₁ hu (.let₁ hs.lift body))
  have right := Eqv.ax (.structural (.letBeta (ps.rename Fin.succ))) (.let₁ hs.lift body) inner
  have left := Eqv.ax (.structural (.letBeta pu)) (.let₁ hu inner) final
  have opened : instantiate
      (instantiate (.case (.bv 0) (bsubst (fun _ => .pair (.bv 2) (.bv 0)) l)
        (bsubst (fun _ => .pair (.bv 2) (.bv 0)) r)) (lift s)) u =
      .case s (bsubst (fun _ => .pair (lift u) (.bv 0)) l)
        (bsubst (fun _ => .pair (lift u) (.bv 0)) r) := by
    simp only [instantiate, bsubst_case, bsubst_bv, bsubst_comp, bsubst_pair, Fin.cases_zero,
      lift, bsubst_rename, Fin.cases_succ]
    have id : bsubst (fun i => .bv i) s = s := by rw [bsubst_bv_eq_rename, rename_id]
    rw [id]
    rfl
  rw [opened] at left
  exact step.trans ((Eqv.let₁ (.refl hu) right).trans left)

private theorem instantiate_pair_application {n : Nat}
    (u a : Tm Empty S.Instr n) (l : Tm Empty S.Instr 1) :
    instantiate (bsubst (fun _ => .pair (lift u) (.bv 0)) l) a =
      bsubst (fun _ => .pair u a) l := by
  simp only [instantiate, bsubst_comp, bsubst_pair, bsubst_bv, Fin.cases_zero, lift, bsubst_rename,
      Fin.cases_succ]
  have id : bsubst (fun i => .bv i) u = u := by rw [bsubst_bv_eq_rename, rename_id]
  rw [id]

private theorem reduce_copair_left {n : Nat} {β : BoundCtx S.Ty n}
    {R A B D : SynCat S} {l r : Tm Empty S.Instr 1}
    (hl : HasType S.Instr Ctx.nil (.snoc .nil (productObj R A).ty) l D.ty)
    (hr : HasType S.Instr Ctx.nil (.snoc .nil (productObj R B).ty) r D.ty)
    {u a : Tm Empty S.Instr n}
    (hu : HasType S.Instr Ctx.nil β u R.ty) (ha : HasType S.Instr Ctx.nil β a A.ty)
    (pu : Pure S.pureEff u) (pa : Pure S.pureEff a) :
    packedArrow (applyTyping (.pair hu (.inl (B := B.ty) ha))
      (copairTyping (R := R) (A := A) (B := B) (D := D) hl hr)) =
      packedArrow (applyTyping (.pair hu ha) hl) := by
  apply (packedArrow_eq_iff _ _).mpr
  refine (open_copair_body hl hr hu (.inl ha) pu (.inl pa)).trans ?_
  let body := applyTyping (.pair hu.lift
    (HasType.newest (β := β) (A := A.ty))) hl
  let other := applyTyping (.pair hu.lift
    (HasType.newest (β := β) (A := B.ty))) hr
  let scrut := HasType.inl (B := B.ty) ha
  let lh := HasType.let₁ ha body
  refine (Eqv.ax (.structural (.caseBetaL _ _ _)) (.case scrut body other) lh).trans ?_
  have beta := Eqv.ax (.structural (.letBeta pa)) lh (body.instantiate ha)
  rwa [instantiate_pair_application] at beta

private theorem reduce_copair_right {n : Nat} {β : BoundCtx S.Ty n}
    {R A B D : SynCat S} {l r : Tm Empty S.Instr 1}
    (hl : HasType S.Instr Ctx.nil (.snoc .nil (productObj R A).ty) l D.ty)
    (hr : HasType S.Instr Ctx.nil (.snoc .nil (productObj R B).ty) r D.ty)
    {u b : Tm Empty S.Instr n}
    (hu : HasType S.Instr Ctx.nil β u R.ty) (hb : HasType S.Instr Ctx.nil β b B.ty)
    (pu : Pure S.pureEff u) (pb : Pure S.pureEff b) :
    packedArrow (applyTyping (.pair hu (.inr (A := A.ty) hb))
      (copairTyping (R := R) (A := A) (B := B) (D := D) hl hr)) =
      packedArrow (applyTyping (.pair hu hb) hr) := by
  apply (packedArrow_eq_iff _ _).mpr
  refine (open_copair_body hl hr hu (.inr hb) pu (.inr pb)).trans ?_
  let body := applyTyping (.pair hu.lift
    (HasType.newest (β := β) (A := B.ty))) hr
  let other := applyTyping (.pair hu.lift
    (HasType.newest (β := β) (A := A.ty))) hl
  let scrut := HasType.inr (A := A.ty) hb
  let rh := HasType.let₁ hb body
  refine (Eqv.ax (.structural (.caseBetaR _ _ _)) (.case scrut other body) rh).trans ?_
  have beta := Eqv.ax (.structural (.letBeta pb)) rh (body.instantiate hb)
  rwa [instantiate_pair_application] at beta

private theorem eq_of_product_test (R A : SynCat S) {D : SynCat S}
    {f g : productObj R A ⟶ D}
    (test : let δ := BoundCtx.nil.snoc (productObj R A).ty
            let x := HasType.previous (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty))
              (β := δ) (A := R.ty) (B := A.ty)
            let y := HasType.newest (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty))
              (β := δ.snoc R.ty) (A := A.ty)
            packedArrow (.pair x y) ≫ f = packedArrow (.pair x y) ≫ g) : f = g := by
  induction f using Syn.ind with
  | H f hf =>
    induction g using Syn.ind with
    | H g hg =>
      let δ := BoundCtx.nil.snoc (productObj R A).ty
      let x := HasType.previous (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty))
        (β := δ) (A := R.ty) (B := A.ty)
      let y := HasType.newest (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty))
        (β := δ.snoc R.ty) (A := A.ty)
      have a := packedArrow_apply (A := productObj R A) (B := D) (.pair x y) (.pair .bv .bv) hf
      have b := packedArrow_apply (A := productObj R A) (B := D) (.pair x y) (.pair .bv .bv) hg
      have e := (packedArrow_eq_iff _ _).mp (a.symm.trans (test.trans b))
      apply Quotient.sound
      let p := HasType.newest (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty)) (β := .nil)
        (A := (productObj R A).ty)
      exact (rebuildProduct (R := R) (A := A) hf).trans
        ((Eqv.let₂ (.refl p) e).trans (rebuildProduct (R := R) (A := A) hg).symm)

private theorem copair_injl {R A B D : SynCat S} {l r : Tm Empty S.Instr 1}
    (hl : HasType S.Instr Ctx.nil (.snoc .nil (productObj R A).ty) l D.ty)
    (hr : HasType S.Instr Ctx.nil (.snoc .nil (productObj R B).ty) r D.ty) :
    tensorLeft R (injl A B) ≫ (mk (copairTyping (R := R) (A := A) (B := B) (D := D) hl hr) :
      productObj R (cop A B) ⟶ D) = (mk hl : productObj R A ⟶ D) := by
  apply eq_of_product_test R A
  intro δ x y
  exact (tensorLeft_injl_specialization (R := R) (A := A) (B := B) (D := D) x y .bv .bv
    (copairTyping hl hr)).trans ((reduce_copair_left hl hr x y .bv .bv).trans
      (packedArrow_apply (A := productObj R A) (B := D) (.pair x y) (.pair .bv .bv) hl).symm)

private theorem copair_injr {R A B D : SynCat S} {l r : Tm Empty S.Instr 1}
    (hl : HasType S.Instr Ctx.nil (.snoc .nil (productObj R A).ty) l D.ty)
    (hr : HasType S.Instr Ctx.nil (.snoc .nil (productObj R B).ty) r D.ty) :
    tensorLeft R (injr A B) ≫ (mk (copairTyping (R := R) (A := A) (B := B) (D := D) hl hr) :
      productObj R (cop A B) ⟶ D) = (mk hr : productObj R B ⟶ D) := by
  apply eq_of_product_test R B
  intro δ x y
  exact (tensorLeft_injr_specialization (R := R) (A := A) (B := B) (D := D) x y .bv .bv
    (copairTyping hl hr)).trans ((reduce_copair_right hl hr x y .bv .bv).trans
      (packedArrow_apply (A := productObj R B) (B := D) (.pair x y) (.pair .bv .bv) hr).symm)

theorem tensorLeft_coprod_exists (R A B : SynCat S) {D : SynCat S}
    (f : productObj R A ⟶ D) (g : productObj R B ⟶ D) :
    ∃ h : productObj R (cop A B) ⟶ D,
      tensorLeft R (injl A B) ≫ h = f ∧ tensorLeft R (injr A B) ≫ h = g := by
  induction f using Syn.ind with
  | H l hl =>
    induction g using Syn.ind with
    | H r hr =>
      exact ⟨mk (copairTyping hl hr), copair_injl hl hr, copair_injr hl hr⟩

theorem tensorLeft_value_coprod_exists (R A B : SynCat S) {D : SynCat S}
    {f : productObj R A ⟶ D} {g : productObj R B ⟶ D} (pf : IsPureMor f) (pg : IsPureMor g) :
    ∃ h : productObj R (cop A B) ⟶ D,
      IsPureMor h ∧ tensorLeft R (injl A B) ≫ h = f ∧ tensorLeft R (injr A B) ≫ h = g := by
  obtain ⟨l, hl, pl, rfl⟩ := pf
  obtain ⟨r, hr, pr, rfl⟩ := pg
  let h := copairTyping (R := R) (A := A) (B := B) (D := D) hl hr
  have pure : Pure S.pureEff
      ((.let₂ (.bv 0) (.case (.bv 0) (bsubst (fun _ => .pair (.bv 2) (.bv 0)) l)
        (bsubst (fun _ => .pair (.bv 2) (.bv 0)) r))) : Tm Empty S.Instr 1) :=
    .let₂ .bv (.case .bv
      (pl.bsubst (fun _ => .pair .bv .bv)) (pr.bsubst (fun _ => .pair .bv .bv)))
  exact ⟨mk h, ⟨_, h, pure, rfl⟩, copair_injl hl hr, copair_injr hl hr⟩

theorem computationDistributive_proof (S : Sig.{u}) : DistributiveTensor (SynCat S) := by
  constructor
  intro R A B
  let F := tensorLeftFunctor R
  let l := tensorLeft R (injl A B)
  let r := tensorLeft R (injr A B)
  let h : IsColimit (BinaryCofan.mk l r) := BinaryCofan.isColimitMk
    (fun s => (tensorLeft_coprod_exists R A B s.inl s.inr).choose)
    (fun s => (tensorLeft_coprod_exists R A B s.inl s.inr).choose_spec.1)
    (fun s => (tensorLeft_coprod_exists R A B s.inl s.inr).choose_spec.2)
    (fun s m hl hr => tensorLeft_coprod_hom_ext_proof R A B
      (hl.trans (tensorLeft_coprod_exists R A B s.inl s.inr).choose_spec.1.symm)
      (hr.trans (tensorLeft_coprod_exists R A B s.inl s.inr).choose_spec.2.symm))
  have : PreservesColimit (pair A B) F :=
    preservesColimit_of_preserves_colimit_cocone (isColimitBinaryCofan A B)
      ((isColimitMapCoconeBinaryCofanEquiv F _ _).symm h)
  change IsIso (coprodComparison F A B)
  infer_instance

theorem valuesDistributive_proof (S : Sig.{u}) : DistributiveTensor (ValueCat S) := by
  constructor
  intro R A B
  let F := MonoidalCategory.tensorLeft R
  let l := F.map (valueCofan A B).inl
  let r := F.map (valueCofan A B).inr
  have leftEq : l.hom = tensorLeft R.obj (injl A.obj B.obj) :=
    (tensorLeft_value (R := R) (valueCofan A B).inl).symm
  have rightEq : r.hom = tensorLeft R.obj (injr A.obj B.obj) :=
    (tensorLeft_value (R := R) (valueCofan A B).inr).symm
  have existsArrow (s : BinaryCofan (R ⊗ A) (R ⊗ B)) :
      ∃ h : F.obj (valueCofan A B).pt ⟶ s.pt, l ≫ h = s.inl ∧ r ≫ h = s.inr := by
    obtain ⟨h, hp, hl, hr⟩ := tensorLeft_value_coprod_exists R.obj A.obj B.obj
      s.inl.property s.inr.property
    refine ⟨⟨h, hp⟩, WideSubcategory.hom_ext (pureProperty S) ?_,
      WideSubcategory.hom_ext (pureProperty S) ?_⟩
    · change l.hom ≫ h = _
      exact (congrArg (fun k => k ≫ h) leftEq).trans hl
    · change r.hom ≫ h = _
      exact (congrArg (fun k => k ≫ h) rightEq).trans hr
  let h : IsColimit (BinaryCofan.mk l r) := BinaryCofan.isColimitMk
    (fun s => (existsArrow s).choose)
    (fun s => (existsArrow s).choose_spec.1)
    (fun s => (existsArrow s).choose_spec.2)
    (fun s m hl hr => WideSubcategory.hom_ext (pureProperty S) (by
      have left := congrArg (fun a => a.hom) (hl.trans (existsArrow s).choose_spec.1.symm)
      have right := congrArg (fun a => a.hom) (hr.trans (existsArrow s).choose_spec.2.symm)
      change l.hom ≫ m.hom = l.hom ≫ (existsArrow s).choose.hom at left
      change r.hom ≫ m.hom = r.hom ≫ (existsArrow s).choose.hom at right
      rw [leftEq] at left
      rw [rightEq] at right
      exact tensorLeft_coprod_hom_ext_proof R.obj A.obj B.obj left right))
  have : PreservesColimit (pair A B) F :=
    preservesColimit_of_preserves_colimit_cocone (valueCofanIsColimit A B)
      ((isColimitMapCoconeBinaryCofanEquiv F _ _).symm h)
  change IsIso (coprodComparison F A B)
  infer_instance

end Silmaril.Thesis.LambdaIter.Syn.SynCat

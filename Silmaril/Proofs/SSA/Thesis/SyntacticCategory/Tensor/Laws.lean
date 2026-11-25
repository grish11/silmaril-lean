module

public import Silmaril.SSA.Thesis.SyntacticCategory.Tensor.Defs

public section

universe u

namespace Silmaril.Thesis.LambdaIter.Syn.SynCat

open CategoryTheory
open scoped MonoidalCategory
open LocallyNameless LocallyNameless.Tm LocallyNameless.Syntax

variable {S : Sig.{u}}

private theorem rename_onNewest {n m : Nat} (ρ : Fin (n + 1) → Fin (m + 1))
    (h : ρ 0 = 0) (t : Tm Empty S.Instr 1) :
    rename ρ (onNewest t) = onNewest t := by
  rw [onNewest, onNewest, rename_comp]
  exact rename_congr (fun _ => h) _

private theorem instantiate_left_body {n : Nat} (t : Tm Empty S.Instr 1)
    (a : Tm Empty S.Instr (n + 1)) :
    instantiate (tensorLeftBody (n := n) t) a =
      .let₁ (bsubst (fun _ => a) t) (.pair (.bv 1) (.bv 0)) := by
  simp only [instantiate, tensorLeftBody, onNewest, bsubst_let₁, bsubst_rename,
    bsubst_pair, bsubst_bv, Fin.cases_zero]
  rfl

private theorem instantiate_twice_left_body {n : Nat} (t : Tm Empty S.Instr 1)
    (a b : Tm Empty S.Instr n) :
    instantiate (instantiate (tensorLeftBody t) (lift b)) a =
      .let₁ (bsubst (fun _ => b) t) (.pair (lift a) (.bv 0)) := by
  rw [instantiate_left_body]
  simp only [instantiate, bsubst_let₁, bsubst_pair, bsubst_bv, bsubst_comp, lift, bsubst_rename,
    Fin.cases_succ]
  have hb : bsubst (fun i => .bv i) b = b := by rw [bsubst_bv_eq_rename, rename_id]
  rw [hb]
  rfl

private theorem left_on_pair {n : Nat} {β : BoundCtx S.Ty n} {R A B : S.Ty}
    {t : Tm Empty S.Instr 1} (h : HasType S.Instr Ctx.nil (.snoc .nil A) t B)
    {a b : Tm Empty S.Instr n} (ha : HasType S.Instr Ctx.nil β a R)
    (hb : HasType S.Instr Ctx.nil β b A) (hpa : Pure S.pureEff a) (hpb : Pure S.pureEff b) :
    Eqv S.pureEff Ctx.nil β
      (.let₂ (.pair a b) (tensorLeftBody t))
      (.let₁ (bsubst (fun _ => b) t) (.pair (lift a) (.bv 0))) (tensor R B) := by
  let ht := tensorLeftBodyTyping (β := β) (R := R) h
  let h₁ := ht.instantiate hb.lift
  let h₂ := h₁.instantiate ha
  refine (Eqv.ax (.structural (.pairBeta a b _)) (.let₂ (.pair ha hb) ht)
    (.let₁ ha (.let₁ hb.lift ht))).trans ?_
  refine (Eqv.let₁ (.refl ha)
    (.ax (.structural (.letBeta (hpb.rename _))) (.let₁ hb.lift ht) h₁)).trans ?_
  have e := Eqv.ax (.structural (.letBeta hpa)) (.let₁ ha h₁) h₂
  rwa [instantiate_twice_left_body] at e

private theorem bsubst_tensorLeftTm {n : Nat} (σ : Fin 1 → Tm Empty S.Instr n)
    (t : Tm Empty S.Instr 1) :
    bsubst σ (tensorLeftTm t) = .let₂ (σ 0) (tensorLeftBody t) := by
  simp only [tensorLeftTm, tensorLeftBody, onNewest, bsubst_let₂, bsubst_let₁, bsubst_pair,
    bsubst_bv, bsubst_rename, upSub_zero]
  rw [bsubst_bv_eq_rename (fun _ => 0) t]
  rfl

private theorem instantiate_onNewest_tensor {n : Nat} (t : Tm Empty S.Instr 1)
    (p : Tm Empty S.Instr n) :
    instantiate (onNewest (tensorLeftTm t)) p = .let₂ p (tensorLeftBody t) := by
  rw [instantiate, onNewest, bsubst_rename, bsubst_tensorLeftTm]
  rfl

private theorem let_tensor_pair {n : Nat} {β : BoundCtx S.Ty n} {R A B : S.Ty}
    {t : Tm Empty S.Instr 1} (h : HasType S.Instr Ctx.nil (.snoc .nil A) t B)
    {a b : Tm Empty S.Instr n} (ha : HasType S.Instr Ctx.nil β a R)
    (hb : HasType S.Instr Ctx.nil β b A) (hpa : Pure S.pureEff a) (hpb : Pure S.pureEff b) :
    Eqv S.pureEff Ctx.nil β (.let₁ (.pair a b) (onNewest (tensorLeftTm t)))
      (.let₁ (bsubst (fun _ => b) t) (.pair (lift a) (.bv 0))) (tensor R B) := by
  let p := HasType.pair ha hb
  let c := onNewestTyping (β := β) (tensorLeftTyping (R := R) h)
  have e := Eqv.ax (.structural (.letBeta (.pair hpa hpb))) (.let₁ p c) (c.instantiate p)
  rw [instantiate_onNewest_tensor] at e
  exact e.trans (left_on_pair h ha hb hpa hpb)

private theorem underBinder_eq_onNewest (t : Tm Empty S.Instr 1) :
    underBinder t = onNewest t :=
  rename_congr (Fin.cases rfl (fun i => i.elim0)) _

private theorem underBinder_onNewest {n : Nat} (t : Tm Empty S.Instr 1) :
    underBinder (onNewest (n := n) t) = onNewest t :=
  rename_onNewest _ rfl _

private theorem onNewest_comp {n : Nat} (f g : Tm Empty S.Instr 1) :
    onNewest (n := n) (.let₁ f (underBinder g)) = .let₁ (onNewest f) (onNewest g) := by
  simp only [onNewest, rename_let₁, underBinder, rename_comp]
  congr 1
  exact rename_congr (Fin.cases rfl (fun i => i.elim0)) _

private theorem left_body_comp {n : Nat} {β : BoundCtx S.Ty n} {R A B C : S.Ty}
    {f g : Tm Empty S.Instr 1}
    (hf : HasType S.Instr Ctx.nil (.snoc .nil A) f B)
    (hg : HasType S.Instr Ctx.nil (.snoc .nil B) g C) :
    Eqv S.pureEff Ctx.nil (.snoc (.snoc β R) A)
      (.let₁ (tensorLeftBody f) (onNewest (tensorLeftTm g)))
      (tensorLeftBody (.let₁ f (underBinder g))) (tensor R C) := by
  let γ := (β.snoc R).snoc A
  let f' := onNewestTyping (β := β.snoc R) hf
  let g' := onNewestTyping (β := γ) hg
  let p : HasType S.Instr (Ctx.nil : Ctx Empty S.Ty) (.snoc γ B) (.pair (.bv 2) (.bv 0)) (tensor R B) :=
    .pair (.bv (ι := 2)) HasType.newest
  let q : HasType S.Instr (Ctx.nil : Ctx Empty S.Ty) (.snoc γ C) (.pair (.bv 2) (.bv 0)) (tensor R C) :=
    .pair (.bv (ι := 2)) HasType.newest
  let k := onNewestTyping (β := γ) (tensorLeftTyping (R := R) hg)
  have e₁ := Eqv.ax (pureEff := S.pureEff) (.sequencing (.bindLet _ _ _)) (.let₁ (.let₁ f' p) k)
    (.let₁ f' (.let₁ p k.underBinder))
  rw [underBinder_onNewest] at e₁
  have e₂ := let_tensor_pair hg
    (HasType.bv (β := .snoc γ B) (ι := 2)) (HasType.newest (β := γ) (A := B)) .bv .bv
  have sub : bsubst (fun _ : Fin 1 => .bv (0 : Fin (n + 3))) g = onNewest g :=
    bsubst_bv_eq_rename (fun _ => 0) g
  rw [sub] at e₂
  have e₃ := Eqv.ax (pureEff := S.pureEff) (.sequencing (.bindLet _ _ _)) (.let₁ (.let₁ f' g') q)
    (.let₁ f' (.let₁ g' q.underBinder))
  refine e₁.trans ((Eqv.let₁ (.refl f') e₂).trans ?_)
  rw [tensorLeftBody, onNewest_comp]
  exact e₃.symm

theorem tensorLeft_id_proof (R A : SynCat S) :
    tensorLeft R (𝟙 A) = 𝟙 (productObj R A) := by
  apply Quotient.sound
  let P := tensor R.ty A.ty
  have x : HasType S.Instr (Ctx.nil : Ctx Empty S.Ty) (.snoc .nil P) (.bv 0) P :=
    HasType.newest
  have body : HasType S.Instr (Ctx.nil : Ctx Empty S.Ty) (.snoc (.snoc (.snoc .nil P) R.ty) A.ty)
      (.pair (.bv 1) (.bv 0)) P :=
    .pair HasType.previous HasType.newest
  have step : HasType S.Instr (Ctx.nil : Ctx Empty S.Ty) (.snoc (.snoc (.snoc .nil P) R.ty) A.ty)
      (tensorLeftBody (.bv 0)) P :=
    tensorLeftBodyTyping (HasType.newest (A := A.ty))
  have e : Eqv S.pureEff (Ctx.nil : Ctx Empty S.Ty) _ (tensorLeftBody (.bv 0)) (.pair (.bv 1) (.bv 0)) P :=
    Eqv.ax (.structural (.letBeta .bv)) step body
  exact (Eqv.let₂ (Eqv.refl x) e).trans (Eqv.ax (.structural (.pairEta _)) (.let₂ x body) x)

private theorem after_destructuring {n : Nat} {β : BoundCtx S.Ty n} {R A B C : S.Ty}
    {p : Tm Empty S.Instr n} {body : Tm Empty S.Instr (n + 2)} {k : Tm Empty S.Instr 1}
    (hp : HasType S.Instr Ctx.nil β p (tensor R A))
    (hb : HasType S.Instr Ctx.nil (.snoc (.snoc β R) A) body B)
    (hk : HasType S.Instr Ctx.nil (.snoc .nil B) k C) :
    Eqv S.pureEff Ctx.nil β (.let₁ (.let₂ p body) (onNewest k))
      (.let₂ p (.let₁ body (onNewest k))) C := by
  let c := onNewestTyping (β := β) hk
  have e := Eqv.ax (pureEff := S.pureEff) (.sequencing (.bindLetPair _ _ _))
    (.let₁ (.let₂ hp hb) c) (.let₂ hp (.let₁ hb c.underBinder.underBinder))
  rwa [underBinder_onNewest, underBinder_onNewest] at e

theorem tensorLeft_comp_proof (R : SynCat S) {A B C : SynCat S}
    (f : A ⟶ B) (g : B ⟶ C) :
    tensorLeft R (f ≫ g) = tensorLeft R f ≫ tensorLeft R g := by
  induction f using Syn.ind with
  | H f hf =>
    induction g using Syn.ind with
    | H g hg =>
      apply Eq.symm
      apply Quotient.sound
      let β := BoundCtx.nil.snoc (tensor R.ty A.ty)
      let x : HasType S.Instr (Ctx.nil : Ctx Empty S.Ty) β (.bv 0) (tensor R.ty A.ty) := HasType.newest
      let l := tensorLeftBodyTyping (β := β) (R := R.ty) hf
      change Eqv S.pureEff Ctx.nil β
        (.let₁ (tensorLeftTm f) (underBinder (tensorLeftTm g)))
        (tensorLeftTm (.let₁ f (underBinder g))) (tensor R.ty C.ty)
      rw [underBinder_eq_onNewest (tensorLeftTm g)]
      exact (after_destructuring x l (tensorLeftTyping (R := R.ty) hg)).trans
        (.let₂ (.refl x) (left_body_comp hf hg))

theorem tensorLeft_isPureMor_proof (R : SynCat S) {A B : SynCat S}
    {f : A ⟶ B} (hf : IsPureMor f) : IsPureMor (tensorLeft R f) := by
  obtain ⟨t, ht, hp, rfl⟩ := hf
  exact ⟨tensorLeftTm t, tensorLeftTyping ht,
    .let₂ .bv (.let₁ (hp.rename _) (.pair .bv .bv)), rfl⟩

private theorem after_pure_tensor_body {n : Nat} {β : BoundCtx S.Ty n} {R A B C : S.Ty}
    {t k : Tm Empty S.Instr 1} (ht : HasType S.Instr Ctx.nil (.snoc .nil A) t B)
    (hp : Pure S.pureEff t) (hk : HasType S.Instr Ctx.nil (.snoc .nil (tensor R B)) k C) :
    Eqv S.pureEff Ctx.nil (.snoc (.snoc β R) A)
      (.let₁ (tensorLeftBody t) (onNewest k))
      (instantiate (onNewest k) (.pair (.bv 1) (onNewest t))) C := by
  let γ := (β.snoc R).snoc A
  let ht' := onNewestTyping (β := β.snoc R) ht
  let hp' := hp.rename (fun _ => (0 : Fin (n + 2)))
  let p := HasType.pair (HasType.previous (β := β) (A := R) (B := A)) ht'
  let k' := onNewestTyping (β := γ) hk
  have e : Eqv S.pureEff Ctx.nil γ (tensorLeftBody t) (.pair (.bv 1) (onNewest t))
      (tensor R B) := .ax (.structural (.letBeta hp')) (tensorLeftBodyTyping ht) p
  exact (Eqv.let₁ e (.refl k')).trans
    (.ax (.structural (.letBeta (.pair .bv hp'))) (.let₁ p k') (k'.instantiate p))

private theorem tensorLeft_first (R : SynCat S) {A B : SynCat S} {f : A ⟶ B}
    (hf : IsPureMor f) : tensorLeft R f ≫ first R B = first R A := by
  obtain ⟨t, ht, hp, rfl⟩ := hf
  apply Quotient.sound
  let β := BoundCtx.nil.snoc (tensor R.ty A.ty)
  let x : HasType S.Instr (Ctx.nil : Ctx Empty S.Ty) β (.bv 0) (tensor R.ty A.ty) :=
    HasType.newest
  let k := HasType.let₂ (A := R.ty) (B := B.ty)
    (HasType.newest (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty)) (β := .nil)) HasType.previous
  let e := after_destructuring x (tensorLeftBodyTyping ht) k
  have step := after_pure_tensor_body (β := β) ht hp k
  have head := first_beta (HasType.previous (β := β) (A := R.ty) (B := A.ty))
    (onNewestTyping (β := β.snoc R.ty) ht) (hp.rename _)
  change Eqv S.pureEff Ctx.nil β
    (.let₁ (tensorLeftTm t) (underBinder (.let₂ (.bv 0) (.bv 1)))) (.let₂ (.bv 0) (.bv 1)) R.ty
  rw [underBinder_eq_onNewest]
  exact e.trans (Eqv.let₂ (.refl x) (step.trans head))

private theorem after_tensor_second {n : Nat} {β : BoundCtx S.Ty n} {R A B : S.Ty}
    {t : Tm Empty S.Instr 1} (ht : HasType S.Instr Ctx.nil (.snoc .nil A) t B) :
    Eqv S.pureEff Ctx.nil (.snoc (.snoc β R) A)
      (.let₁ (tensorLeftBody t) (onNewest (.let₂ (.bv 0) (.bv 0)))) (onNewest t) B := by
  let γ := (β.snoc R).snoc A
  let f := onNewestTyping (β := β.snoc R) ht
  let left : HasType S.Instr (Ctx.nil : Ctx Empty S.Ty) (.snoc γ B) (.bv 2) R := .bv
  let right := HasType.newest (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty))
    (β := γ) (A := B)
  let p := HasType.pair left right
  let k := HasType.let₂ (A := R) (B := B)
    (HasType.newest (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty)) (β := .nil)) HasType.newest
  let c := onNewestTyping (β := γ) k
  have assoc := Eqv.ax (pureEff := S.pureEff) (.sequencing (.bindLet _ _ _))
    (.let₁ (.let₁ f p) c) (.let₁ f (.let₁ p c.underBinder))
  rw [underBinder_onNewest] at assoc
  let c' := onNewestTyping (β := γ.snoc B) k
  have beta := Eqv.ax (pureEff := S.pureEff) (.structural (.letBeta (.pair .bv .bv)))
    (.let₁ p c') (c'.instantiate p)
  have eta := Eqv.ax (pureEff := S.pureEff) (.structural (.letEta _))
    (.let₁ f HasType.newest) f
  exact assoc.trans ((Eqv.let₁ (.refl f)
    (beta.trans (second_beta left right .bv))).trans eta)

theorem tensorLeft_second_proof (R : SynCat S) {A B : SynCat S} (f : A ⟶ B) :
    tensorLeft R f ≫ second R B = second R A ≫ f := by
  induction f using Syn.ind with
  | H t ht =>
    apply Quotient.sound
    let β := BoundCtx.nil.snoc (tensor R.ty A.ty)
    let γ := (β.snoc R.ty).snoc A.ty
    let x : HasType S.Instr (Ctx.nil : Ctx Empty S.Ty) β (.bv 0) (tensor R.ty A.ty) :=
      HasType.newest
    let k := HasType.let₂ (A := R.ty) (B := B.ty)
      (HasType.newest (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty)) (β := .nil)) HasType.newest
    let e := after_destructuring x (tensorLeftBodyTyping ht) k
    let x₀ := HasType.newest (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty))
      (β := β.snoc R.ty) (A := A.ty)
    let hbody := onNewestTyping (β := γ) ht
    have beta : Eqv S.pureEff Ctx.nil γ (.let₁ (.bv 0) (onNewest t)) (onNewest t) B.ty := by
      have ax := Eqv.ax (pureEff := S.pureEff) (.structural (.letBeta .bv))
        (.let₁ x₀ hbody) (hbody.instantiate x₀)
      have openTerm : instantiate (onNewest t) (.bv (0 : Fin 3)) = onNewest t := by
        rw [instantiate, onNewest, bsubst_rename, onNewest]
        exact bsubst_bv_eq_rename (fun _ => 0) _
      rwa [openTerm] at ax
    change Eqv S.pureEff Ctx.nil β
      (.let₁ (tensorLeftTm t) (underBinder (.let₂ (.bv 0) (.bv 0))))
      (.let₁ (.let₂ (.bv 0) (.bv 0)) (underBinder t)) B.ty
    rw [underBinder_eq_onNewest, underBinder_eq_onNewest]
    exact (e.trans (Eqv.let₂ (.refl x) (after_tensor_second ht))).trans
      ((after_destructuring x x₀ ht).trans (Eqv.let₂ (.refl x) beta)).symm

theorem tensorLeft_value_proof {R A B : ValueCat S} (f : A ⟶ B) :
    tensorLeft R.obj f.hom = (CategoryTheory.MonoidalCategoryStruct.whiskerLeft R f).hom := by
  let g : R ⊗ A ⟶ R ⊗ B :=
    ⟨tensorLeft R.obj f.hom, tensorLeft_isPureMor_proof R.obj f.property⟩
  suffices h : g = CategoryTheory.MonoidalCategoryStruct.whiskerLeft R f by
    exact congrArg (fun a => a.hom) h
  apply CartesianMonoidalCategory.hom_ext
  · rw [CartesianMonoidalCategory.whiskerLeft_fst]
    exact WideSubcategory.hom_ext (pureProperty S) (tensorLeft_first R.obj f.property)
  · rw [CartesianMonoidalCategory.whiskerLeft_snd]
    exact WideSubcategory.hom_ext (pureProperty S) (tensorLeft_second_proof R.obj f.hom)

theorem tensorRight_value_proof {R A B : ValueCat S} (f : A ⟶ B) :
    tensorRight R.obj f.hom = (CategoryTheory.MonoidalCategoryStruct.whiskerRight f R).hom := by
  rw [tensorRight, tensorLeft_value_proof]
  let : BraidedCategory (ValueCat S) := BraidedCategory.ofCartesianMonoidalCategory
  have h : (valueSwap A.obj R.obj).hom ≫ (R ◁ f) ≫ (valueSwap B.obj R.obj).inv = f ▷ R := by
    change (BraidedCategory.braiding A R).hom ≫ (R ◁ f) ≫
      (BraidedCategory.braiding B R).inv = f ▷ R
    rw [← Category.assoc, ← BraidedCategory.braiding_naturality_left]
    simp
  exact congrArg (fun g => g.hom) h

theorem tensorRight_first_proof (R : SynCat S) {A B : SynCat S} (f : A ⟶ B) :
    tensorRight R f ≫ first B R = first A R ≫ f := by
  let : BraidedCategory (ValueCat S) := BraidedCategory.ofCartesianMonoidalCategory
  have hf : (tensorSwap B R).inv ≫ first B R = second R B :=
    congrArg (fun g => g.hom)
      (CartesianMonoidalCategory.braiding_inv_fst (⟨B⟩ : ValueCat S) ⟨R⟩)
  have hs : (tensorSwap A R).hom ≫ second R A = first A R :=
    congrArg (fun g => g.hom)
      (CartesianMonoidalCategory.braiding_hom_snd (⟨A⟩ : ValueCat S) ⟨R⟩)
  simp only [tensorRight, Category.assoc, hf]
  rw [tensorLeft_second_proof, ← Category.assoc, hs]

end Silmaril.Thesis.LambdaIter.Syn.SynCat

module

public import Silmaril.SSA.Thesis.SyntacticCategory.Values.Defs

public section

universe u

namespace Silmaril.Thesis.LambdaIter.Syn.SynCat

open CategoryTheory CategoryTheory.Limits
open LocallyNameless

variable {S : Sig.{u}}

theorem pureToUnit_unique_proof {A : SynCat S}
    {f : A ⟶ of (S := S) (unit : S.Ty)} (hf : IsPureMor f) :
    f = mk (HasType.unit (Φ := S.Instr) (Γ := Ctx.nil) (β := BoundCtx.nil.snoc A.ty)) := by
  obtain ⟨t, ht, hp, rfl⟩ := hf
  refine Quotient.sound ?_
  have hu : HasType S.Instr Ctx.nil (.snoc (.snoc .nil A.ty) (unit : S.Ty))
      (.unit : Tm Empty S.Instr 2) unit := .unit
  have h := HasType.let₁ ht hu
  exact (Eqv.ax (.structural (.unitEta t)) h ht).symm.trans
    (Eqv.ax (.structural (.letBeta hp)) h .unit)

theorem isPureMor_injl_proof (A B : SynCat S) : IsPureMor (injl A B) :=
  ⟨.inl (.bv 0), .inl HasType.newest, .inl .bv, rfl⟩

theorem isPureMor_injr_proof (A B : SynCat S) : IsPureMor (injr A B) :=
  ⟨.inr (.bv 0), .inr HasType.newest, .inr .bv, rfl⟩

theorem isPureMor_desc_proof {A B C : SynCat S} {l : A ⟶ C} {r : B ⟶ C}
    (hl : IsPureMor l) (hr : IsPureMor r) : IsPureMor (desc l r) := by
  obtain ⟨lt, lht, lhp, rfl⟩ := hl
  obtain ⟨rt, rht, rhp, rfl⟩ := hr
  exact ⟨_, HasType.case (A := A.ty) (B := B.ty) HasType.newest lht.underBinder rht.underBinder,
    .case .bv (lhp.rename _) (rhp.rename _), rfl⟩

theorem isPureMor_first_proof (A B : SynCat S) : IsPureMor (first A B) :=
  ⟨_, HasType.let₂ HasType.newest (.bv (ι := 1)), .let₂ .bv .bv, rfl⟩

theorem isPureMor_second_proof (A B : SynCat S) : IsPureMor (second A B) :=
  ⟨_, HasType.let₂ HasType.newest HasType.newest, .let₂ .bv .bv, rfl⟩

theorem isPureMor_pairArrows_proof {X A B : SynCat S} {f : X ⟶ A} {g : X ⟶ B}
    (hf : IsPureMor f) (hg : IsPureMor g) : IsPureMor (pairArrows f g) := by
  obtain ⟨a, ha, hpa, rfl⟩ := hf
  obtain ⟨b, hb, hpb, rfl⟩ := hg
  exact ⟨.pair a b, .pair ha hb, .pair hpa hpb, rfl⟩

private theorem instantiate_lift {n : Nat} (b a : Tm Empty S.Instr n) :
    Tm.instantiate (Tm.lift b) a = b := by
  simp only [Tm.instantiate, Tm.lift, Syntax.bsubst_rename]
  change Tm.bsubst (fun i => Tm.bv i) b = b
  rw [Syntax.bsubst_bv_eq_rename, Syntax.rename_id]

theorem first_beta_proof {n : Nat} {β : BoundCtx S.Ty n}
    {a b : Tm Empty S.Instr n} {A B : S.Ty}
    (ha : HasType S.Instr Ctx.nil β a A) (hb : HasType S.Instr Ctx.nil β b B) :
    Pure S.pureEff b → Eqv S.pureEff Ctx.nil β (.let₂ (.pair a b) (.bv 1)) a A := by
  intro hp
  have h₁ := HasType.let₂ (.pair ha hb) (.bv (ι := 1))
  have h₂ := HasType.let₁ ha (HasType.let₁ hb.lift (.bv (ι := 1)))
  have h₃ := HasType.let₁ ha HasType.newest
  refine (Eqv.ax (.structural (.pairBeta a b (.bv 1))) h₁ h₂).trans ?_
  refine (Eqv.let₁ (Eqv.refl ha)
    (Eqv.ax (.structural (.letBeta (a := Tm.lift b) (b := .bv 1) (hp.rename _)))
      (HasType.let₁ hb.lift (.bv (ι := 1))) HasType.newest)).trans ?_
  exact Eqv.ax (.structural (.letEta a)) h₃ ha

theorem second_beta_proof {n : Nat} {β : BoundCtx S.Ty n}
    {a b : Tm Empty S.Instr n} {A B : S.Ty}
    (ha : HasType S.Instr Ctx.nil β a A) (hb : HasType S.Instr Ctx.nil β b B)
    (hpa : Pure S.pureEff a) :
    Eqv S.pureEff Ctx.nil β (.let₂ (.pair a b) (.bv 0)) b B := by
  have h₁ := HasType.let₂ (.pair ha hb) HasType.newest
  have h₂ := HasType.let₁ ha (HasType.let₁ hb.lift HasType.newest)
  have h₃ := HasType.let₁ ha hb.lift
  refine (Eqv.ax (.structural (.pairBeta a b (.bv 0))) h₁ h₂).trans ?_
  refine (Eqv.let₁ (Eqv.refl ha)
    (Eqv.ax (.structural (.letEta (Tm.lift b))) (HasType.let₁ hb.lift HasType.newest)
      hb.lift)).trans ?_
  refine Eqv.ax (.structural ?_) h₃ hb
  have beta := StructuralAxiom.letBeta (b := Tm.lift b) hpa
  rwa [instantiate_lift] at beta

theorem pairArrows_first_proof {X A B : SynCat S} {f : X ⟶ A} {g : X ⟶ B}
    (hf : IsPureMor f) (hg : IsPureMor g) :
    pairArrows f g ≫ first A B = f := by
  obtain ⟨a, ha, hpa, rfl⟩ := hf
  obtain ⟨b, hb, hpb, rfl⟩ := hg
  apply Quotient.sound
  have projection : HasType S.Instr (Ctx.nil : Ctx Empty S.Ty) (BoundCtx.nil.snoc (productObj A B).ty)
      (.let₂ (.bv 0) (.bv 1)) A.ty :=
    HasType.let₂ HasType.newest (.bv (ι := 1))
  refine (Eqv.ax (.structural (.letBeta (.pair hpa hpb)))
    (.let₁ (.pair ha hb) projection.underBinder)
    (projection.underBinder.instantiate (.pair ha hb))).trans ?_
  exact first_beta_proof ha hb hpb

theorem pairArrows_second_proof {X A B : SynCat S} {f : X ⟶ A} {g : X ⟶ B}
    (hf : IsPureMor f) (hg : IsPureMor g) :
    pairArrows f g ≫ second A B = g := by
  obtain ⟨a, ha, hpa, rfl⟩ := hf
  obtain ⟨b, hb, hpb, rfl⟩ := hg
  apply Quotient.sound
  have p := HasType.let₂ (HasType.pair ha hb) HasType.newest
  exact (Eqv.ax (.structural (.letBeta (.pair hpa hpb)))
    (.let₁ (.pair ha hb) (HasType.let₂ HasType.newest HasType.newest).underBinder) p).trans
    (second_beta_proof ha hb hpa)

theorem precomp_pairArrows_proof {X Y A B : SynCat S} {f : X ⟶ Y}
    (hf : IsPureMor f) (l : Y ⟶ A) (r : Y ⟶ B) :
    f ≫ pairArrows l r = pairArrows (f ≫ l) (f ≫ r) := by
  obtain ⟨a, ha, hpa, rfl⟩ := hf
  induction l using Syn.ind with
  | H l hl =>
      induction r using Syn.ind with
      | H r hr =>
          apply Quotient.sound
          have eq_l := Eqv.ax (.structural (StructuralAxiom.letBeta (b := Tm.underBinder l) hpa))
            (.let₁ ha hl.underBinder) (hl.underBinder.instantiate ha)
          have eq_r := Eqv.ax (.structural (StructuralAxiom.letBeta (b := Tm.underBinder r) hpa))
            (.let₁ ha hr.underBinder) (hr.underBinder.instantiate ha)
          exact (Eqv.ax (.structural (.letBeta hpa))
            (.let₁ ha (HasType.pair hl hr).underBinder)
            (.pair (hl.underBinder.instantiate ha) (hr.underBinder.instantiate ha))).trans
            (.pair eq_l.symm eq_r.symm)

theorem pairArrows_projections_proof (A B : SynCat S) :
    pairArrows (first A B) (second A B) = 𝟙 (productObj A B) := by
  apply Quotient.sound
  let P := tensor A.ty B.ty
  let β : BoundCtx S.Ty 1 := .snoc .nil P
  have x : HasType S.Instr (Ctx.nil : Ctx Empty S.Ty) β (.bv 0) P := HasType.newest
  have p : HasType S.Instr (Ctx.nil : Ctx Empty S.Ty) (.snoc (.snoc β A.ty) B.ty) (.pair (.bv 1) (.bv 0)) P :=
    .pair (.bv (ι := 1)) HasType.newest
  have projections : HasType S.Instr (Ctx.nil : Ctx Empty S.Ty) β
      (.pair (.let₂ (.bv 0) (.bv 1)) (.let₂ (.bv 0) (.bv 0))) P :=
    .pair (.let₂ x (.bv (ι := 1))) (.let₂ x HasType.newest)
  let body := Tm.underBinder
    (.pair (.let₂ (.bv 0) (.bv 1)) (.let₂ (.bv 0) (.bv 0)) : Tm Empty S.Instr 1)
  have exit : HasType S.Instr (Ctx.nil : Ctx Empty S.Ty) (.snoc β P) body P :=
    projections.underBinder
  have eta : Eqv S.pureEff Ctx.nil β
      (.let₂ (.bv 0) (.pair (.bv 1) (.bv 0))) (.bv 0) P :=
    .ax (.structural (.pairEta _)) (.let₂ x p) x
  have e₁ := Eqv.ax (.structural (StructuralAxiom.letBeta (pureEff := S.pureEff) (b := body) (a := .bv 0) .bv))
    (HasType.let₁ x exit) projections
  have e₂ := Eqv.let₁ eta (.refl exit)
  have e₃ := Eqv.ax (.sequencing (SequencingAxiom.bindLetPair (pureEff := S.pureEff) (.bv 0) (.pair (.bv 1) (.bv 0))
      body))
    (.let₁ (.let₂ x p) exit) (.let₂ x (.let₁ p exit.underBinder.underBinder))
  have e₄ := Eqv.ax (.structural (StructuralAxiom.letBeta (pureEff := S.pureEff) (b := Tm.underBinder (Tm.underBinder body))
      (a := .pair (.bv 1) (.bv 0)) (.pair .bv .bv)))
    (.let₁ p exit.underBinder.underBinder) (exit.underBinder.underBinder.instantiate p)
  have e₅ := Eqv.pair
    (first_beta_proof (A := A.ty) (B := B.ty) (.bv (β := .snoc (.snoc β A.ty) B.ty) (ι := 1))
      HasType.newest .bv)
    (second_beta_proof (A := A.ty) (B := B.ty) (.bv (β := .snoc (.snoc β A.ty) B.ty) (ι := 1))
      HasType.newest .bv)
  exact e₁.symm.trans (e₂.symm.trans (e₃.trans
    ((Eqv.let₂ (Eqv.refl x) (e₄.trans e₅)).trans eta)))

theorem pair_projections_eta_proof {n : Nat} {β : BoundCtx S.Ty n}
    {p : Tm Empty S.Instr n} {A B : S.Ty}
    (h : HasType S.Instr Ctx.nil β p (tensor A B)) (hp : Pure S.pureEff p) :
    Eqv S.pureEff Ctx.nil β (.pair (.let₂ p (.bv 1)) (.let₂ p (.bv 0))) p (tensor A B) := by
  have x : HasType S.Instr (Ctx.nil : Ctx Empty S.Ty) (.snoc .nil (tensor A B)) (.bv 0) (tensor A B) :=
    HasType.newest
  have e := Syn.eqv_of_mk_eq
    (h := HasType.pair (HasType.let₂ x HasType.previous) (HasType.let₂ x HasType.newest))
    (h' := x) (pairArrows_projections_proof (of A) (of B))
  let s : PureTypedSubst (Γ := Ctx.nil) (pureEff := S.pureEff)
      (.snoc .nil (tensor A B)) β (fun _ => p) :=
    ⟨fun i => Fin.cases h (fun j => j.elim0) i, fun _ => hp⟩
  exact e.bsubst s

theorem pairArrows_uniq_proof {X A B : SynCat S} {f : X ⟶ productObj A B}
    (hf : IsPureMor f) :
    f = pairArrows (f ≫ first A B) (f ≫ second A B) := by
  rw [← precomp_pairArrows_proof hf, pairArrows_projections_proof, Category.comp_id]

end Silmaril.Thesis.LambdaIter.Syn.SynCat

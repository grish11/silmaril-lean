module

public import Silmaril.Logic.Algebraic.OrderSorted.Representation.Defs

@[expose] public section
namespace Silmaril.Logic.Algebraic.OrderSorted.Representation
open CategoryTheory Silmaril.Logic.Institution.Examples
variable {A : Signature}

/-- Upper-cone amalgamation is equivalent to the paper's connected-component
filtration, so this construction does not strengthen the source hypothesis. -/
theorem locallyFiltered_iff_componentFiltered : LocallyFiltered A ↔ ComponentFiltered A := by
  constructor
  · intro filtered s t connected
    induction connected with
    | refl => exact ⟨s, le_refl s, le_refl s⟩
    | @step t u path edge ih =>
      obtain ⟨v, hsv, htv⟩ := ih
      rcases edge with htu | hut
      · obtain ⟨w, hvw, huw⟩ := filtered t v u htv htu
        exact ⟨w, le_trans hsv hvw, huw⟩
      · exact ⟨v, hsv, le_trans hut htv⟩
  · intro filtered s t u hst hsu
    exact filtered t u (.step (.step (.refl t) (.inr hst)) (.inl hsu))

theorem literal_coherent (L : LiteralModel A) : Coherent L.algebra where
  identity := fun _ _ => Subtype.ext rfl
  injective := by
    intro s t h x y same
    exact Subtype.ext (congrArg (fun z : L.algebra.carrier t => z.val) same)
  composition := fun _ _ _ => Subtype.ext rfl

def LiteralModel.model (L : LiteralModel A) : Model A := ⟨L.algebra, literal_coherent L⟩

theorem meets_refl (M : Model A) (x : Tagged M) : Meets M x x :=
  ⟨x.1, le_refl _, le_refl _, rfl⟩

theorem meets_symm (M : Model A) {x y : Tagged M} (h : Meets M x y) : Meets M y x := by
  obtain ⟨u, hx, hy, same⟩ := h
  exact ⟨u, hy, hx, same.symm⟩

theorem meets_trans (filtered : LocallyFiltered A) (M : Model A)
    {x y z : Tagged M} (hxy : Meets M x y) (hyz : Meets M y z) : Meets M x z := by
  obtain ⟨u, hxu, hyu, same₁⟩ := hxy
  obtain ⟨v, hyv, hzv, same₂⟩ := hyz
  obtain ⟨w, huw, hvw⟩ := filtered y.1 u v hyu hyv
  refine ⟨w, le_trans hxu huw, le_trans hzv hvw, ?_⟩
  calc
    M.algebra.coerce (le_trans hxu huw) x.2 =
        M.algebra.coerce huw (M.algebra.coerce hxu x.2) :=
      (M.coherent.composition hxu huw x.2).symm
    _ = M.algebra.coerce huw (M.algebra.coerce hyu y.2) := congrArg _ same₁
    _ = M.algebra.coerce (le_trans hyu huw) y.2 := M.coherent.composition hyu huw y.2
    _ = M.algebra.coerce hvw (M.algebra.coerce hyv y.2) :=
      (M.coherent.composition hyv hvw y.2).symm
    _ = M.algebra.coerce hvw (M.algebra.coerce hzv z.2) := congrArg _ same₂
    _ = M.algebra.coerce (le_trans hzv hvw) z.2 := M.coherent.composition hzv hvw z.2

def valueSetoid (filtered : LocallyFiltered A) (M : Model A) : Setoid (Tagged M) where
  r := Meets M
  iseqv := ⟨meets_refl M, meets_symm M, meets_trans filtered M⟩

abbrev Ambient (filtered : LocallyFiltered A) (M : Model A) := Quotient (valueSetoid filtered M)

def embed (filtered : LocallyFiltered A) (M : Model A) (s : A.base.S)
    (x : M.algebra.carrier s) : Ambient filtered M := Quotient.mk _ ⟨s, x⟩

/-- Source Lemma 4.1: each original carrier injects into the filtered colimit. -/
theorem embed_injective (filtered : LocallyFiltered A) (M : Model A) (s : A.base.S) :
    Function.Injective (embed filtered M s) := by
  intro x y same
  obtain ⟨u, hx, hy, equal⟩ := Quotient.exact same
  exact M.coherent.injective hx equal

/-- All explicit coercions become literal identities in the common ambient type. -/
theorem embed_coerce (filtered : LocallyFiltered A) (M : Model A)
    {s t : A.base.S} (h : s ≤ t) (x : M.algebra.carrier s) :
    embed filtered M t (M.algebra.coerce h x) = embed filtered M s x := by
  apply Quotient.sound
  refine ⟨t, le_refl _, h, ?_⟩
  exact M.coherent.identity t _

noncomputable def carrierEquiv (filtered : LocallyFiltered A) (M : Model A) (s : A.base.S) :
    M.algebra.carrier s ≃ Set.range (embed filtered M s) :=
  Equiv.ofInjective _ (embed_injective filtered M s)

/-- Actual literal subsets of the quotient, with transported original operations. -/
noncomputable def represent (filtered : LocallyFiltered A) (M : Model A) : LiteralModel A where
  ambient := Ambient filtered M
  carrier s := Set.range (embed filtered M s)
  inclusion := by
    intro s t h x hx
    obtain ⟨y, rfl⟩ := hx
    exact ⟨M.algebra.coerce h y, embed_coerce filtered M h y⟩
  op := fun {n w s} o args =>
    carrierEquiv filtered M s (M.algebra.op (.base o)
      (fun i => (carrierEquiv filtered M (w i)).symm (args i)))

/-- Representation preserves every operation, including explicit inclusions. -/
noncomputable def representationHom (filtered : LocallyFiltered A) (M : Model A) :
    M.algebra ⟶ (represent filtered M).algebra where
  map := fun s => carrierEquiv filtered M s
  map_op := by
    intro n w s o args
    cases o with
    | base b => simp [represent, LiteralModel.algebra]
    | inclusion lower upper h =>
      apply Subtype.ext
      change embed filtered M _ (M.algebra.op (.inclusion lower _ h) args) =
        embed filtered M lower (args 0)
      have ha : args = fun _ => args 0 := funext (fun i => congrArg args (Subsingleton.elim i 0))
      rw [ha]
      exact embed_coerce filtered M h (args 0)

/-- Each source carrier is exactly isomorphic to its literal image, including
empty carriers. This is stronger than a one-way embedding. -/
theorem representation_bijective (filtered : LocallyFiltered A) (M : Model A) (s : A.base.S) :
    Function.Bijective ((representationHom filtered M).map s) :=
  (carrierEquiv filtered M s).bijective

/-- The inverse carrier bijections also preserve all compiled operations. -/
noncomputable def representationInv (filtered : LocallyFiltered A) (M : Model A) :
    (represent filtered M).algebra ⟶ M.algebra where
  map := fun s => (carrierEquiv filtered M s).symm
  map_op := by
    intro n w s o args
    apply (carrierEquiv filtered M s).injective
    have comm := (representationHom filtered M).map_op o
      (fun i => (carrierEquiv filtered M (w i)).symm (args i))
    change (carrierEquiv filtered M s)
      ((carrierEquiv filtered M s).symm ((represent filtered M).algebra.op o args)) = _
    have ha : (fun i => (representationHom filtered M).map (w i)
        ((carrierEquiv filtered M (w i)).symm (args i))) = args := by
      funext i
      exact (carrierEquiv filtered M (w i)).apply_symm_apply (args i)
    exact ((carrierEquiv filtered M s).apply_symm_apply _).trans
      ((congrArg ((represent filtered M).algebra.op o) ha).symm.trans comm.symm)

private theorem algebraHom_ext {S : EQ.Signature} {M N : EQ.Algebra S}
    (f g : M ⟶ N) (h : f.map = g.map) : f = g := by
  cases f
  cases g
  cases h
  rfl

noncomputable def representationIso (filtered : LocallyFiltered A) (M : Model A) :
    M.algebra ≅ (represent filtered M).algebra where
  hom := representationHom filtered M
  inv := representationInv filtered M
  hom_inv_id := by
    apply algebraHom_ext
    funext s x
    exact (carrierEquiv filtered M s).symm_apply_apply x
  inv_hom_id := by
    apply algebraHom_ext
    funext s x
    exact (carrierEquiv filtered M s).apply_symm_apply x

/-- Open terms retain their original meaning, through the actual carrier
bijection, for every original variable assignment. -/
theorem eval_represent (filtered : LocallyFiltered A) (M : Model A)
    {k : Nat} {Γ : Fin k → A.base.S} {s : A.base.S}
    (t : EQ.Term (compiled A) Γ s) (ρ : ∀ i, M.algebra.carrier (Γ i)) :
    t.eval (represent filtered M).algebra
      (fun i => carrierEquiv filtered M (Γ i) (ρ i)) =
      carrierEquiv filtered M s (t.eval M.algebra ρ) := by
  induction t using @EQ.Term.rec (compiled A) k Γ with
  | var i => rfl
  | app o args ih =>
    simp only [EQ.Term.eval]
    exact (congrArg ((represent filtered M).algebra.op o) (funext ih)).trans
      ((representationHom filtered M).map_op o _).symm

/-- Exact equation satisfaction, with all original contexts retained and no
inhabitedness assumption on the carrier family. -/
theorem satisfies_represent_iff (filtered : LocallyFiltered A) (M : Model A)
    (e : Sentence A) :
    e.Holds (represent filtered M).algebra ↔ e.Holds M.algebra := by
  constructor
  · intro h ρ
    apply (carrierEquiv filtered M e.sort).injective
    rw [← eval_represent filtered M e.lhs ρ, ← eval_represent filtered M e.rhs ρ]
    exact h _
  · intro h ρ
    let source := fun i => (carrierEquiv filtered M (e.ctx i)).symm (ρ i)
    have assignments : (fun i => carrierEquiv filtered M (e.ctx i) (source i)) = ρ := by
      funext i
      exact (carrierEquiv filtered M (e.ctx i)).apply_symm_apply (ρ i)
    rw [← assignments, eval_represent, eval_represent, h source]

/-- Literal inclusion supplies all three explicit-coercion coherence laws. -/
def compileFunctor : LiteralModel A ⥤ Model A where
  obj := LiteralModel.model
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Every coherent model and every actual sorted homomorphism is represented. -/
noncomputable def representationFunctor (filtered : LocallyFiltered A) :
    Model A ⥤ LiteralModel A where
  obj := represent filtered
  map {M N} f := {
    map := fun s x => carrierEquiv filtered N s
      (f.map s ((carrierEquiv filtered M s).symm x))
    map_op := (representationInv filtered M ≫
      (show M.algebra ⟶ N.algebra from f) ≫ representationHom filtered N).map_op }
  map_id M := by
    apply algebraHom_ext
    funext s x
    exact (carrierEquiv filtered M s).apply_symm_apply x
  map_comp {M N P} f g := by
    apply algebraHom_ext
    funext s x
    change (carrierEquiv filtered P s) (g.map s (f.map s
      ((carrierEquiv filtered M s).symm x))) =
      (carrierEquiv filtered P s) (g.map s ((carrierEquiv filtered N s).symm
        ((carrierEquiv filtered N s) (f.map s ((carrierEquiv filtered M s).symm x)))))
    rw [(carrierEquiv filtered N s).symm_apply_apply]

noncomputable def modelRepresentationIso (filtered : LocallyFiltered A) (M : Model A) :
    M ≅ (represent filtered M).model where
  hom := representationHom filtered M
  inv := representationInv filtered M
  hom_inv_id := (representationIso filtered M).hom_inv_id
  inv_hom_id := (representationIso filtered M).inv_hom_id

/-- The model isomorphisms commute with every original sorted homomorphism. -/
noncomputable def representationUnit (filtered : LocallyFiltered A) :
    𝟭 (Model A) ≅ representationFunctor filtered ⋙ compileFunctor :=
  NatIso.ofComponents (modelRepresentationIso filtered) (by
    intro M N f
    apply algebraHom_ext
    funext s x
    change (carrierEquiv filtered N s) (f.map s x) =
      (carrierEquiv filtered N s) (f.map s
        ((carrierEquiv filtered M s).symm ((carrierEquiv filtered M s) x)))
    rw [(carrierEquiv filtered M s).symm_apply_apply])

noncomputable def literalRepresentationIso (filtered : LocallyFiltered A) (L : LiteralModel A) :
    represent filtered L.model ≅ L where
  hom := representationInv filtered L.model
  inv := representationHom filtered L.model
  hom_inv_id := (representationIso filtered L.model).inv_hom_id
  inv_hom_id := (representationIso filtered L.model).hom_inv_id

noncomputable def representationCounit (filtered : LocallyFiltered A) :
    compileFunctor ⋙ representationFunctor filtered ≅ 𝟭 (LiteralModel A) :=
  NatIso.ofComponents (literalRepresentationIso filtered) (by
    intro L K f
    apply algebraHom_ext
    funext s x
    change (carrierEquiv filtered K.model s).symm
      ((carrierEquiv filtered K.model s)
        (f.map s ((carrierEquiv filtered L.model s).symm x))) =
      f.map s ((carrierEquiv filtered L.model s).symm x)
    exact (carrierEquiv filtered K.model s).symm_apply_apply _)

/-- Non-overloaded instance of the source reduction relationship: literal
subset models and coherent explicit-coercion models are equivalent categories.
All sorted homomorphisms and empty carriers are retained. -/
noncomputable def representationEquivalence (filtered : LocallyFiltered A) :
    Model A ≌ LiteralModel A where
  functor := representationFunctor filtered
  inverse := compileFunctor
  unitIso := representationUnit filtered
  counitIso := representationCounit filtered
  functor_unitIso_comp M := by
    apply algebraHom_ext
    funext s x
    change (carrierEquiv filtered ((represent filtered M).model) s).symm
      ((carrierEquiv filtered ((represent filtered M).model) s)
        ((carrierEquiv filtered M s)
          ((carrierEquiv filtered M s).symm x))) = x
    exact ((carrierEquiv filtered ((represent filtered M).model) s).symm_apply_apply _).trans
      ((carrierEquiv filtered M s).apply_symm_apply x)

/-- A theory has a coherent model exactly when it has a literal-subset model.
Representation preserves every equation in an arbitrary theory at once. -/
theorem theory_satisfiable_iff (filtered : LocallyFiltered A) (H : Set (Sentence A)) :
    (∃ M : Model A, ∀ e ∈ H, e.Holds M.algebra) ↔
      ∃ L : LiteralModel A, ∀ e ∈ H, e.Holds L.algebra := by
  constructor
  · rintro ⟨M, h⟩
    exact ⟨represent filtered M, fun e he => (satisfies_represent_iff filtered M e).mpr (h e he)⟩
  · rintro ⟨L, h⟩
    exact ⟨L.model, h⟩

/-- Exact arbitrary-theory semantic consequence in both presentations. -/
theorem theory_entails_iff (filtered : LocallyFiltered A) (H : Set (Sentence A)) (e : Sentence A) :
    (∀ M : Model A, (∀ h ∈ H, h.Holds M.algebra) → e.Holds M.algebra) ↔
      ∀ L : LiteralModel A, (∀ h ∈ H, h.Holds L.algebra) → e.Holds L.algebra := by
  constructor
  · intro consequence L assumptions
    exact consequence L.model assumptions
  · intro consequence M assumptions
    apply (satisfies_represent_iff filtered M e).mp
    exact consequence (represent filtered M)
      (fun h hh => (satisfies_represent_iff filtered M h).mpr (assumptions h hh))

end Silmaril.Logic.Algebraic.OrderSorted.Representation

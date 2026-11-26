module

public import Silmaril.SSA.Isotope.LetCase.HandledTrace.Category.Tensor.Premonoidal.Defs

public section

namespace Silmaril.Isotope.LetCase.HandledTrace.PremonoidalProofs

open LocallyNameless Silmaril.Isotope.Semantics Silmaril.Elgot.ITree

universe u v e w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {D : τ → Type (e + 1)} [ProductModel D] [UnitModel D] [CoproductModel D] [EmptyModel D]
  {Events : Type e → Type e} {M : InstructionModel D Φ (Tree Events)}
  {ε : Type w} [HasEff Φ ε] [Bot ε] {A B : τ}

private theorem denote_pure {n : Nat} {ctx : BoundCtx τ n} {t : Tm Empty Φ n}
    (d : Derivation Φ Ctx.nil ctx t A) (compatible : M.RespectsPure (ε := ε))
    (written : Pure (⊥ : ε) t) (env : BoundEnv D ctx) :
    ∃ a, d.denote D M (fun x => Empty.elim x) env = pure a := by
  induction d with
  | fv | bv | unit => exact ⟨_, rfl⟩
  | @op _ _ f _ _ ih =>
    cases written with
    | op hf ha =>
      obtain ⟨a, ha'⟩ := ih ha env
      obtain ⟨value, eval⟩ := compatible f hf
      exact ⟨value a, by simp only [Derivation.denote, ha', pure_bind, eval]⟩
  | let₁ _ _ producer body =>
    cases written with
    | let₁ hp hb =>
      obtain ⟨a, ha⟩ := producer hp env
      obtain ⟨b, hb⟩ := body hb (env.snoc a)
      exact ⟨b, by simp only [Derivation.denote, ha, pure_bind, hb]⟩
  | pair _ _ left right =>
    cases written with
    | pair hl hr =>
      obtain ⟨a, ha⟩ := left hl env
      obtain ⟨b, hb⟩ := right hr env
      refine ⟨(ProductModel.productEquiv _ _).symm (a, b), ?_⟩
      simp only [Derivation.denote, ha, hb, pure_bind]
  | let₂ _ _ producer body =>
    cases written with
    | let₂ hp hb =>
      obtain ⟨packet, seen⟩ := producer hp env
      let values := ProductModel.productEquiv (D := D) _ _ packet
      obtain ⟨c, hc⟩ := body hb ((env.snoc values.1).snoc values.2)
      refine ⟨c, ?_⟩
      simpa only [Derivation.denote, seen, pure_bind] using hc
  | inl _ ih =>
    cases written with
    | inl hp =>
      obtain ⟨a, ha⟩ := ih hp env
      refine ⟨(CoproductModel.coprodEquiv _ _).symm (.inl a), ?_⟩
      simp only [Derivation.denote, ha, pure_bind]
  | inr _ ih =>
    cases written with
    | inr hp =>
      obtain ⟨b, hb⟩ := ih hp env
      refine ⟨(CoproductModel.coprodEquiv _ _).symm (.inr b), ?_⟩
      simp only [Derivation.denote, hb, pure_bind]
  | case _ _ _ scrutinee left right =>
    cases written with
    | case hs hl hr =>
      obtain ⟨value, seen⟩ := scrutinee hs env
      simp only [Derivation.denote, seen, pure_bind]
      cases CoproductModel.coprodEquiv (D := D) _ _ value with
      | inl a => exact left hl (env.snoc a)
      | inr b => exact right hr (env.snoc b)
  | abort _ ih =>
    cases written with
    | abort h =>
      obtain ⟨zero, _⟩ := ih h env
      exact ((EmptyModel.emptyEquiv (D := D)) zero).elim

theorem pureRun_of_pure {p : Program Φ A B} (compatible : M.RespectsPure (ε := ε))
    (written : Pure (⊥ : ε) p.1) : p.HasPureRun M := by
  have returns (a : D A) : ∃ b, p.run M a = pure b :=
    denote_pure p.2 compatible written (BoundEnv.snoc (β := .nil) (fun i => i.elim0) a)
  choose value runs using returns
  exact ⟨value, runs⟩

end Silmaril.Isotope.LetCase.HandledTrace.PremonoidalProofs

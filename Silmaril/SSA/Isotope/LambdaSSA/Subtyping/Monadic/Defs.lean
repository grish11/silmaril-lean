module

public import Silmaril.SSA.Isotope.LambdaSSA.Subtyping.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Kleisli.Thms

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

/-! # Direct monadic semantics of proof-relevant λSSA -/

namespace Silmaril.Isotope.LambdaSSA.Subtyping.Semantics.Monadic

open Silmaril.Elgot

open Silmaril.Isotope.LetIter.ProofRelevant.Semantics

universe u v q r

variable {τ : Type u} [TypeFormers τ] [Silmaril.Isotope.Subtyping τ] [TypeModel.{u, v} τ]
variable {Φ : Type q} [HasTy Φ τ] {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m] [InstructionModel Φ τ ε m]

abbrev Env {τ : Type u} [TypeFormers τ] [Silmaril.Isotope.Subtyping τ]
    [TypeModel.{u, v} τ] (Γ : VCtx τ) : Type v :=
  @LambdaSSA.Semantics.Monadic.Env τ _ _ _ Γ

/-- Direct call-by-value semantics.  The `.sub` equation applies the coercion
selected by that particular subtype witness, so the definition does not
silently assume proof irrelevance. -/
def denote : {Γ : VCtx τ} → {t : LambdaSSA.Tm Φ} → {A : τ} →
    Tm.HasType Γ t A → Env Γ → m (TyDen A)
  | _, _, _, .var h, ρ => pure (LambdaSSA.Semantics.Monadic.Env.get ρ _ h)
  | _, _, _, .op h, ρ => denote h ρ >>=
      InstructionModel.denote (Φ := Φ) (τ := τ) (ε := ε) (m := m) _
  | _, _, _, .let₁ ha hb, ρ => denote ha ρ >>= fun a => denote hb (ρ, a)
  | _, _, _, .pair ha hb, ρ =>
      denote ha ρ >>= fun a => denote hb ρ >>= fun b =>
        pure ((TypeModel.productEquiv _ _).symm (a, b))
  | _, _, _, .unit, _ => pure (TypeModel.unitEquiv.symm ())
  | _, _, _, .let₂ ha hb, ρ => denote ha ρ >>= fun ab =>
      let p := TypeModel.productEquiv _ _ ab
      denote hb ((ρ, p.1), p.2)
  | _, _, _, .inl ha, ρ => denote ha ρ >>= fun a =>
      pure ((TypeModel.coprodEquiv _ _).symm (.inl a))
  | _, _, _, .inr hb, ρ => denote hb ρ >>= fun b =>
      pure ((TypeModel.coprodEquiv _ _).symm (.inr b))
  | _, _, _, .case he hl hr, ρ => denote he ρ >>= fun e =>
      match TypeModel.coprodEquiv _ _ e with
      | .inl a => denote hl (ρ, a)
      | .inr b => denote hr (ρ, b)
  | _, _, _, .abort ha, ρ => denote ha ρ >>= fun z =>
      Empty.elim (TypeModel.emptyEquiv z)
  | _, _, _, .sub ha d, ρ => denote ha ρ >>= fun a => pure (coeSub d a)

/-- Graph of the direct proof-relevant term denotation. -/
inductive Denotes (ε : Type r) [HasEff Φ ε] [Bot ε] [InstructionModel Φ τ ε m] :
    {Γ : VCtx τ} → {t : LambdaSSA.Tm Φ} → {A : τ} →
    Tm.HasType Γ t A → (Env Γ → m (TyDen A)) → Prop where
  | var (h : At Γ i A) : Denotes ε (.var h) (fun ρ => pure
      (LambdaSSA.Semantics.Monadic.Env.get ρ i h))
  | op (h : Denotes ε ha fa) : Denotes ε (.op ha) (fun ρ => fa ρ >>=
      InstructionModel.denote (Φ := Φ) (τ := τ) (ε := ε) (m := m) _)
  | let₁ (ha : Denotes ε h₁ f) (hb : Denotes ε h₂ g) :
      Denotes ε (.let₁ h₁ h₂) (fun ρ => f ρ >>= fun a => g (ρ, a))
  | pair (ha : Denotes ε h₁ f) (hb : Denotes ε h₂ g) :
      Denotes ε (.pair h₁ h₂) (fun ρ => f ρ >>= fun a => g ρ >>= fun b =>
        pure ((TypeModel.productEquiv _ _).symm (a, b)))
  | unit : Denotes ε (.unit (Γ := Γ)) (fun _ => pure (TypeModel.unitEquiv.symm ()))
  | let₂ (ha : Denotes ε h₁ f) (hb : Denotes ε h₂ g) :
      Denotes ε (.let₂ h₁ h₂) (fun ρ => f ρ >>= fun ab =>
        let p := TypeModel.productEquiv _ _ ab; g ((ρ, p.1), p.2))
  | inl (h : Denotes ε ha f) : Denotes ε (.inl (B := B) ha) (fun ρ =>
      f ρ >>= fun a => pure ((TypeModel.coprodEquiv _ _).symm (.inl a)))
  | inr (h : Denotes ε hb f) : Denotes ε (.inr (A := A) hb) (fun ρ =>
      f ρ >>= fun b => pure ((TypeModel.coprodEquiv _ _).symm (.inr b)))
  | case {A B C : τ} {h : Tm.HasType Γ e (coprod A B)}
      {h₁ : Tm.HasType (A :: Γ) left C} {h₂ : Tm.HasType (B :: Γ) right C}
      {f : Env Γ → m (TyDen (coprod A B))}
      {l : Env (A :: Γ) → m (TyDen C)} {r : Env (B :: Γ) → m (TyDen C)}
      (he : Denotes ε h f) (hl : Denotes ε h₁ l) (hr : Denotes ε h₂ r) :
      Denotes ε (.case h h₁ h₂) (fun ρ => f ρ >>= fun value =>
        match TypeModel.coprodEquiv A B value with
        | .inl a => l (ρ, a) | .inr b => r (ρ, b))
  | abort (h : Denotes ε ha f) : Denotes ε (.abort (A := A) ha) (fun ρ =>
      f ρ >>= fun z => Empty.elim (TypeModel.emptyEquiv z))
  | sub {A B : τ} {ha : Tm.HasType Γ a A} {f : Env Γ → m (TyDen A)}
      (h : Denotes ε ha f) (d : Subty A B) : Denotes ε (.sub ha d) (fun ρ =>
        f ρ >>= fun value => pure (coeSub d value))

omit [LawfulMonad m] in
@[simp] theorem denote_sub {Γ : VCtx τ} {t : LambdaSSA.Tm Φ} {A B : τ}
    (h : Tm.HasType Γ t A) (d : Subty A B) (ρ : Env Γ) :
    denote (ε := ε) (m := m) (.sub h d) ρ =
      (denote (ε := ε) (m := m) h ρ >>= fun a => pure (coeSub d a)) := rfl

section Region

variable [Iterate m] [LawfulElgotMonad m]

abbrev LabelDen {τ : Type u} [TypeFormers τ] [Silmaril.Isotope.Subtyping τ]
    [TypeModel.{u, v} τ] (L : LCtx τ) : Type v :=
  @LambdaSSA.Semantics.Monadic.LabelDen τ _ _ _ L

/-- The collective block graph is representation-independent: subtyping is
carried by each block's proof-relevant term premises, while collective dispatch
only packages their already interpreted functions. -/
abbrev CollectiveDenotes := @LambdaSSA.Semantics.Monadic.CollectiveDenotes

/-- Structural graph of the direct proof-relevant region interpretation.  The
CFG clause records the canonical dependent finite-label dispatcher used by
`denoteRegion`, while its premises expose every block interpretation. -/
inductive RegionDenotes (ε : Type r) [HasEff Φ ε] [Bot ε]
    [InstructionModel Φ τ ε m] :
    {Γ : VCtx τ} → {region : LambdaSSA.Region Φ} → {L : LCtx τ} →
    Region.HasType Γ region L → (Env Γ → m (LabelDen L)) → Prop where
  | br (dt : Denotes ε ha fa) :
      RegionDenotes ε (.br h ha) (fun ρ => fa ρ >>= fun a =>
        pure (LambdaSSA.Semantics.Monadic.labelInject _ h a))
  | case {Γ : VCtx τ} {L : LCtx τ} {A B : τ} {a : LambdaSSA.Tm Φ}
      {l r : LambdaSSA.Region Φ}
      {he : Tm.HasType Γ a (Silmaril.coprod A B)}
      {hl : Region.HasType (A :: Γ) l L}
      {hr : Region.HasType (B :: Γ) r L}
      {fe : Env Γ → m (TyDen (Silmaril.coprod A B))}
      {fl : Env (A :: Γ) → m (LabelDen L)}
      {fr : Env (B :: Γ) → m (LabelDen L)}
      (de : Denotes ε he fe)
      (dl : RegionDenotes ε hl fl) (dr : RegionDenotes ε hr fr) :
      RegionDenotes ε (.case he hl hr) (fun ρ => fe ρ >>= fun e =>
        match TypeModel.coprodEquiv A B e with
        | .inl a => fl (ρ, a)
        | .inr b => fr (ρ, b))
  | let₁ (da : Denotes ε ha fa) (db : RegionDenotes ε hb fb) :
      RegionDenotes ε (.let₁ ha hb) (fun ρ => fa ρ >>= fun a => fb (ρ, a))
  | let₂ (da : Denotes ε ha fa) (db : RegionDenotes ε hb fb) :
      RegionDenotes ε (.let₂ ha hb) (fun ρ => fa ρ >>= fun ab =>
        let p := TypeModel.productEquiv _ _ ab
        fb ((ρ, p.1), p.2))
  | cfgZero {R : Fin 0 → τ} {Γ : VCtx τ} {L : LCtx τ}
      {entry : LambdaSSA.Region Φ} {blocks : Fin 0 → LambdaSSA.Region Φ}
      (he : Region.HasType Γ entry (List.ofFn R ++ L))
      (hb : ∀ i, Region.HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L))
      {fe : Env Γ → m (LabelDen L)} (de : RegionDenotes ε he fe) :
      RegionDenotes ε (.cfg R he hb) fe
  | cfg {n : Nat} {R : Fin (n + 1) → τ} {Γ : VCtx τ} {L : LCtx τ}
      {entry : LambdaSSA.Region Φ} {blocks : Fin (n + 1) → LambdaSSA.Region Φ}
      (he : Region.HasType Γ entry (List.ofFn R ++ L))
      (hb : ∀ i, Region.HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L))
      {fe : Env Γ → m (LabelDen (List.ofFn R ++ L))}
      {fb : ∀ i, Env (R i :: Γ) → m (LabelDen (List.ofFn R ++ L))}
      {collective : Env Γ × LambdaSSA.Semantics.Monadic.FiniteLabelDen R →
        m (LabelDen (List.ofFn R ++ L))}
      (de : RegionDenotes ε he fe) (db : ∀ i, RegionDenotes ε (hb i) (fb i))
      (dc : CollectiveDenotes Γ R L fb collective) :
      RegionDenotes ε (.cfg R he hb)
        (LambdaSSA.Semantics.Monadic.cfgDenotation fe collective)

end Region

end Silmaril.Isotope.LambdaSSA.Subtyping.Semantics.Monadic

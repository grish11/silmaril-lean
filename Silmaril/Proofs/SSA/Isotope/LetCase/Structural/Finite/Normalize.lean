module

public import Silmaril.SSA.Isotope.LetCase.Structural.Finite.Defs
import Silmaril.Proofs.SSA.Isotope.LetCase.Structural.Finite.Substitution
import Silmaril.SSA.Isotope.LetCase.Categorical.Defs

public section

namespace Silmaril.Isotope.LetCase.Structural.Finite

open LocallyNameless (Derivation Equiv HasType Tm)
open Reply (Γ₀)
open scoped Silmaril.Isotope.LetCase.Structural.Finite LetSeq.StraightLine.Structural

variable {Φ : Type} [Signature Φ]
set_option backward.isDefEq.respectTransparency false

private theorem prepend_eq {A : Types} {t u : Term Φ 0}
    (eq : Equiv false Γ₀ .nil t u A) (hu : Normalizes A u) : Normalizes A t := by
  obtain ⟨v, h, replay⟩ := hu
  exact ⟨v, h, eq.trans replay⟩

private theorem normal_value {A : Types} (a : Constructor A) : Normalizes A (a.term (Φ := Φ)) :=
  ⟨_, .ret a, .refl a.typing.toHasType⟩

private theorem no_empty_head {t : Term Φ 0} (p : Head .empty t) : False := by
  induction p with
  | ret v => cases v
  | request f _ _ _ _ _ ih => exact ih ((Signature.target f).witness)

theorem bind_replay_proof {A B : Types} {t : Term Φ 0} {k : Term Φ 1}
    (p : Head A t) (dk : HasType Φ Γ₀ (.snoc .nil A) k B)
    (cont : ∀ x : Constructor A, Normalizes B (Tm.instantiate k x.term)) :
    Normalizes B (.let₁ t k) := by
  induction p with
  | ret v => exact prepend_eq (Equiv.letBeta v.pure v.typing.toHasType dk) (cont v)
  | @request f arg body typed next heads replay ih =>
    have finish (x : Constructor (instrTrg f)) :
        Normalizes B (Tm.instantiate (.let₁ body k.underBinder) x.term) := by
      change Normalizes B (.let₁ (Tm.instantiate body x.term)
        (k.underBinder.bsubst (Tm.upSub (Fin.cases (x.term : Term Φ 0) fun i => .bv i))))
      rw [open_underBinder]
      exact prepend_eq (.let₁ (replay x) (.refl dk)) (ih x)
    choose next' heads' replay' using finish
    obtain ⟨weakened⟩ := Derivation.ofHasType (dk.underBinder (X := instrTrg f))
    exact ⟨_, .request f arg (.let₁ typed weakened) next' heads' replay',
      Equiv.bindLet (.op arg.typing.toHasType) typed.toHasType dk⟩

private theorem request_head (f : Φ) (a : Constructor (instrSrc f)) :
    Normalizes (instrTrg (τ := Types) f) (.op f a.term) := by
  refine ⟨_, .request f a (.bv (ι := 0)) (fun x => x.term) (fun x => .ret x) ?_,
    (Equiv.letEta (.op a.typing.toHasType)).symm⟩
  intro x
  exact .refl x.typing.toHasType

private theorem split_argument {t : Term Φ 0} (f : Φ)
    (ht : HasType Φ Γ₀ .nil t (instrSrc (τ := Types) f)) :
    Equiv false Γ₀ .nil (.op f t) (.let₁ t (.op f (.bv 0))) (instrTrg (τ := Types) f) := by
  have slot : HasType Φ Γ₀ (.snoc .nil (instrSrc f)) (.bv 0) (instrSrc f) :=
    HasType.bv (β := (BoundCtx.nil.snoc (instrSrc (τ := Types) f))) (ι := 0)
  have bt : HasType Φ Γ₀ (.snoc .nil (instrSrc f)) (.op f (.bv 0)) (instrTrg f) := .op slot
  have split := (Equiv.letEta (pureEff := false) (HasType.op (f := f) ht)).symm.trans
    (Equiv.bindOp ht (HasType.bv (ι := 0)))
  exact split.trans (.let₁ (.refl ht) (Equiv.letEta bt))

private theorem normalize_pair {A B : Types} {l r : Term Φ 0}
    (left : Head A l) (right : Head B r) : Normalizes (.product A B) (.pair l r) := by
  have hl := left.typing.toHasType
  have hr := right.typing.toHasType
  have pairVars : HasType Φ Γ₀ ((BoundCtx.nil.snoc A).snoc B) (.pair (.bv 1) (.bv 0)) (.product A B) :=
    .pair .bv .bv
  apply prepend_eq ((Equiv.pairEta (pureEff := false) (.pair hl hr)).symm.trans
    (Equiv.pairBeta hl hr pairVars))
  apply bind_replay_proof left (.let₁ hr.lift pairVars)
  intro a
  change Normalizes (.product A B) (.let₁ (Tm.instantiate r.lift a.term) (.pair a.term.lift (.bv 0)))
  rw [open_lift]
  have body : HasType Φ Γ₀ (.snoc .nil B) (.pair a.term.lift (.bv 0)) (.product A B) :=
    .pair a.typing.toHasType.lift .bv
  apply bind_replay_proof right body
  intro b
  change Normalizes (.product A B) (.pair (Tm.instantiate a.term.lift b.term) b.term)
  rw [open_lift]
  exact normal_value (.pair a b)

private theorem normalize_inl {A B : Types} {t : Term Φ 0}
    (p : Head A t) : Normalizes (.coprod A B) (.inl t) := by
  have l : HasType Φ Γ₀ (.snoc .nil A) (.inl (.bv 0)) (.coprod A B) := .inl .bv
  have r : HasType Φ Γ₀ (.snoc .nil B) (.inr (.bv 0)) (.coprod A B) := .inr .bv
  have inj : HasType Φ Γ₀ .nil (.inl t) (.coprod A B) := .inl p.typing.toHasType
  apply prepend_eq ((Equiv.caseEta (pureEff := false) inj).symm.trans
    (Equiv.caseBetaL p.typing.toHasType l r))
  apply bind_replay_proof p l
  intro x
  exact normal_value (.inl x)

private theorem normalize_inr {A B : Types} {t : Term Φ 0}
    (p : Head B t) : Normalizes (.coprod A B) (.inr t) := by
  have l : HasType Φ Γ₀ (.snoc .nil A) (.inl (.bv 0)) (.coprod A B) := .inl .bv
  have r : HasType Φ Γ₀ (.snoc .nil B) (.inr (.bv 0)) (.coprod A B) := .inr .bv
  have inj : HasType Φ Γ₀ .nil (.inr t) (.coprod A B) := .inr p.typing.toHasType
  apply prepend_eq ((Equiv.caseEta (pureEff := false) inj).symm.trans
    (Equiv.caseBetaR p.typing.toHasType l r))
  apply bind_replay_proof p r
  intro x
  exact normal_value (.inr x)

/-- Evaluate the constructive inputs by induction on the exact native typing.
An empty scrutinee has no head since every request has a constructor reply. -/
theorem normalize_proof {n : Nat} {β : Context n} {t : Term Φ n} {A : Types}
    (d : Derivation Φ Γ₀ β t A) (ρ : Assignment β) :
    Normalizes A (t.bsubst ρ.terms) := by
  induction d with
  | @fv _ _ x _ _ => exact x.elim
  | bv => exact normal_value (ρ _)
  | unit => exact normal_value .unit
  | @op _ _ f t arg ih =>
    obtain ⟨u, p, hu⟩ := ih ρ
    apply prepend_eq (Equiv.op hu)
    apply prepend_eq (split_argument f p.typing.toHasType)
    apply bind_replay_proof p (HasType.op (f := f) (HasType.bv (ι := 0)))
    exact request_head f
  | @let₁ _ _ t k A B a b iha ihb =>
    obtain ⟨u, p, hu⟩ := iha ρ
    have body : HasType Φ Γ₀ (.snoc .nil A) (k.bsubst (Tm.upSub ρ.terms)) B :=
      b.toHasType.bsubst ((ρ.typed (Φ := Φ)).up A)
    apply prepend_eq (Equiv.let₁ hu (.refl body))
    apply bind_replay_proof p body
    intro x
    rw [Assignment.instantiate]
    exact ihb (ρ.snoc x)
  | @let₂ _ _ t k A B D a b iha ihb =>
    obtain ⟨u, p, hu⟩ := iha ρ
    let body := k.bsubst (Tm.upSub (Tm.upSub ρ.terms))
    have hb : HasType Φ Γ₀ ((BoundCtx.nil.snoc A).snoc B) body D :=
      b.toHasType.bsubst (((ρ.typed (Φ := Φ)).up A).up B)
    apply prepend_eq ((Equiv.let₂ hu (.refl hb)).trans (Equiv.bindPair p.typing.toHasType hb))
    apply bind_replay_proof p (HasType.let₂ .bv hb.underTwoBinders)
    intro x
    cases x with
    | pair l r =>
      change Normalizes D (.let₂ (.pair l.term r.term)
        (body.underTwoBinders.bsubst (Tm.upSub (Tm.upSub (Fin.cases
          (Tm.pair l.term r.term : Term Φ 0) (fun i => .bv i))))))
      rw [open_underTwoBinders]
      exact prepend_eq (replay_constructor_pair ρ l r b.toHasType) (ihb ((ρ.snoc l).snoc r))
  | pair a b iha ihb =>
    obtain ⟨u, left, hu⟩ := iha ρ
    obtain ⟨v, right, hv⟩ := ihb ρ
    exact prepend_eq (.pair hu hv) (normalize_pair left right)
  | inl a ih =>
    obtain ⟨u, p, hu⟩ := ih ρ
    exact prepend_eq (.inl hu) (normalize_inl p)
  | inr a ih =>
    obtain ⟨u, p, hu⟩ := ih ρ
    exact prepend_eq (.inr hu) (normalize_inr p)
  | @case _ _ e l r A B D scr dl dr ih ihl ihr =>
    obtain ⟨u, p, hu⟩ := ih ρ
    let l' := l.bsubst (Tm.upSub ρ.terms)
    let r' := r.bsubst (Tm.upSub ρ.terms)
    have hl : HasType Φ Γ₀ (.snoc .nil A) l' D := dl.toHasType.bsubst ((ρ.typed (Φ := Φ)).up A)
    have hr : HasType Φ Γ₀ (.snoc .nil B) r' D := dr.toHasType.bsubst ((ρ.typed (Φ := Φ)).up B)
    apply prepend_eq ((Equiv.case hu (.refl hl) (.refl hr)).trans (Equiv.bindCase p.typing.toHasType hl hr))
    apply bind_replay_proof p (HasType.case .bv hl.underBinder hr.underBinder)
    intro x
    change Normalizes D (.case x.term
      (l'.underBinder.bsubst (Tm.upSub (Fin.cases x.term (fun i => .bv i))))
      (r'.underBinder.bsubst (Tm.upSub (Fin.cases x.term (fun i => .bv i)))))
    rw [open_underBinder, open_underBinder]
    cases x with
    | inl a =>
      have beta := Equiv.letBeta (pureEff := false) a.pure a.typing.toHasType hl
      change Equiv false Γ₀ .nil _ (Tm.instantiate (l.bsubst (Tm.upSub ρ.terms)) a.term) _ at beta
      rw [Assignment.instantiate] at beta
      exact prepend_eq ((Equiv.caseBetaL a.typing.toHasType hl hr).trans beta) (ihl (ρ.snoc a))
    | inr b =>
      have beta := Equiv.letBeta (pureEff := false) b.pure b.typing.toHasType hr
      change Equiv false Γ₀ .nil _ (Tm.instantiate (r.bsubst (Tm.upSub ρ.terms)) b.term) _ at beta
      rw [Assignment.instantiate] at beta
      exact prepend_eq ((Equiv.caseBetaR b.typing.toHasType hl hr).trans beta) (ihr (ρ.snoc b))
  | abort a ih =>
    obtain ⟨_, p, _⟩ := ih ρ
    exact (no_empty_head p).elim

end Silmaril.Isotope.LetCase.Structural.Finite

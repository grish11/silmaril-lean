module

public import Silmaril.SSA.Isotope.LetSeq.StraightLine.Structural.Defs
import Silmaril.Proofs.SSA.Isotope.LetSeq.StraightLine.Structural.Replay

import Silmaril.SSA.Isotope.LetSeq.StraightLine.Binders.Thms

public section

namespace Silmaril.Isotope.LetSeq.StraightLine.Structural

open LocallyNameless (Derivation Equiv HasType Tm)
open scoped Structural

variable {α Φ : Type} [Signature α Φ]
open Binders

set_option backward.isDefEq.respectTransparency false

private theorem normalized_of_equiv {n : Nat} {β : Context α n} {t u : Term Φ n} {A : Ty α}
    (h : Equiv false Γ₀ β t u A) (hu : Normalizes β u A) : Normalizes β t A := by
  obtain ⟨v, w, replay⟩ := hu
  exact ⟨v, w, h.trans replay⟩

private theorem bind_normalizes {n : Nat} {β : Context α n} {t : Term Φ n}
    {k : Term Φ (n + 1)} {A B : Ty α} (p : Normal β t A)
    (dk : HasType Φ Γ₀ (β.snoc A) k B)
    (cont : ∀ {m : Nat} {γ : Context α m} (ρ : BoundCtx.Renaming β γ) (v : Assembly γ A),
      Normalizes γ (Tm.instantiate (k.rename (Tm.up ρ.toFun)) v.term) B) :
    Normalizes β (.let₁ t k) B := by
  induction p with
  | ret v =>
    have next := cont (BoundCtx.Renaming.id _) v
    simp only [BoundCtx.Renaming.id, Tm.up_id, Tm.rename_id] at next
    exact normalized_of_equiv (Equiv.letBeta v.pure v.derivation.toHasType dk) next
  | @request _ β A f a body rest ih =>
    let split := (replyUnpack β f).split
    let shift := (BoundCtx.Renaming.succ β (instrTrg f)).comp split.rename
    have moved : ∀ {m : Nat} {γ : Context α m}
        (ρ : BoundCtx.Renaming (replyUnpack β f).context γ) (v : Assembly γ A),
        Normalizes γ (Tm.instantiate
          ((k.underBinder.rename (Tm.up split.rename.toFun)).rename (Tm.up ρ.toFun)) v.term) B := by
      intro m γ ρ v
      change Normalizes γ (Tm.instantiate
        (((k.rename (Tm.up Fin.succ)).rename (Tm.up split.rename.toFun)).rename (Tm.up ρ.toFun)) v.term) B
      rw [Tm.rename_comp, ← Tm.up_comp, Tm.rename_comp, ← Tm.up_comp]
      exact cont (shift.comp ρ) v
    obtain ⟨u, normal, replay⟩ := ih (dk.underBinder.rename (split.rename.up A)) moved
    have call := HasType.op (f := f) a.derivation.toHasType
    have commute := Equiv.bindLet (pureEff := false) call (split.derivation rest.derivation).toHasType dk
    have across := split.bind rest.derivation dk.underBinder
    exact ⟨_, .request f a normal, commute.trans (.let₁ (.refl call) (across.trans (split.congr replay)))⟩

omit [Signature α Φ] in
private theorem rename_substituted {n m k : Nat} {source : Context α n} {target : Context α m}
    {γ : Context α k} (σ : AssemblyEnv source target) (ρ : BoundCtx.Renaming target γ)
    (t : Term Φ n) :
    (t.bsubst σ.terms).rename ρ.toFun = t.bsubst (σ.rename ρ).terms := by
  rw [Tm.rename_bsubst]
  exact Tm.bsubst_congr (fun i => (Assembly.term_rename ρ (σ i)).symm) t

omit [Signature α Φ] in
private theorem rename_open_assembly {n m k : Nat} {source : Context α n}
    {target : Context α m} {γ : Context α k}
    (σ : AssemblyEnv source target) (ρ : BoundCtx.Renaming target γ)
    (body : Term Φ (n + 1)) :
    (body.bsubst (Tm.upSub σ.terms)).rename (Tm.up ρ.toFun) =
      body.bsubst (Tm.upSub (AssemblyEnv.terms (fun i => (σ i).rename ρ))) := by
  rw [rename_open_substitution]
  congr 2
  exact funext fun i => (Assembly.term_rename (Φ := Φ) ρ (σ i)).symm

omit [Signature α Φ] in
private theorem rename_open_pair_assembly {n m k : Nat} {source : Context α n}
    {target : Context α m} {γ : Context α k}
    (σ : AssemblyEnv source target) (ρ : BoundCtx.Renaming target γ)
    (body : Term Φ (n + 2)) :
    (body.bsubst (Tm.upSub (Tm.upSub σ.terms))).rename (Tm.up (Tm.up ρ.toFun)) =
      body.bsubst (Tm.upSub (Tm.upSub (AssemblyEnv.terms (fun i => (σ i).rename ρ)))) := by
  rw [rename_open_substitution]
  congr 1
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  simp only [Tm.upSub_succ]
  apply congrArg Tm.lift
  refine Fin.cases rfl (fun j => ?_) j
  simp only [Tm.upSub_succ, Tm.rename_lift]
  exact congrArg Tm.lift (Assembly.term_rename (Φ := Φ) ρ (σ j)).symm

private theorem request_normalizes {n : Nat} {β : Context α n} (f : Φ) (a : Assembly β (instrSrc f)) :
    Normalizes β (.op f a.term) (instrTrg f) := by
  have call := HasType.op (f := f) a.derivation.toHasType
  have eta := unpack_eta (Φ := Φ) (Signature.reply (α := α) f) (β := β.snoc (instrTrg f)) ⟨0, rfl⟩
  exact ⟨_, .request f a (.ret (replyUnpack β f).value),
    (Equiv.letEta call).symm.trans (.let₁ (.refl call) eta)⟩

/-- Every exact native derivation normalizes after assigning assemblies to
its input variables. The proof follows the native constructors. -/
theorem normalize_exact_proof {n m : Nat} {source : Context α n} {target : Context α m}
    {t : Term Φ n} {A : Ty α} (d : Derivation Φ Γ₀ source t A) (σ : AssemblyEnv source target) :
    Normalizes target (t.bsubst σ.terms) A := by
  induction d generalizing m with
  | @fv _ _ x _ _ => exact x.elim
  | bv => exact ⟨_, .ret (σ _), .refl (σ _).derivation.toHasType⟩
  | unit => exact ⟨_, .ret .unit, .unit⟩
  | @op _ _ f a arg iha =>
    obtain ⟨u, norm, replay⟩ := iha σ
    have k : HasType Φ Γ₀ (target.snoc (instrSrc f)) (.op f (.bv 0)) (instrTrg f) := .op .bv
    apply normalized_of_equiv (Equiv.op (f := f) replay)
    have split := (Equiv.letEta (pureEff := false) (HasType.op (f := f) norm.derivation.toHasType)).symm.trans
      (Equiv.bindOp norm.derivation.toHasType (HasType.bv (i := 0)))
    apply normalized_of_equiv (split.trans (.let₁ (.refl norm.derivation.toHasType) (Equiv.letEta k)))
    apply bind_normalizes norm k
    intro _ γ ρ v
    exact request_normalizes f v
  | @let₁ _ _ a b A B da db iha ihb =>
    obtain ⟨u, norm, replay⟩ := iha σ
    have body := db.toHasType.bsubst ((σ.typed (Φ := Φ)).up A)
    apply normalized_of_equiv (.let₁ replay (.refl body))
    apply bind_normalizes norm body
    intro _ γ ρ v
    rw [rename_open_assembly, instantiate_assembly]
    exact ihb ((σ.rename ρ).extend v)
  | @let₂ _ _ a b A B C da db iha ihb =>
    obtain ⟨u, norm, replay⟩ := iha σ
    have body := db.toHasType.bsubst (((σ.typed (Φ := Φ)).up A).up B)
    have expand := Equiv.bindPair (pureEff := false) norm.derivation.toHasType body
    apply normalized_of_equiv ((Equiv.let₂ replay (.refl body)).trans expand)
    apply bind_normalizes norm (HasType.let₂ .bv body.underTwoBinders)
    intro _ γ ρ v
    cases v with
    | pair left right =>
      rw [open_pack_continuation, rename_open_pair_assembly]
      let env : AssemblyEnv _ γ := fun i => (σ i).rename ρ
      exact normalized_of_equiv (replay_pair env left right db.toHasType)
        (ihb ((env.extend left).extend right))
  | @pair _ _ a b A B da db iha ihb =>
    obtain ⟨u, norm, replay⟩ := iha σ
    have right := db.toHasType.bsubst (σ.typed (Φ := Φ))
    have pairType : HasType Φ Γ₀ ((target.snoc A).snoc B)
        (.pair (.bv 1) (.bv 0)) (.product A B) := .pair .bv .bv
    have steps := (Equiv.pairEta (pureEff := false) (HasType.pair norm.derivation.toHasType right)).symm.trans
      (Equiv.pairBeta norm.derivation.toHasType right pairType)
    apply normalized_of_equiv ((Equiv.pair replay (.refl right)).trans steps)
    apply bind_normalizes norm (HasType.let₁ right.lift pairType)
    intro _ γ ρ v
    rw [open_left_pair]
    obtain ⟨u', norm', replay'⟩ := ihb (σ.rename ρ)
    rw [← rename_substituted σ ρ b] at replay'
    have pairRight : HasType Φ Γ₀ (γ.snoc B) (.pair v.term.lift (.bv 0)) (.product A B) :=
      .pair v.derivation.toHasType.lift .bv
    apply normalized_of_equiv (.let₁ replay' (.refl pairRight))
    apply bind_normalizes norm' pairRight
    intro _ _ ρ' w
    rw [open_right_pair, ← Assembly.term_rename ρ' v]
    exact ⟨_, .ret (.pair (v.rename ρ') w), .refl (.pair
      (v.rename ρ').derivation.toHasType w.derivation.toHasType)⟩

end Silmaril.Isotope.LetSeq.StraightLine.Structural

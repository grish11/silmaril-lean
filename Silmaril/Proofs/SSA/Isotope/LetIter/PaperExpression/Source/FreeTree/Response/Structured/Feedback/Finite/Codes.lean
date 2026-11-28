module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Defs
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Equations.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Reply.Reconstruction.Thms

import Mathlib.Data.Fintype.EquivFin
import Mathlib.Basic.Finite.Sum
import Mathlib.Logic.Equiv.Fin.Basic

public section

open Silmaril.Isotope
open Silmaril.Isotope.LetIter.PaperExpression.Source

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Proofs

variable {Φ ε : Type} [HasTy Φ (Ty Unit)] [HasEff Φ ε] [Preorder ε] [OrderBot ε]
  {Γ : EffectCtx (Ty Unit) ε} {c S T B : Code} {C : Ty Unit} {e : ε} {a : Expr Φ}

local notation "slot[" c "]" => (Code.ty c, (⊥ : ε))

omit [HasTy Φ (Ty Unit)] in
theorem literal_subst (c : Code) (x : c.Value) (σ : Nat → Expr Φ) :
    (c.literal x).subst σ = c.literal x := by
  induction c with
  | unit => rfl
  | sum l r il ir =>
      cases x with
      | inl v => exact congrArg Expr.inl (il v)
      | inr v => exact congrArg Expr.inr (ir v)

theorem literal_wf (c : Code) (x : c.Value) : Wf Γ (c.literal x : Expr Φ) c.ty e := by
  induction c with
  | unit => exact .unit _ _
  | sum l r il ir =>
      cases x with
      | inl v => exact .inl (il v)
      | inr v => exact .inr (ir v)

omit [HasTy Φ (Ty Unit)] in
theorem dispatch_subst (c : Code) {rows : c.Value → Expr Φ}
    (closed : ∀ v σ, (rows v).subst σ = rows v) (σ : Nat → Expr Φ) :
    (c.dispatch rows a).subst σ = c.dispatch rows (a.subst σ) := by
  induction c generalizing a σ with
  | unit => exact closed _ _
  | sum l r il ir =>
      simp only [Code.dispatch, Expr.subst]
      rw [il (fun v => closed (.inl v)), ir (fun v => closed (.inr v))]
      rfl

theorem dispatch_wf (c : Code) {rows : c.Value → Expr Φ}
    (branches : ∀ {Δ : EffectCtx (Ty Unit) ε} v, Wf Δ (rows v) C e)
    (arg : Wf Γ a c.ty e) : Wf Γ (c.dispatch rows a) C e := by
  induction c generalizing Γ a with
  | unit => exact branches _
  | sum l r il ir =>
      exact .case arg (il (fun v => branches (.inl v)) (.var 0 bot_le))
        (ir (fun v => branches (.inr v)) (.var 0 bot_le))

theorem dispatch_eqv (c : Code) {rows : c.Value → Expr Φ} {b : Expr Φ}
    (branches : ∀ {Δ : EffectCtx (Ty Unit) ε} v, Wf Δ (rows v) C e)
    (arg : Eqv Γ c.ty e a b) : Eqv Γ C e (c.dispatch rows a) (c.dispatch rows b) := by
  cases c with
  | unit => exact .refl (branches _)
  | sum l r =>
      exact .case arg (.refl (dispatch_wf l (fun v => branches (.inl v)) (.var 0 bot_le)))
        (.refl (dispatch_wf r (fun v => branches (.inr v)) (.var 0 bot_le)))

theorem dispatch_beta (c : Code) (v : c.Value) {rows : c.Value → Expr Φ}
    (closed : ∀ v σ, (rows v).subst σ = rows v)
    (branches : ∀ {Δ : EffectCtx (Ty Unit) ε} v, Wf Δ (rows v) C e) :
    Eqv Γ C e (c.dispatch rows (c.literal v)) (rows v) := by
  induction c generalizing Γ with
  | unit =>
      cases v
      exact .refl (branches _)
  | sum l r il ir =>
      have left := dispatch_wf (Γ := (l.ty, ⊥) :: Γ) l (fun v => branches (.inl v)) (.var 0 bot_le)
      have right := dispatch_wf (Γ := (r.ty, ⊥) :: Γ) r (fun v => branches (.inr v)) (.var 0 bot_le)
      cases v with
      | inl v =>
          have value : Wf Γ (l.literal v : Expr Φ) l.ty ⊥ := literal_wf l v
          have red := Eqv.step (.reduce (.case (.inl (value.weakenEffect bot_le)) left right)
            (.let₁ (value.weakenEffect bot_le) left) (.case_inl _ _ _))
          have beta := Eqv.step (.let1_beta value left)
          rw [dispatch_subst l (fun v => closed (.inl v))] at beta
          exact red.trans (beta.trans (il v (fun v => closed (.inl v)) (fun v => branches (.inl v))))
      | inr v =>
          have value : Wf Γ (r.literal v : Expr Φ) r.ty ⊥ := literal_wf r v
          have red := Eqv.step (.reduce (.case (.inr (value.weakenEffect bot_le)) left right)
            (.let₁ (value.weakenEffect bot_le) right) (.case_inr _ _ _))
          have beta := Eqv.step (.let1_beta value right)
          rw [dispatch_subst r (fun v => closed (.inr v))] at beta
          exact red.trans (beta.trans (ir v (fun v => closed (.inr v)) (fun v => branches (.inr v))))

omit [HasTy Φ (Ty Unit)] in
private theorem shape_value (c : Code) {n : Nat} {ss : Fin n → Unit} (s : ReplyShape ss c.ty) :
    n = 0 ∧ ∃ v : c.Value, ∀ {m : Nat} (place : Fin n → Fin m),
      s.source (Φ := Φ) place = c.literal v := by
  induction c with
  | unit =>
      cases s
      exact ⟨rfl, PUnit.unit, fun _ => rfl⟩
  | sum l r il ir =>
      cases s with
      | inl s =>
          obtain ⟨zero, v, eq⟩ := il s
          exact ⟨zero, .inl v, fun p => congrArg Expr.inl (eq p)⟩
      | inr s =>
          obtain ⟨zero, v, eq⟩ := ir s
          exact ⟨zero, .inr v, fun p => congrArg Expr.inr (eq p)⟩

theorem eqv_by_codes (c : Code) {a b : Expr Φ}
    (ha : Wf [(c.ty, ⊥)] a C e) (hb : Wf [(c.ty, ⊥)] b C e)
    (rows : ∀ v : c.Value, Eqv ([] : EffectCtx (Ty Unit) ε) C e
      (a.subst (c.literal v).subst0) (b.subst (c.literal v).subst0)) :
    Eqv [(c.ty, ⊥)] C e a b := by
  apply (ReplyShape.eqv_iff_specializations (Γ := []) (fun i => i.elim0) (fun i => i.elim0) ha hb).mpr
  intro n ss shape
  obtain ⟨rfl, v, eq⟩ := shape_value (Φ := Φ) c shape
  have σ : shape.sourceSubst ([] : EffectCtx (Ty Unit) ε) = (c.literal (Φ := Φ) v).subst0 := by
    funext i
    cases i with
    | zero => exact eq _
    | succ i => simp [ReplyShape.sourceSubst, Expr.subst0]
  change Eqv [] C e (a.subst (shape.sourceSubst ([] : EffectCtx (Ty Unit) ε)))
    (b.subst (shape.sourceSubst ([] : EffectCtx (Ty Unit) ε)))
  rw [σ]
  exact rows v

theorem stateMap_wf (h : S.Value → T.Value) :
    Wf (slot[S] :: Γ) (stateMap S T h : Expr Φ) T.ty e :=
  dispatch_wf S (fun _ => literal_wf _ _) (.var 0 bot_le)

theorem stateMap_readback (h : S.Value → T.Value) (s : S.Value) :
    Eqv Γ T.ty e ((stateMap S T h : Expr Φ).subst (S.literal s).subst0) (T.literal (h s)) := by
  unfold stateMap
  rw [dispatch_subst S (fun v => literal_subst T (h v))]
  exact dispatch_beta S s (fun v => literal_subst T (h v)) (fun _ => literal_wf _ _)

omit [HasTy Φ (Ty Unit)] [HasEff Φ ε] [Preorder ε] [OrderBot ε] in
theorem stateMap_wk1 {h : S.Value → T.Value} :
    (stateMap S T h : Expr Φ).wk1 = stateMap S T h := by
  rw [Expr.wk1, Expr.wk_eq_subst, stateMap, dispatch_subst S (fun v => literal_subst _ _)]
  rfl

theorem mapControl_wf (h : S.Value → T.Value) :
    Wf (slot[Code.sum B S] :: Γ) (mapControl (Φ := Φ) B h) (Code.sum B T).ty e :=
  .case (.var 0 bot_le) (.inl (.var 0 bot_le)) (.inr (stateMap_wf h))

omit [HasTy Φ (Ty Unit)] [HasEff Φ ε] [Preorder ε] [OrderBot ε] in
theorem mapControl_subst (h : S.Value → T.Value) (σ : Nat → Expr Φ) :
    (mapControl (Φ := Φ) B h).subst σ = .case (σ 0) (.inl (.var 0)) (.inr (stateMap S T h)) := by
  simp only [mapControl, Expr.subst, Expr.liftSubst, stateMap, dispatch_subst S (fun v => literal_subst _ _)]

omit [HasTy Φ (Ty Unit)] [HasEff Φ ε] [Preorder ε] [OrderBot ε] in
theorem mapControl_wk1 {h : S.Value → T.Value} :
    (mapControl (Φ := Φ) B h).wk1 = mapControl B h := by
  rw [Expr.wk1, Expr.wk_eq_subst, mapControl_subst]
  rfl

theorem mapControl_readback (h : S.Value → T.Value) (v : (Code.sum B S).Value) :
    Eqv Γ (Code.sum B T).ty e (.let₁ ((Code.sum B S).literal v) (mapControl B h) : Expr Φ)
      ((Code.sum B T).literal (Sum.map id h v)) := by
  have value : Wf Γ ((Code.sum B S).literal v : Expr Φ) (Code.sum B S).ty ⊥ := literal_wf _ _
  have beta := Eqv.step (.let1_beta value (mapControl_wf (Γ := Γ) (B := B) (e := e) h))
  rw [mapControl_subst] at beta
  have l : Wf (slot[B] :: Γ) (.inl (.var 0) : Expr Φ) (Code.sum B T).ty e := .inl (.var 0 bot_le)
  have r : Wf (slot[S] :: Γ) (.inr (stateMap S T h) : Expr Φ) (Code.sum B T).ty e := .inr (stateMap_wf h)
  cases v with
  | inl v =>
      have p : Wf Γ (B.literal v : Expr Φ) B.ty ⊥ := literal_wf _ _
      exact beta.trans ((Eqv.step (.reduce (.case (.inl (p.weakenEffect bot_le)) l r)
        (.let₁ (p.weakenEffect bot_le) l) (.case_inl _ _ _))).trans (.step (.let1_beta p l)))
  | inr v =>
      have p : Wf Γ (S.literal v : Expr Φ) S.ty ⊥ := literal_wf _ _
      exact beta.trans ((Eqv.step (.reduce (.case (.inr (p.weakenEffect bot_le)) l r)
        (.let₁ (p.weakenEffect bot_le) r) (.case_inr _ _ _))).trans
        ((Eqv.step (.let1_beta p r)).trans (.inr (stateMap_readback h v))))


theorem finiteValue (c : Code) : _root_.Finite c.Value := by
  induction c with
  | unit => exact inferInstanceAs (_root_.Finite PUnit)
  | sum l r il ir => exact inferInstanceAs (_root_.Finite (l.Value ⊕ r.Value))

private theorem encodeFin (n : Nat) : ∃ c : Code, Nonempty (c.Value ≃ Fin (n + 1)) := by
  let unitCode : Code.Value Code.unit ≃ Fin 1 := (Equiv.equivPUnit (Fin 1)).symm
  induction n with
  | zero => exact ⟨.unit, ⟨unitCode⟩⟩
  | succ _ ih =>
      obtain ⟨c, ⟨eqv⟩⟩ := ih
      exact ⟨.sum c .unit, ⟨(eqv.sumCongr unitCode).trans finSumFinEquiv⟩⟩

theorem encodeFinite (A : Type) [_root_.Finite A] (initial : A) :
    ∃ c : Code, Nonempty (c.Value ≃ A) := by
  obtain ⟨n, ⟨e⟩⟩ := _root_.Finite.exists_equiv_fin A
  cases n with
  | zero => exact (e initial).elim0
  | succ n =>
      obtain ⟨c, ⟨v⟩⟩ := encodeFin n
      exact ⟨c, ⟨v.trans e.symm⟩⟩


end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Proofs

module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Defs
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Codes.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Square
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Equations.Thms

public section

open Silmaril.Isotope
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.LocallyNameless (Tm HasTypeEffect AbortEquiv)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Proofs

variable {Q K S T B : Code} {ε : Type}
  [HasEff (Opcode Q K) ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]
  {e : ε} {L : Table Q K S B} {R : Table Q K T B}

local notation "Ops" => Opcode Q K
local notation "Free" => (Ctx.nil : Ctx Empty (Ty Unit))
local notation "emptyCtx" => ([] : EffectCtx (Ty Unit) ε)

section Dispatch

variable {Φ : Type} [HasTy Φ (Ty Unit)] [HasEff Φ ε] {S T B : Code}

theorem replay_dispatch_square {s₀ : S.Value} {t₀ : T.Value}
    (left : S.Value → Expr Φ) (right : T.Value → Expr Φ)
    (closed : ∀ v σ, (right v).subst σ = right v)
    (wl : Wf [(S.ty, ⊥)] (S.dispatch left (.var 0)) (Code.sum B S).ty e)
    (wr : Wf [(T.ty, ⊥)] (T.dispatch right (.var 0)) (Code.sum B T).ty e)
    {h : S.Value → T.Value} (initial : h s₀ = t₀)
    (square : Eqv [(S.ty, ⊥)] (Code.sum B T).ty e
      (.case (S.dispatch left (.var 0)) (.inl (.var 0)) (.inr (stateMap S T h)))
      (T.dispatch right (stateMap S T h)))
    (he : IsIterative e) :
    ∃ (a a' : Tm Empty Φ 0) (b b' : Tm Empty Φ 1),
      (S.literal s₀).toLetIter 0 = some a ∧ (T.literal t₀).toLetIter 0 = some a' ∧
      (S.dispatch left (.var 0)).toLetIter 1 = some b ∧ (T.dispatch right (.var 0)).toLetIter 1 = some b' ∧
      HasTypeEffect Free .nil (.iter a b) B.ty e ∧ HasTypeEffect Free .nil (.iter a' b') B.ty e ∧
      AbortEquiv (⊥ : ε) Free .nil (.iter a b) (.iter a' b') B.ty := by
  have lhs : Wf emptyCtx (S.literal s₀ : Expr Φ) S.ty e := literal_wf S s₀
  have rhs : Wf emptyCtx (T.literal t₀ : Expr Φ) T.ty e := literal_wf T t₀
  obtain ⟨a, ha, ta⟩ := lhs.toLetIter
  obtain ⟨a', ha', ta'⟩ := rhs.toLetIter
  obtain ⟨b, hb, tb⟩ := wl.toLetIter
  obtain ⟨b', hb', tb'⟩ := wr.toLetIter
  have hm : Wf [(S.ty, (⊥ : ε))] (stateMap S T h : Expr Φ) T.ty ⊥ := stateMap_typed h
  obtain ⟨m, ml, mt⟩ := hm.toLetIter
  have pure := hm.pure_toLetIter ml
  have underMap := Expr.toLetIter_wk1 ml
  rw [stateMap_wk1] at underMap
  change (S.dispatch left (.var 0)).toLetIter 1 = some b at hb
  change (T.dispatch right (.var 0)).toLetIter 1 = some b' at hb'
  change (stateMap S T h : Expr Φ).toLetIter 2 = some m.underBinder at underMap
  have leftSquare : (.case (S.dispatch left (.var 0)) (.inl (.var 0)) (.inr (stateMap S T h)) : Expr Φ).toLetIter 1 =
      some (.case b (.inl (.bv 0)) (.inr m.underBinder)) := by
    simp [Expr.toLetIter, hb, underMap]
  have rhsSquare : T.dispatch right (stateMap S T h) =
      ((T.dispatch right (.var 0)).wk1).subst (stateMap S T h).subst0 := by
    rw [Expr.wk1, Expr.wk_eq_subst, Expr.subst_comp, dispatch_subst T closed]
    rfl
  have rightSquare := Expr.toLetIter_subst0 ml (Expr.toLetIter_wk1 hb')
  rw [← rhsSquare] at rightSquare
  have eq := replay_written_square (Γ := emptyCtx) ta.1 mt.1 pure tb.1 tb'.1
    leftSquare rightSquare square
  change (S.literal s₀ : Expr Φ).toLetIter 0 = some a at ha
  change (stateMap S T h : Expr Φ).toLetIter 1 = some m at ml
  have beta : Eqv emptyCtx T.ty e (.let₁ (S.literal s₀) (stateMap S T h) : Expr Φ) (T.literal t₀) := by
    rw [← initial]
    exact (Eqv.step (.let1_beta (literal_wf S s₀) (stateMap_typed h))).trans (stateMap_specialize h s₀)
  have initEq := beta.toLetIter (show (.let₁ (S.literal s₀) (stateMap S T h) : Expr Φ).toLetIter 0 =
    some (.let₁ a m) by simp [Expr.toLetIter, ha, ml]) ha'
  exact ⟨a, a', b, b', ha, ha', hb, hb', .iter he ta tb, .iter he ta' tb',
    eq.trans (.iter initEq (.refl tb'.1))⟩

end Dispatch

theorem replay_commutes {s₀ : S.Value} {t₀ : T.Value}
    {h : S.Value → T.Value} (commute : Commutes L R h) (initial : h s₀ = t₀)
    (hf : instrEff (Opcode.ask : Ops) ≤ e) (he : IsIterative e) :
    ∃ (a a' : Tm Empty Ops 0) (b b' : Tm Empty Ops 1),
      (S.literal s₀).toLetIter 0 = some a ∧ (T.literal t₀).toLetIter 0 = some a' ∧
      L.source.toLetIter 1 = some b ∧ R.source.toLetIter 1 = some b' ∧
      HasTypeEffect Free .nil (.iter a b) B.ty e ∧ HasTypeEffect Free .nil (.iter a' b') B.ty e ∧
      AbortEquiv (⊥ : ε) Free .nil (.iter a b) (.iter a' b') B.ty := by
  exact replay_dispatch_square L.row R.row (row_closed R) (step_wf L hf) (step_wf R hf)
    initial (source_square h commute hf) he

theorem replay {s₀ : S.Value} {t₀ : T.Value}
    (separates : Function.Injective R.request) (reach : ∀ s, L.Reaches s₀ s)
    (obs : L.run s₀ = R.run t₀)
    (hf : instrEff (Opcode.ask : Ops) ≤ e) (he : IsIterative e) :
    ∃ (a a' : Tm Empty Ops 0) (b b' : Tm Empty Ops 1),
      (S.literal s₀).toLetIter 0 = some a ∧ (T.literal t₀).toLetIter 0 = some a' ∧
      L.source.toLetIter 1 = some b ∧ R.source.toLetIter 1 = some b' ∧
      HasTypeEffect Free .nil (.iter a b) B.ty e ∧ HasTypeEffect Free .nil (.iter a' b') B.ty e ∧
      AbortEquiv (⊥ : ε) Free .nil (.iter a b) (.iter a' b') B.ty := by
  obtain ⟨h, commute, initial⟩ := exists_commutes_of_initial separates reach obs
  exact replay_commutes commute initial hf he

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Proofs

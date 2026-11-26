module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Codes.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Square
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Replay

/-! # Reifying a recovered finite state map and replaying source equations -/

public section

open Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Tm HasTypeEffect AbortEquiv)
open Silmaril.Isotope.LetIter.PaperExpression.Source

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite

variable {Q K S T B : Code} {ε : Type} [HasEff (Opcode Q K) ε]
  {e : ε} {L : Table Q K S B} {R : Table Q K T B}

local notation "Ops" => Opcode Q K

section Source

variable [Preorder ε] [OrderBot ε]

theorem Code.literal_wf (c : Code) (v : c.Value) (Γ : EffectCtx (Ty Unit) ε) :
    Wf Γ (c.literal v : Expr Ops) c.ty e :=
  Finite.literal_wf c v

theorem Table.step_wf (M : Table Q K S B) (hf : instrEff (Opcode.ask : Ops) ≤ e) :
    Wf [(S.ty, ⊥)] M.source (Code.sum B S).ty e :=
  Proofs.step_wf M hf

/-- The rendered state map is typed at bottom. -/
theorem stateMap_wf (h : S.Value → T.Value) :
    Wf [(S.ty, (⊥ : ε))] (stateMap S T h : Expr Ops) T.ty ⊥ :=
  Finite.stateMap_typed h

/-- Supplying a constructor state evaluates the map to its reified result
using only source case and bottom let beta. -/
theorem stateMap_readback (h : S.Value → T.Value) (s : S.Value) :
    Source.Eqv ([] : EffectCtx (Ty Unit) ε) T.ty e
      ((stateMap S T h : Expr Ops).subst (S.literal s).subst0) (T.literal (h s)) :=
  Finite.stateMap_specialize h s

/-- Specializing the rendered step selects the row for that constructor
state while preserving the original bound. -/
theorem Table.step_readback (M : Table Q K S B) (s : S.Value) (hf : instrEff (Opcode.ask : Ops) ≤ e) :
    Source.Eqv ([] : EffectCtx (Ty Unit) ε) (Code.sum B S).ty e
      (M.source.subst (S.literal s).subst0) (M.row s) :=
  Proofs.step_readback M s hf

/-- After the request returns, its constructor reply selects exactly the
literal return or repeat value from that row. -/
theorem Table.reply_readback (M : Table Q K S B) (s : S.Value) (r : K.Value) :
    Source.Eqv ([] : EffectCtx (Ty Unit) ε) (Code.sum B S).ty e
      ((K.dispatch (fun r => (Code.sum B S).literal (M.reply s r)) (.var 0) : Expr Ops).subst
        (K.literal r).subst0) ((Code.sum B S).literal (M.reply s r)) :=
  Proofs.reply_readback M s r

/-- A commuting table map yields a typed source equation between the two
loop-free step expressions at the supplied effect bound. -/
theorem source_square (h : S.Value → T.Value) (square : Commutes L R h)
    (hf : instrEff (Opcode.ask : Ops) ≤ e) :
    Source.Eqv [(S.ty, ⊥)] (Code.sum B T).ty e
      (.case L.source (.inl (.var 0)) (.inr (stateMap S T h)))
      (T.dispatch R.row (stateMap S T h)) :=
  Proofs.source_square h square hf

end Source

variable [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]

local notation "Free" => (Ctx.nil : Ctx Empty (Ty Unit))

section Dispatch

variable {Φ : Type} [HasTy Φ (Ty Unit)] [HasEff Φ ε]

/-- Lower a square between constructor dispatches and replay it by native
uniformity, preserving the supplied bound. -/
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
      AbortEquiv (⊥ : ε) Free .nil (.iter a b) (.iter a' b') B.ty :=
  Proofs.replay_dispatch_square left right closed wl wr initial square he

end Dispatch

/-- Replay a supplied commuting table map by reifying it to pure case
syntax, lowering the source square, and applying native uniformity. -/
theorem replay_commutes {s₀ : S.Value} {t₀ : T.Value}
    {h : S.Value → T.Value} (commute : Commutes L R h) (initial : h s₀ = t₀)
    (hf : instrEff (Opcode.ask : Ops) ≤ e) (he : IsIterative e) :
    ∃ (a a' : Tm Empty Ops 0) (b b' : Tm Empty Ops 1),
      (S.literal s₀).toLetIter 0 = some a ∧ (T.literal t₀).toLetIter 0 = some a' ∧
      L.source.toLetIter 1 = some b ∧ R.source.toLetIter 1 = some b' ∧
      HasTypeEffect Free .nil (.iter a b) B.ty e ∧ HasTypeEffect Free .nil (.iter a' b') B.ty e ∧
      AbortEquiv (⊥ : ε) Free .nil (.iter a b) (.iter a' b') B.ty :=
  Proofs.replay_commutes commute initial hf he

/-- Recover a finite state map from the table observations and replay it on
the independently rendered native loops. Reachability and request
separation are the hypotheses of the semantic recovery theorem. -/
theorem replay {s₀ : S.Value} {t₀ : T.Value}
    (separates : Function.Injective R.request) (reach : ∀ s, L.Reaches s₀ s)
    (obs : L.run s₀ = R.run t₀)
    (hf : instrEff (Opcode.ask : Ops) ≤ e) (he : IsIterative e) :
    ∃ (a a' : Tm Empty Ops 0) (b b' : Tm Empty Ops 1),
      (S.literal s₀).toLetIter 0 = some a ∧ (T.literal t₀).toLetIter 0 = some a' ∧
      L.source.toLetIter 1 = some b ∧ R.source.toLetIter 1 = some b' ∧
      HasTypeEffect Free .nil (.iter a b) B.ty e ∧ HasTypeEffect Free .nil (.iter a' b') B.ty e ∧
      AbortEquiv (⊥ : ε) Free .nil (.iter a b) (.iter a' b') B.ty :=
  Proofs.replay separates reach obs hf he

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite

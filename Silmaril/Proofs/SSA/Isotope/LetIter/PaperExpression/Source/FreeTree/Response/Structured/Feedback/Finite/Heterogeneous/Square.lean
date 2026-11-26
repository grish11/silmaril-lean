module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Defs
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Codes.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Reply.Arguments.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Equations.Thms

public section

open Silmaril.Isotope
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyArguments (case_eqv_bind)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Proofs

variable {n : Nat} {F : Family n} {S T B : Code} {ε : Type} [HasEff (Opcode F) ε]
  [Preorder ε] [OrderBot ε] {Γ : EffectCtx (Ty Unit) ε} {e : ε}

local notation "Ops" => Opcode F
local notation "slot[" c "]" => (Code.ty c, (⊥ : ε))
local notation "Δ₀" => ([] : EffectCtx (Ty Unit) ε)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem reply_wf {f : Ops} (k : f.replyCode.Value → B.Value ⊕ S.Value) :
    Wf (slot[f.replyCode] :: Γ) (replySource k) (Code.sum B S).ty e :=
  dispatch_wf f.replyCode (fun _ => literal_wf _ _) (.var 0 bot_le)

theorem row_wf (row : Row F S B) (hf : ∀ f : Ops, instrEff f ≤ e) :
    Wf Γ row.source (Code.sum B S).ty e := by
  cases row with
  | ret v => exact .inl (literal_wf _ _)
  | call f x k => exact .let₁ (.op (hf f) (literal_wf _ _)) (reply_wf k)

theorem step_wf (L : Table F S B) (hf : ∀ f : Ops, instrEff f ≤ e) :
    Wf [slot[S]] L.source (Code.sum B S).ty e :=
  dispatch_wf S (fun s => row_wf (L s) hf) (.var 0 bot_le)

omit [HasEff (Opcode F) ε] [Preorder ε] [OrderBot ε] in
theorem row_closed (row : Row F S B) (σ : Nat → Expr Ops) : row.source.subst σ = row.source := by
  cases row with
  | ret v => simp only [Row.source, Expr.subst, literal_subst]
  | call f x k =>
    simp only [Row.source, replySource, Expr.subst, literal_subst,
      dispatch_subst f.replyCode (fun v => literal_subst _ _) (Expr.liftSubst σ), Expr.liftSubst]

theorem reply_readback {f : Ops} (k : f.replyCode.Value → B.Value ⊕ S.Value) (r : f.replyCode.Value) :
    Eqv Δ₀ (Code.sum B S).ty e ((replySource k).subst (f.replyCode.literal r).subst0)
      ((Code.sum B S).literal (k r)) := by
  unfold replySource
  rw [dispatch_subst f.replyCode (fun v => literal_subst (Code.sum B S) (k v))]
  exact dispatch_beta f.replyCode r (fun v => literal_subst _ _) (fun _ => literal_wf _ _)

theorem step_readback (M : Table F S B) (s : S.Value) (hf : ∀ f : Ops, instrEff f ≤ e) :
    Eqv Δ₀ (Code.sum B S).ty e (M.source.subst (S.literal s).subst0) (M s).source := by
  unfold Table.source
  rw [dispatch_subst S (fun v => row_closed (M v))]
  exact dispatch_beta S s (fun v => row_closed (M v)) (fun v => row_wf (M v) hf)

private theorem case_row (row : Row F S B) (h : S.Value → T.Value) (hf : ∀ f : Ops, instrEff f ≤ e) :
    Eqv Δ₀ (Code.sum B T).ty e
      (.case row.source (.inl (.var 0)) (.inr (stateMap S T h))) (row.map h).source := by
  have lhs : Wf [slot[B]] (.inl (.var 0) : Expr Ops) (Code.sum B T).ty e := .inl (.var 0 bot_le)
  have rhs : Wf [slot[S]] (.inr (stateMap S T h) : Expr Ops) (Code.sum B T).ty e :=
    .inr (stateMap_typed h)
  have first := case_eqv_bind (row_wf (Γ := []) row hf) lhs rhs
  have ir : (.inr (stateMap S T h) : Expr Ops).wk1 = .inr (stateMap S T h) := congrArg Expr.inr stateMap_wk1
  rw [ir] at first
  change Eqv Δ₀ (Code.sum B T).ty e _ (.let₁ row.source (mapControl B h)) at first
  refine first.trans ?_
  cases row with
  | ret value => exact mapControl_readback h (.inl value)
  | call f x k =>
    let K := f.replyCode
    let req : Expr Ops := .op f (f.argCode.literal x)
    have typedReq : Wf Δ₀ req K.ty e := .op (hf f) (literal_wf _ _)
    have resL := reply_wf (Γ := []) (e := e) k
    have wrap := mapControl_wf (Φ := Ops) (Γ := []) (B := B) (e := e) h
    have wrap' := mapControl_wf (Φ := Ops) (Γ := [slot[K]]) (B := B) (e := e) h
    have assoc := Eqv.step (.rewrite (.let₁ (.let₁ typedReq resL) wrap)
      (.let₁ typedReq (.let₁ resL (mapControl_wk1.symm ▸ wrap'))) (.let1_let1 _ _ _))
    rw [mapControl_wk1] at assoc
    change Eqv Δ₀ (Code.sum B T).ty e (.let₁ (.let₁ req (replySource k)) (mapControl B h)) _
    refine assoc.trans (.let1 (.refl typedReq)
      (eqv_by_codes K (.let₁ resL wrap') (reply_wf (fun r => Sum.map id h (k r))) (fun v => ?_)))
    simp only [replySource, Expr.subst, dispatch_subst f.replyCode (fun v => literal_subst _ _), Expr.subst0,
      mapControl_subst, Expr.liftSubst]
    have left := dispatch_beta (Φ := Ops) (Γ := []) (e := e) K v
      (rows := fun r => (Code.sum B S).literal (k r)) (fun v => literal_subst _ _) (fun _ => literal_wf _ _)
    have right := dispatch_beta (Φ := Ops) (Γ := []) (e := e) K v
      (rows := fun r => (Code.sum B T).literal (Sum.map id h (k r)))
      (fun v => literal_subst _ _) (fun _ => literal_wf _ _)
    exact (Eqv.let1 left (.refl wrap)).trans ((mapControl_readback h (k v)).trans right.symm)

theorem source_square {L : Table F S B} {R : Table F T B}
    (h : S.Value → T.Value) (square : Commutes L R h) (hf : ∀ f : Ops, instrEff f ≤ e) :
    Eqv [slot[S]] (Code.sum B T).ty e
      (.case L.source (.inl (.var 0)) (.inr (stateMap S T h)))
      (T.dispatch (fun t => (R t).source) (stateMap S T h)) := by
  refine eqv_by_codes S (.case (step_wf L hf) (.inl (.var 0 bot_le)) (.inr (stateMap_typed h)))
    (dispatch_wf T (fun t => row_wf (R t) hf) (stateMap_typed h)) (fun s => ?_)
  simp only [Expr.subst, Table.source, dispatch_subst S (fun v => row_closed (L v)),
    dispatch_subst T (fun v => row_closed (R v)), stateMap,
    dispatch_subst S (fun v => literal_subst _ _), Expr.subst0, Expr.liftSubst]
  have read := dispatch_beta (Γ := []) S s (rows := fun v => (L v).source)
    (fun v => row_closed (L v)) (fun v => row_wf (L v) hf)
  have arg := dispatch_beta (Φ := Ops) (Γ := []) (e := e) S s
    (rows := fun v => T.literal (h v)) (fun v => literal_subst _ _) (fun _ => literal_wf _ _)
  have right := dispatch_beta (Γ := []) T (h s) (rows := fun v => (R v).source)
    (fun v => row_closed (R v)) (fun v => row_wf (R v) hf)
  have mapped := case_row (L s) h hf
  rw [square s] at mapped
  exact (Eqv.case read (.refl (.inl (.var 0 bot_le))) (.refl (.inr (stateMap_typed h)))).trans
    (mapped.trans (right.symm.trans (dispatch_eqv T (fun v => row_wf (R v) hf) arg.symm)))

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Proofs

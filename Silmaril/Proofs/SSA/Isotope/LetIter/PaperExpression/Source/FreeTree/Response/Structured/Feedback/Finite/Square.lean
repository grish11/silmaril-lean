module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Defs
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Codes.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Reply.Arguments.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Equations.Thms

public section

open Silmaril.Isotope
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyArguments (case_eqv_bind)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Proofs

variable {Q K S T B : Code} {ε : Type} [HasEff (Opcode Q K) ε] [Preorder ε] [OrderBot ε]
  {Γ : EffectCtx (Ty Unit) ε} {e : ε}

local notation "Ops" => Opcode Q K
local notation "slot[" c "]" => (Code.ty c, (⊥ : ε))

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem replies_wf (L : Table Q K S B) (s : S.Value) :
    Wf (slot[K] :: Γ)
      (K.dispatch (fun r => (Code.sum B S).literal (L.reply s r)) (.var 0) : Expr Ops)
      (Code.sum B S).ty e :=
  dispatch_wf K (fun _ => literal_wf _ _) (.var 0 bot_le)

theorem row_wf (L : Table Q K S B) (s : S.Value) (hf : instrEff (Opcode.ask : Ops) ≤ e) :
    Wf Γ (L.row s) (Code.sum B S).ty e :=
  .let₁ (.op hf (literal_wf _ _)) (replies_wf L s)

theorem step_wf (L : Table Q K S B) (hf : instrEff (Opcode.ask : Ops) ≤ e) :
    Wf [slot[S]] L.source (Code.sum B S).ty e :=
  dispatch_wf S (fun s => row_wf L s hf) (.var 0 bot_le)

omit [HasEff (Opcode Q K) ε] [Preorder ε] [OrderBot ε] in
theorem row_closed (L : Table Q K S B) (s : S.Value) (σ : Nat → Expr Ops) :
    (L.row s).subst σ = L.row s := by
  simp only [Table.row, Expr.subst]
  rw [literal_subst Q (L.request s) σ,
    dispatch_subst K (rows := fun r => (Code.sum B S).literal (L.reply s r)) (fun v => literal_subst _ _)]
  rfl

theorem reply_readback (L : Table Q K S B) (s : S.Value) (r : K.Value) :
    Eqv ([] : EffectCtx (Ty Unit) ε) (Code.sum B S).ty e
      ((K.dispatch (fun r => (Code.sum B S).literal (L.reply s r)) (.var 0) : Expr Ops).subst
        (K.literal r).subst0) ((Code.sum B S).literal (L.reply s r)) := by
  rw [dispatch_subst K (rows := fun r => (Code.sum B S).literal (L.reply s r)) (fun v => literal_subst _ _)]
  exact dispatch_beta K r (fun v => literal_subst _ _) (fun _ => literal_wf _ _)

theorem step_readback (L : Table Q K S B) (s : S.Value) (hf : instrEff (Opcode.ask : Ops) ≤ e) :
    Eqv ([] : EffectCtx (Ty Unit) ε) (Code.sum B S).ty e
      (L.source.subst (S.literal s).subst0) (L.row s) := by
  unfold Table.source
  rw [dispatch_subst S (row_closed L)]
  exact dispatch_beta S s (row_closed L) (fun v => row_wf L v hf)

private theorem case_row {L : Table Q K S B} {R : Table Q K T B}
    (h : S.Value → T.Value) (square : Commutes L R h) (s : S.Value)
    (hf : instrEff (Opcode.ask : Ops) ≤ e) :
    Eqv ([] : EffectCtx (Ty Unit) ε) (Code.sum B T).ty e
      (.case (L.row s) (.inl (.var 0)) (.inr (stateMap S T h))) (R.row (h s)) := by
  obtain ⟨head, replies⟩ := square s
  let request : Expr Ops := .op .ask (Q.literal (L.request s))
  have req : Wf ([] : EffectCtx (Ty Unit) ε) request K.ty e := .op hf (literal_wf _ _)
  have resL := replies_wf (Γ := []) (e := e) L s
  have wrap := mapControl_wf (Φ := Ops) (Γ := []) (B := B) (e := e) h
  have wrap' := mapControl_wf (Φ := Ops) (Γ := [slot[K]]) (B := B) (e := e) h
  have first : Eqv ([] : EffectCtx (Ty Unit) ε) (Code.sum B T).ty e
      (.case (L.row s) (.inl (.var 0)) (.inr (stateMap S T h))) (.let₁ (L.row s) (mapControl B h)) := by
    have lhs : Wf [slot[B]] (.inl (.var 0) : Expr Ops) (Code.sum B T).ty e := .inl (.var 0 bot_le)
    have rhs : Wf [slot[S]] (.inr (stateMap S T h) : Expr Ops) (Code.sum B T).ty e := .inr (stateMap_typed h)
    have eq := case_eqv_bind (row_wf (Γ := []) L s hf) lhs rhs
    have ir : (.inr (stateMap S T h) : Expr Ops).wk1 = .inr (stateMap S T h) :=
      congrArg Expr.inr stateMap_wk1
    rw [ir] at eq
    exact eq
  have assoc := Eqv.step (.rewrite (.let₁ (.let₁ req resL) wrap)
    (.let₁ req (.let₁ resL (mapControl_wk1.symm ▸ wrap'))) (.let1_let1 _ _ _))
  rw [mapControl_wk1] at assoc
  refine first.trans (assoc.trans ?_)
  unfold Table.row
  rw [← head]
  refine .let1 (.refl req) (eqv_by_codes K (.let₁ resL wrap') (replies_wf R (h s)) (fun v => ?_))
  simp only [Expr.subst, dispatch_subst K (fun v => literal_subst _ _), Expr.subst0,
    mapControl_subst, Expr.liftSubst]
  have left := dispatch_beta (Φ := Ops) (Γ := []) (e := e) K v
    (rows := fun r => (Code.sum B S).literal (L.reply s r))
    (fun v => literal_subst _ _) (fun _ => literal_wf _ _)
  have right := dispatch_beta (Φ := Ops) (Γ := []) (e := e) K v
    (rows := fun r => (Code.sum B T).literal (R.reply (h s) r))
    (fun v => literal_subst _ _) (fun _ => literal_wf _ _)
  have mapped := mapControl_readback (Φ := Ops) (Γ := []) h (L.reply s v) (e := e)
  rw [replies v] at mapped
  exact (Eqv.let1 left (.refl wrap)).trans (mapped.trans right.symm)

theorem source_square {L : Table Q K S B} {R : Table Q K T B}
    (h : S.Value → T.Value) (square : Commutes L R h) (hf : instrEff (Opcode.ask : Ops) ≤ e) :
    Eqv [slot[S]] (Code.sum B T).ty e
      (.case L.source (.inl (.var 0)) (.inr (stateMap S T h)))
      (T.dispatch R.row (stateMap S T h)) := by
  refine eqv_by_codes S (.case (step_wf L hf) (.inl (.var 0 bot_le)) (.inr (stateMap_typed h)))
    (dispatch_wf T (fun t => row_wf R t hf) (stateMap_typed h)) (fun s => ?_)
  simp only [Expr.subst, Table.source, dispatch_subst S (fun v => row_closed L v),
    dispatch_subst T (fun v => row_closed R v), stateMap,
    dispatch_subst S (fun v => literal_subst _ _), Expr.subst0, Expr.liftSubst]
  have read := dispatch_beta (Γ := []) S s (rows := L.row) (row_closed L) (fun v => row_wf L v hf)
  have arg := dispatch_beta (Φ := Ops) (Γ := []) (e := e) S s
    (rows := fun v => T.literal (h v)) (fun v => literal_subst _ _) (fun _ => literal_wf _ _)
  have right := dispatch_beta (Γ := []) T (h s) (rows := R.row) (row_closed R) (fun v => row_wf R v hf)
  exact (Eqv.case read (.refl (.inl (.var 0 bot_le))) (.refl (.inr (stateMap_typed h)))).trans
    ((case_row h square s hf).trans (right.symm.trans (dispatch_eqv T (fun v => row_wf R v hf) arg.symm)))

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Proofs

module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Defs
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Codes.Thms
import Mathlib.Basic.Finite.Prod

public section

open Silmaril.Elgot

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Proofs

variable {n : Nat} {F : Family n} {S T B : Code} {L : Table F S B} {R : Table F T B}
  {s₀ : S.Value} {t₀ : T.Value}

theorem run_unfold (M : Table F S B) (s : S.Value) :
    M.run s = match M s with
    | .ret v => ITree.ret (B.raise v)
    | .call f x k => ITree.vis (.call f x) (fun r => Sum.elim (fun b => ITree.ret (B.raise b)) M.run (k r)) := by
  unfold Table.run
  nth_rw 1 [congrFun (ITree.iterate_fixpoint M.step) (S.raise s)]
  unfold Table.step
  rw [Equiv.symm_apply_apply]
  cases M s with
  | ret v =>
    change (pure (Sum.inl (B.raise v) : B.Large ⊕ S.Large) >>= _) = _
    rw [pure_bind]
    rfl
  | call f x k =>
    rw [Row.step, ITree.vis_bind]
    congr 1
    funext r
    change (pure (Sum.map B.raise S.raise (k r)) >>= _) = _
    rw [pure_bind]
    cases k r <;> rfl

private def MatchesResult (rel : S.Value → T.Value → Prop) :
    B.Value ⊕ S.Value → B.Value ⊕ T.Value → Prop
  | .inl l, .inl r => l = r
  | .inr l, .inr r => rel l r
  | _, _ => False

private inductive Matches (rel : S.Value → T.Value → Prop) : Row F S B → Row F T B → Prop
  | ret (v : B.Value) : Matches rel (.ret v) (.ret v)
  | call (f : Opcode F) (x : f.argCode.Value) (k : f.replyCode.Value → B.Value ⊕ S.Value)
      (j : f.replyCode.Value → B.Value ⊕ T.Value) (next : ∀ r, MatchesResult rel (k r) (j r)) :
      Matches rel (.call f x k) (.call f x j)

private theorem related_step {s : S.Value} {t : T.Value} (obs : L.run s = R.run t)
    (aligned : ∀ {f : Opcode F} {x : f.argCode.Value}
      {k : f.replyCode.Value → B.Value ⊕ S.Value} {j : f.replyCode.Value → B.Value ⊕ T.Value},
      L s = .call f x k → R t = .call f x j → ∀ r, (k r).isLeft = (j r).isLeft) :
    Matches (fun s t => L.run s = R.run t) (L s) (R t) := by
  rw [run_unfold, run_unfold] at obs
  cases hL : L s with
  | ret v =>
    cases hR : R t with
    | ret w =>
      rw [hL, hR] at obs
      have eq := B.raise.injective (ITree.ret_inj.mp obs)
      subst w
      exact .ret v
    | call _ _ _ =>
      rw [hL, hR] at obs
      exact (ITree.ret_ne_vis _ _ _ obs).elim
  | call f x k =>
    cases hR : R t with
    | ret _ =>
      rw [hL, hR] at obs
      exact (ITree.ret_ne_vis _ _ _ obs.symm).elim
    | call g y j =>
      rw [hL, hR] at obs
      have tag : f = g := congrArg Sigma.fst (request_eq_of_vis_eq carriers obs)
      subst g
      obtain ⟨rfl, children⟩ := (vis_eq_iff carriers).mp obs
      refine .call f x k j (fun r => ?_)
      have child := children r
      have mode := aligned hL hR r
      cases hl : k r <;> cases hr : j r <;> rw [hl, hr] at child
      · exact B.raise.injective (ITree.ret_inj.mp child)
      · rw [hl, hr] at mode
        cases mode
      · rw [hl, hr] at mode
        cases mode
      · exact child

theorem run_eq_of_reach (obs : L.run s₀ = R.run t₀)
    {p : S.Value × T.Value} (reach : PairedReach L R s₀ t₀ p) :
    L.run p.1 = R.run p.2 := by
  induction reach with
  | initial => exact obs
  | after_reply _ f x r k j hL hR hl hr ih =>
    rw [run_unfold, run_unfold, hL, hR] at ih
    have next := (vis_eq_iff carriers).mp ih |>.2 r
    rw [hl, hr] at next
    exact next

theorem aligned_of_guarded (obs : L.run s₀ = R.run t₀) (left : Guarded L) (right : Guarded R) :
    ReplyAligned L R s₀ t₀ := by
  intro s t reach f x k j hL hR r
  have eq := run_eq_of_reach obs reach
  rw [run_unfold, run_unfold, hL, hR] at eq
  have child := (vis_eq_iff carriers).mp eq |>.2 r
  cases hl : k r <;> cases hr : j r <;> rw [hl, hr] at child
  · rfl
  · obtain ⟨g, y, next, row⟩ := right hR r hr
    change ITree.ret _ = R.run _ at child
    rw [run_unfold, row] at child
    exact (ITree.ret_ne_vis _ _ _ child).elim
  · obtain ⟨g, y, next, row⟩ := left hL r hl
    change L.run _ = ITree.ret _ at child
    rw [run_unfold, row] at child
    exact (ITree.ret_ne_vis _ _ _ child.symm).elim
  · rfl

private theorem make_row (obs : L.run s₀ = R.run t₀) (aligned : ReplyAligned L R s₀ t₀)
    {C : Code} (decode : C.Value ≃ {p // PairedReach L R s₀ t₀ p}) (v : C.Value) :
    ∃ row : Row F C B, row.map (fun u => (decode u).val.1) = L (decode v).val.1 ∧
      row.map (fun u => (decode u).val.2) = R (decode v).val.2 := by
  have reach := (decode v).property
  have related := related_step (run_eq_of_reach obs reach) (aligned reach)
  generalize hL : L (decode v).val.1 = l at related
  generalize hR : R (decode v).val.2 = r at related
  cases related with
  | ret value =>
    exact ⟨.ret value, rfl, rfl⟩
  | call f x k j next =>
    have replies (r : f.replyCode.Value) : ∃ out : B.Value ⊕ C.Value,
        Sum.map id (fun u => (decode u).val.1) out = k r ∧
        Sum.map id (fun u => (decode u).val.2) out = j r := by
      have related := next r
      cases hl : k r <;> cases hr : j r <;> rw [hl, hr] at related
      · exact ⟨.inl _, rfl, congrArg Sum.inl related⟩
      · exact related.elim
      · exact related.elim
      · rename_i s t
        let pair : {p // PairedReach L R s₀ t₀ p} :=
          ⟨(s, t), .after_reply reach f x r k j hL hR hl hr⟩
        exact ⟨.inr (decode.symm pair), by simp [pair], by simp [pair]⟩
    let reply (r : f.replyCode.Value) := Classical.choose (replies r)
    have left := funext (fun r => (Classical.choose_spec (replies r)).1)
    have right := funext (fun r => (Classical.choose_spec (replies r)).2)
    exact ⟨.call f x reply, congrArg (Row.call f x) left, congrArg (Row.call f x) right⟩

theorem exists_cover (obs : L.run s₀ = R.run t₀) (aligned : ReplyAligned L R s₀ t₀) :
    Nonempty (Cover L R s₀ t₀) := by
  let _ : _root_.Finite S.Value := finiteValue S
  let _ : _root_.Finite T.Value := finiteValue T
  obtain ⟨C, ⟨decode⟩⟩ := encodeFinite {p // PairedReach L R s₀ t₀ p} ⟨(s₀, t₀), .initial⟩
  exact ⟨⟨C, decode, fun v => Classical.choose (make_row obs aligned decode v),
    fun v => (Classical.choose_spec (make_row obs aligned decode v)).1,
    fun v => (Classical.choose_spec (make_row obs aligned decode v)).2⟩⟩

theorem aligned_of_cover (C : Cover L R s₀ t₀) : ReplyAligned L R s₀ t₀ := by
  intro s t reach f x k j hL hR r
  let pair : {p // PairedReach L R s₀ t₀ p} := ⟨(s, t), reach⟩
  let v := C.decode.symm pair
  have hv : C.decode v = pair := C.decode.apply_symm_apply pair
  have left := C.left_commutes v
  have right := C.right_commutes v
  change (C.table v).map _ = L (C.decode v).val.1 at left
  change (C.table v).map _ = R (C.decode v).val.2 at right
  rw [hv] at left right
  change (C.table v).map _ = L s at left
  change (C.table v).map _ = R t at right
  rw [hL] at left
  rw [hR] at right
  generalize row : C.table v = u at left right
  cases u with
  | ret _ => cases left
  | call op arg next =>
    cases left
    cases right
    cases eq : next r <;> simp [eq]

theorem runs_eq {h : S.Value → T.Value} (comm : Commutes L R h) (s : S.Value) :
    L.run s = R.run (h s) := by
  let mapState (v : S.Large) := T.raise (h (S.raise.symm v))
  have square : (L.step >=> liftPure (Sum.map id mapState)) = (liftPure mapState >=> R.step) := by
    funext v
    obtain ⟨v, rfl⟩ := S.raise.surjective v
    have mapped : mapState (S.raise v) = T.raise (h v) := by simp [mapState]
    have row := comm v
    change (L.step (S.raise v) >>= fun result => pure (Sum.map id mapState result)) =
      (pure (mapState (S.raise v)) >>= R.step)
    rw [pure_bind, mapped, Table.step, Table.step, Equiv.symm_apply_apply, Equiv.symm_apply_apply, ← row]
    cases L v with
    | ret value =>
      change (pure (Sum.inl (B.raise value) : B.Large ⊕ S.Large) >>= _) = _
      rw [pure_bind]
      rfl
    | call f x k =>
      rw [Row.map, Row.step, Row.step, ITree.vis_bind]
      congr 1
      funext r
      change (pure (Sum.map B.raise S.raise (k r)) >>= _) = _
      rw [pure_bind]
      cases k r <;> simp [mapState] <;> rfl
  have eq := congrFun (ITree.iterate_uniformity L.step R.step mapState square) (S.raise s)
  change L.run s = (pure (mapState (S.raise s)) >>= Silmaril.Elgot.iter R.step) at eq
  simpa only [pure_bind, mapState, Equiv.symm_apply_apply, Table.run] using eq

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Proofs

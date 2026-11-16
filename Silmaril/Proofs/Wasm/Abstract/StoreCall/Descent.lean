module

public import Silmaril.Proofs.Wasm.Abstract.StoreCall.Answer
public import Silmaril.Proofs.Wasm.Abstract.BodyTrace.Faithful
public import Silmaril.Proofs.Wasm.Abstract.BodyTrace.Iter
public import Silmaril.Wasm.Abstract.Decomp.Defs
public import Silmaril.Wasm.Abstract.Recursion.Thms
public import Silmaril.Wasm.Interp.Diverge.Thms

/-!
Proofs for `Silmaril.Wasm.Abstract.StoreCall.Thms`: descents. The native
descent relation `Decomp.Reach` (a problem reaches an internal call after a
terminating prefix, the base of `Interp.EvalDiv`/`Shape.closeDL`'s descents)
is a pending call event of the exposed abstract body after call events
answered by `closedCall` (`reach_pend`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.StoreCall

open Silmaril.Wasm Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract
  Silmaril.Wasm.Abstract.Body Silmaril.Wasm.Abstract.BodyTrace Silmaril.Wasm.Binaryen
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall
  Silmaril.Elgot.ITree Silmaril.Proofs.Wasm.Abstract.StoreBody Silmaril.Proofs.Wasm.Abstract.BodyTrace

variable {H : Type}

/-! ## Pending calls through binds -/

section
universe u
variable {E : Sig.{u}} {Y Z : Type (u + 1)}

theorem pend_bind_left {t : Tree (SigEv E) Z} {k : Z → Tree (SigEv E) Y} {cs : List (Call E)}
    {m : E.Op} (h : Pend t cs m) : Pend (t >>= k) cs m := by
  induction h with
  | here ht => rw [ht, vis_bind]; exact .here rfl
  | vis ht _ ih => rw [ht, vis_bind]; exact .vis rfl ih

theorem pend_bind_right {t : Tree (SigEv E) Z} {k : Z → Tree (SigEv E) Y}
    {cs₁ cs₂ : List (Call E)} {v : Z} {m : E.Op} (h₁ : Path t cs₁ (.val v))
    (h₂ : Pend (k v) cs₂ m) : Pend (t >>= k) (cs₁ ++ cs₂) m := by
  generalize hv : (PathEnd.val v : PathEnd Z) = rv at h₁
  induction h₁ with
  | ret ht =>
    cases hv
    rw [ht, show (ret _ >>= k) = k _ from pure_bind _ k]
    exact h₂
  | div _ => cases hv
  | vis ht _ ih =>
    rw [ht, vis_bind]
    exact .vis rfl (ih hv)

end

/-! ## At the level of bodies -/

section
variable {E : Sig.{0}}

theorem pendR_bind_left {X Y : Type 1} {x : M E H X} {k : X → M E H Y} {s : St H}
    {cs : List (Call E)} {m : E.Op} (h : Pend (run' x s) cs m) : Pend (run' (x >>= k) s) cs m := by
  rw [StoreBody.run_bind]; exact pend_bind_left h

theorem pendR_bind_ok {X Y : Type 1} {x : M E H X} {k : X → M E H Y} {s : St H}
    {cs₁ cs₂ : List (Call E)} {a : X} {s₁ : St H} {m : E.Op}
    (h₁ : Path (run' x s) cs₁ (.val (.ok (a, s₁)))) (h₂ : Pend (run' (k a) s₁) cs₂ m) :
    Pend (run' (x >>= k) s) (cs₁ ++ cs₂) m := by
  rw [StoreBody.run_bind]; exact pend_bind_right h₁ h₂

theorem pendR_thenK {K : Frame → List Val → M E H Res} {x : M E H Res} {s : St H}
    {cs₁ cs₂ : List (Call E)} {s₁ : Store H} {f₁ : Frame} {stk₁ : List Val} {m : E.Op}
    (h₁ : Path (run' x s) cs₁ (endR (s₁, f₁, .normal stk₁)))
    (h₂ : Pend (run' (K f₁ stk₁) ⟨s₁⟩) cs₂ m) :
    Pend (run' (x >>= thenK K) s) (cs₁ ++ cs₂) m :=
  pendR_bind_ok h₁ h₂

end

theorem pend_callEv {x : FuncIdx} {f : Frame} {stk : List Val} {s : Store H} {a : Nat}
    {fi : FuncInst H} {ps rs : List Validation.CValType} (hfi : s.func? f x = some (a, fi))
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
    Pend (run' (callEv x f stk : M (CallSig H) H Res) ⟨s⟩) [] (a, (stk.take ps.length).reverse, s) := by
  rw [run_callEv_vis hfi hty]; exact .here rfl

theorem eval_path' {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {r : Store H × Frame × Flow} (h : Eval s f stk es r) :
    ∃ cs, Answered closedCall cs ∧
      Path (run' (denListC callEv es f stk : M (CallSig H) H Res) ⟨s⟩) cs (endR r) :=
  evalO_path (evalO_closed_iff.2 h)

/-- A returning internal call is answered by `closedCall`. -/
theorem closedCall_of_eval {s₁ s₂ : Store H} {f₁ f₂ : Frame} {x : FuncIdx} {a : Nat}
    {fi : FuncInst H} {fn : Func} {ps rs : List Validation.CValType} {fl : Flow}
    {args : List Val} (hfi : s₁.func? f₁ x = some (a, fi)) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hbody : Eval s₁ (Frame.forCall fi.module args fn.locals) [] (liftInstrs fn.body) (s₂, f₂, fl)) :
    closedCall s₁ a args (s₂, fl) := by
  rw [closedCall_eq]
  exact ⟨fi, fn, ps, rs, f₂, funcs_of_func? hfi, hcode, hty, hbody⟩

/-- **Descents are pending calls.** A native descent from a problem to an
internal call is a pending call event of the exposed body, after call events
answered by `closedCall`. -/
theorem reach_pend {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {y : (wasmOShape H).self.Op} (h : Reach s f stk es y) :
    ∃ cs, Answered closedCall cs ∧
      Pend (run' (denListC callEv es f stk : M (CallSig H) H Res) ⟨s⟩) cs (callOp y) := by
  induction h with
  | @here s s₁ f f₁ stk stk₁ x args es a fi ps rs hargs hfi hty =>
    obtain ⟨cs, hA, hp⟩ := eval_path' hargs
    refine ⟨cs ++ [], answered_append hA answered_nil, ?_⟩
    rw [denListC_cons, denC_op]
    exact pendR_bind_left (pendR_thenK hp (pend_callEv hfi hty))
  | args _ ih =>
    obtain ⟨cs, hA, hp⟩ := ih
    refine ⟨cs, hA, ?_⟩
    rw [denListC_cons, denC_op]
    exact pendR_bind_left (pendR_bind_left hp)
  | @callK s s₁ s₂ f f₁ f₂ stk stk₁ vs x args es a fi fn ps rs fl y hargs hfi hcode hty hbody hvs _ ih =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := eval_path' hargs
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih
    refine ⟨cs₁ ++ [⟨(a, (stk₁.take ps.length).reverse, s₁), (s₂, fl)⟩] ++ cs₂,
      answered_append (answered_append hA₁
        (answered_single (closedCall_of_eval hfi hcode hty hbody))) hA₂, ?_⟩
    rw [denListC_cons, denC_op]
    exact pendR_thenK (path_thenK_normal hp₁
      (path_callEv hfi hty (s₂, fl) (path_callAns_vals hvs _))) hp₂
  | @opK s s₁ s₂ f f₁ f₂ stk stk₁ stk₂ i args es y hi hargs hflat _ ih =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := eval_path' hargs
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih
    refine ⟨cs₁ ++ [] ++ cs₂, answered_append (answered_append hA₁ answered_nil) hA₂, ?_⟩
    rw [denListC_cons, denC_op]
    have hop : opC callEv i f₁ stk₁ = (flatK i f₁ stk₁ : M (CallSig H) H Res) := by
      simp only [opC, callIdx_none hi]
    exact pendR_thenK (path_thenK_normal hp₁ (hop ▸ path_flatK hflat)) hp₂
  | @block s f stk bt body es np nr y har _ ih =>
    obtain ⟨cs, hA, hp⟩ := ih
    refine ⟨cs, hA, ?_⟩
    rw [denListC_cons, denC_block]
    simp only [har]
    exact pendR_bind_left (pendR_bind_left hp)
  | @blockK s s₁ f f₁ stk vs bt body es np nr fl y har hbody hvs _ ih =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := eval_path' hbody
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih
    refine ⟨cs₁ ++ cs₂, answered_append hA₁ hA₂, ?_⟩
    rw [denListC_cons, denC_block]
    simp only [har]
    have hb := path_blockK (np := np) (nr := nr) (stk := stk) hp₁
    rw [blockFlow_of_vals hvs] at hb
    exact pendR_thenK hb hp₂
  | @loop s f stk bt body es np nr y har _ ih =>
    obtain ⟨cs, hA, hp⟩ := ih
    refine ⟨cs, hA, ?_⟩
    rw [denListC_cons, denC_loop_unfold]
    refine pendR_bind_left (pendR_bind_left ?_)
    simp only [loopBodyC, har]
    exact pendR_bind_left hp
  | @loopK s s₁ f f₁ stk vs bt body es np nr y har hbody _ ih =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := eval_path' hbody
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih
    refine ⟨cs₁ ++ cs₂, answered_append hA₁ hA₂, ?_⟩
    rw [denListC_cons, denC_loop_unfold]
    have h1 : Path (run' (loopBodyC callEv bt body ⟨(f, stk)⟩) ⟨s⟩) cs₁
        (.val (.ok (.inl ⟨(f₁, .normal (vs.take nr ++ stk.drop np))⟩, ⟨s₁⟩))) := by
      simp only [loopBodyC, har]; exact path_bind_pure hp₁ rfl
    exact pendR_thenK (path_bind_pure h1 rfl) hp₂
  | @loopBack s s₁ f f₁ stk vs bt body es np nr y har hbody _ ih =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := eval_path' hbody
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih
    refine ⟨cs₁ ++ cs₂, answered_append hA₁ hA₂, ?_⟩
    rw [denListC_cons, denC_loop_unfold, bind_assoc]
    have h1 : Path (run' (loopBodyC callEv bt body ⟨(f, stk)⟩) ⟨s⟩) cs₁
        (.val (.ok (.inr ⟨(f₁, vs.take np ++ stk.drop np)⟩, ⟨s₁⟩))) := by
      simp only [loopBodyC, har]; exact path_bind_pure hp₁ rfl
    rw [denListC_cons] at hp₂
    exact pendR_bind_ok h1 hp₂
  | cond _ ih =>
    obtain ⟨cs, hA, hp⟩ := ih
    refine ⟨cs, hA, ?_⟩
    rw [denListC_cons, denC_if]
    exact pendR_bind_left (pendR_bind_left hp)
  | @arm s s₁ f f₁ stk stk₁ cv b bt c t el es np nr y hc hb har _ ih =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := eval_path' hc
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih
    refine ⟨cs₁ ++ cs₂, answered_append hA₁ hA₂, ?_⟩
    rw [denListC_cons, denC_if, bind_assoc]
    refine pendR_bind_ok hp₁ ?_
    simp only [hb, har]
    refine pendR_bind_left (pendR_bind_left ?_)
    cases b <;> exact hp₂
  | @ifK s s₁ s₂ f f₁ f₂ stk stk₁ vs cv b bt c t el es np nr fl y hc hb har harm hvs _ ih =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := eval_path' hc
    obtain ⟨cs₂, hA₂, hp₂⟩ := eval_path' harm
    obtain ⟨cs₃, hA₃, hp₃⟩ := ih
    refine ⟨cs₁ ++ (cs₂ ++ cs₃), answered_append hA₁ (answered_append hA₂ hA₃), ?_⟩
    rw [denListC_cons, denC_if, bind_assoc]
    refine pendR_bind_ok hp₁ ?_
    simp only [hb, har]
    have harm' : Path (run' ((if b then denListC callEv t f₁ (stk₁.take np) else
        denListC callEv el f₁ (stk₁.take np)) : M (CallSig H) H Res) ⟨s₁⟩) cs₂ (endR (s₂, f₂, fl)) := by
      cases b <;> exact hp₂
    have hbk := path_blockK (np := np) (nr := nr) (stk := stk₁) harm'
    rw [blockFlow_of_vals hvs] at hbk
    exact pendR_thenK hbk hp₃

/-! ## Pending calls, inverted -/

section
universe u
variable {E : Sig.{u}} {X Y Z : Type (u + 1)}

theorem pend_bind_inv {t : Tree (SigEv E) Z} {k : Z → Tree (SigEv E) Y} {cs : List (Call E)}
    {m : E.Op} (h : Pend (t >>= k) cs m) :
    Pend t cs m ∨ ∃ cs₁ cs₂ v, cs = cs₁ ++ cs₂ ∧ Path t cs₁ (.val v) ∧ Pend (k v) cs₂ m := by
  generalize hT : t >>= k = T at h
  induction h generalizing t with
  | @here T R e k'' hv =>
    rcases cases_visible t with rfl | ⟨a, rfl⟩ | ⟨R', e', k', rfl⟩
    · rw [diverge_bind] at hT; rw [← hT] at hv; exact absurd hv.symm (vis_ne_diverge _ _)
    · rw [show (ret a >>= k) = k a from pure_bind a k] at hT
      exact .inr ⟨[], [], a, rfl, .ret rfl, .here (hT.trans hv)⟩
    · rw [vis_bind] at hT
      rw [← hT] at hv
      obtain ⟨rfl, he, -⟩ := vis_heq hv
      obtain rfl := eq_of_heq he
      exact .inl (.here rfl)
  | @vis T R e k'' n cs' m' hv hp ih =>
    rcases cases_visible t with rfl | ⟨a, rfl⟩ | ⟨R', e', k', rfl⟩
    · rw [diverge_bind] at hT; rw [← hT] at hv; exact absurd hv.symm (vis_ne_diverge _ _)
    · rw [show (ret a >>= k) = k a from pure_bind a k] at hT
      exact .inr ⟨[], _, a, rfl, .ret rfl, .vis (hT.trans hv) hp⟩
    · rw [vis_bind] at hT
      rw [← hT] at hv
      obtain ⟨rfl, he, hk⟩ := vis_heq hv
      obtain rfl := eq_of_heq he
      obtain rfl := eq_of_heq hk
      rcases ih (t := k' n) rfl with h₁ | ⟨cs₁, cs₂, v, rfl, h₁, h₂⟩
      · exact .inl (.vis rfl h₁)
      · exact .inr ⟨_ :: cs₁, cs₂, v, rfl, .vis rfl h₁, h₂⟩

/-- Pending calls of an iteration: inside one iteration, after a chain of
continuing iterations. -/
inductive IterPend (G : X → Tree (SigEv E) (Y ⊕ X)) : X → List (Call E) → E.Op → Prop
  | inside {x cs m} : Pend (G x) cs m → IterPend G x cs m
  | step {x cs₁ x' cs₂ m} : Path (G x) cs₁ (.val (.inr x')) → IterPend G x' cs₂ m →
      IterPend G x (cs₁ ++ cs₂) m

theorem pend_iterPend_base {G : X → Tree (SigEv E) (Y ⊕ X)} (L : Nat)
    (ih : ∀ (x : X) (cs : List (Call E)) (m : E.Op), cs.length < L →
      Pend (iterT G x) cs m → IterPend G x cs m)
    {x : X} {cs : List (Call E)} {m : E.Op} (hL : cs.length = L) (hs : ¬ IterSilent G x)
    (hp : Pend (iterT G x) cs m) : IterPend G x cs m := by
  rw [iter_unfold] at hp
  rcases pend_bind_inv hp with h₁ | ⟨cs₁, cs₂, v, rfl, h₁, h₂⟩
  · exact .inside h₁
  · rcases v with y | x'
    · exact absurd h₂ not_pend_ret
    · cases cs₁ with
      | nil => exact absurd ⟨x', path_nil_val h₁⟩ hs
      | cons c cs₁ =>
        refine .step h₁ (ih x' cs₂ m ?_ h₂)
        simp at hL; omega

theorem pend_iterPend_aux {G : X → Tree (SigEv E) (Y ⊕ X)} (L : Nat)
    (ih : ∀ (x : X) (cs : List (Call E)) (m : E.Op), cs.length < L →
      Pend (iterT G x) cs m → IterPend G x cs m)
    (n : Nat) : ∀ (x : X) (cs : List (Call E)) (m : E.Op), cs.length = L →
      ¬ IterSilent G ((iterNext G)^[n] x) → Pend (iterT G x) cs m → IterPend G x cs m := by
  induction n with
  | zero => exact fun x cs m hL hs hp => pend_iterPend_base L ih hL hs hp
  | succ n ihn =>
    intro x cs m hL hs hp
    by_cases hx : IterSilent G x
    · have hG := iterNext_spec hx
      have hp' : Pend (iterT G (iterNext G x)) cs m := by
        have e : (G x >>= Sum.elim pure (iterT G)) = iterT G (iterNext G x) := by
          rw [hG]; exact pure_bind _ _
        rw [iter_unfold, e] at hp
        exact hp
      have := ihn (iterNext G x) cs m hL (by rwa [Function.iterate_succ_apply] at hs) hp'
      have h1 : Path (G x) [] (.val (.inr (iterNext G x))) := .ret hG
      simpa using IterPend.step h1 this
    · exact pend_iterPend_base L ih hL hx hp

theorem pend_iterPend_len {G : X → Tree (SigEv E) (Y ⊕ X)} (L : Nat) :
    ∀ (x : X) (cs : List (Call E)) (m : E.Op), cs.length = L → Pend (iterT G x) cs m →
      IterPend G x cs m := by
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    intro x cs m h hp
    by_cases hall : ∀ n, IterSilent G ((iterNext G)^[n] x)
    · have hσ : ∀ n, G ((iterNext G)^[n] x) = ret (.inr ((iterNext G)^[n + 1] x)) := fun n => by
        rw [Function.iterate_succ_apply']; exact iterNext_spec (hall n)
      have hd := iter_eq_diverge G (fun n => (iterNext G)^[n] x) hσ
      simp only [Function.iterate_zero, id] at hd
      rw [hd] at hp
      exact absurd hp not_pend_diverge
    · push Not at hall
      obtain ⟨n, hn⟩ := hall
      exact pend_iterPend_aux L (fun x cs m hl hp => ih _ hl x cs m rfl hp) n x cs m h hn hp

theorem pend_iterPend {G : X → Tree (SigEv E) (Y ⊕ X)} {x : X} {cs : List (Call E)} {m : E.Op}
    (hp : Pend (iterT G x) cs m) : IterPend G x cs m :=
  pend_iterPend_len _ x cs m rfl hp

end

section
variable {E : Sig.{0}}

theorem pendR_bind_inv {X Y : Type 1} {x : M E H X} {k : X → M E H Y} {s : St H}
    {cs : List (Call E)} {m : E.Op} (h : Pend (run' (x >>= k) s) cs m) :
    Pend (run' x s) cs m ∨ ∃ cs₁ cs₂ a s₁, cs = cs₁ ++ cs₂ ∧
      Path (run' x s) cs₁ (.val (.ok (a, s₁))) ∧ Pend (run' (k a) s₁) cs₂ m := by
  rw [StoreBody.run_bind] at h
  rcases pend_bind_inv h with h₁ | ⟨cs₁, cs₂, v, rfl, h₁, h₂⟩
  · exact .inl h₁
  · rcases v with e | ⟨a, s₁⟩
    · exact absurd h₂ not_pend_ret
    · exact .inr ⟨cs₁, cs₂, a, s₁, rfl, h₁, h₂⟩

theorem not_pendR_pure {X : Type 1} {a : X} {s : St H} {cs : List (Call E)} {m : E.Op} :
    ¬ Pend (run' (pure a : M E H X) s) cs m := not_pend_ret

theorem not_pendR_stuck {X : Type 1} {s : St H} {cs : List (Call E)} {m : E.Op} :
    ¬ Pend (run' (stuck : M E H X) s) cs m := not_pend_diverge

theorem not_pendR_flatK {i : Instr} {f : Frame} {stk : List Val} {s : Store H}
    {cs : List (Call E)} {m : E.Op} : ¬ Pend (run' (flatK i f stk : M E H Res) ⟨s⟩) cs m := by
  rw [show run' (flatK i f stk : M E H Res) ⟨s⟩ = evalTree (evalFlat s f stk i) from
    run_flatK i f stk s]
  rcases evalFlat s f stk i with _ | ⟨s', f', fl⟩
  · exact not_pend_diverge
  · cases fl <;> exact not_pend_ret

end

theorem not_pend_callAns {f : Frame} {stk : List Val} {ps rs : List Validation.CValType}
    {ans : Store H × Flow} {s : St H} {cs : List (Call (CallSig H))} {m : (CallSig H).Op} :
    ¬ Pend (run' (callAns f stk ps rs ans) s) cs m := by
  obtain ⟨s₂, fl⟩ := ans
  intro h
  cases fl with
  | trap => rw [show run' (callAns f stk ps rs (s₂, .trap)) s = _ from run_trapS s] at h; exact not_pend_ret h
  | throw t => rw [show run' (callAns f stk ps rs (s₂, .throw t)) s = _ from run_set_pure _ _ _] at h; exact not_pend_ret h
  | normal ws => rw [show run' (callAns f stk ps rs (s₂, .normal ws)) s = _ from run_set_pure _ _ _] at h; exact not_pend_ret h
  | ret ws => rw [show run' (callAns f stk ps rs (s₂, .ret ws)) s = _ from run_set_pure _ _ _] at h; exact not_pend_ret h
  | brk k ws =>
    cases k with
    | zero => rw [show run' (callAns f stk ps rs (s₂, .brk 0 ws)) s = _ from run_set_pure _ _ _] at h; exact not_pend_ret h
    | succ k => exact not_pend_diverge h

/-- The only pending call of a call is its own event. -/
theorem pend_callEv_inv {x : FuncIdx} {f : Frame} {stk : List Val} {s : Store H}
    {cs : List (Call (CallSig H))} {m : (CallSig H).Op}
    (h : Pend (run' (callEv x f stk : M (CallSig H) H Res) ⟨s⟩) cs m) :
    ∃ a fi ps rs, s.func? f x = some (a, fi) ∧ Validation.DefType.funcType? fi.type = some (ps, rs) ∧
      cs = [] ∧ m = (a, (stk.take ps.length).reverse, s) := by
  by_cases hex : ∃ a fi ps rs, s.func? f x = some (a, fi) ∧
      Validation.DefType.funcType? fi.type = some (ps, rs)
  · obtain ⟨a, fi, ps, rs, hfi, hty⟩ := hex
    rw [run_callEv_vis hfi hty] at h
    rcases pend_vis_inv h with ⟨rfl, rfl⟩ | ⟨n, cs', rfl, hp⟩
    · exact ⟨a, fi, ps, rs, hfi, hty, rfl, rfl⟩
    · exact absurd hp not_pend_callAns
  · rw [run_callEv_none (fun a fi ps rs h1 h2 => hex ⟨a, fi, ps, rs, h1, h2⟩)] at h
    exact absurd h not_pend_diverge

/-! ## Pending calls are descents -/

/-- The descent target of a call event. -/
def opOf (m : (CallSig H).Op) : (wasmOShape H).self.Op := ⟨m.1, (m.2.1, m.2.2)⟩

/-- Pending calls of the exposed body of `es` after `closedCall` answers are descents. -/
def PRe (es : List BExpr) : Prop :=
  ∀ (s : Store H) (f : Frame) (stk : List Val) (cs : List (Call (CallSig H))) (m : (CallSig H).Op),
    Answered closedCall cs →
    Pend (run' (denListC callEv es f stk : M (CallSig H) H Res) ⟨s⟩) cs m →
    Reach s f stk es (opOf m)

theorem lans_closed (es : List BExpr) : LAns (closedCall : CallRel H) es := list_ans es

theorem eval_of_evalO {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {r : Store H × Frame × Flow} (h : EvalO closedCall s f stk es r) : Eval s f stk es r :=
  evalO_closed_iff.1 h

/-- A finished head followed by a pending call in the continuation. -/
theorem cont_pend {es : List BExpr} (hes : PRe (H := H) es) {x : M (CallSig H) H Res} {s : St H}
    {cs : List (Call (CallSig H))} {m : (CallSig H).Op} {Q : Store H × Frame × Flow → Prop}
    (hA : Answered closedCall cs) (h : Pend (run' (x >>= thenK (denListC callEv es)) s) cs m)
    (hx : ∀ cs₁ v, Answered closedCall cs₁ → Path (run' x s) cs₁ (.val v) →
      ∃ r₀, Q r₀ ∧ endR r₀ = .val v) :
    Pend (run' x s) cs m ∨
      ∃ s₁ f₁ stk₁, Q (s₁, f₁, .normal stk₁) ∧ Reach s₁ f₁ stk₁ es (opOf m) := by
  rcases pendR_bind_inv h with h₁ | ⟨cs₁, cs₂, a, t, rfl, h₁, h₂⟩
  · exact .inl h₁
  · obtain ⟨⟨s₁, f₁, fl⟩, hQ, hend⟩ := hx cs₁ _ (answered_left hA) h₁
    obtain ⟨-, rfl, rfl⟩ := endR_ok_inv hend
    by_cases hn : fl.IsNormal
    · obtain ⟨stk₁, rfl⟩ : ∃ stk₁, fl = .normal stk₁ := by
        cases fl <;> first | exact ⟨_, rfl⟩ | exact absurd hn id
      exact .inr ⟨s₁, f₁, stk₁, hQ, hes s₁ f₁ stk₁ cs₂ m (answered_right hA) h₂⟩
    · rw [thenK_pass_eq hn] at h₂
      exact absurd h₂ not_pendR_pure

theorem op_pend {i : Instr} {args es : List BExpr} (hargs : PRe (H := H) args) (hes : PRe (H := H) es)
    {s : Store H} {f : Frame} {stk : List Val} {cs : List (Call (CallSig H))}
    {m : (CallSig H).Op} (hA : Answered closedCall cs)
    (h : Pend (run' (denC callEv (.op i args) f stk >>= thenK (denListC callEv es)) ⟨s⟩) cs m) :
    Reach s f stk (.op i args :: es) (opOf m) := by
  rw [denC_op] at h
  rcases cont_pend hes hA h (opHead_ans (lans_closed args)) with h₁ |
    ⟨s₂, f₂, stk₂, hQ, hk⟩
  · rcases pendR_bind_inv h₁ with h₂ | ⟨c₁, c₂, a, t, rfl, h₂, h₃⟩
    · exact .args (hargs s f stk cs m hA h₂)
    · obtain ⟨⟨s₁, f₁, fl⟩, hev, hend⟩ := lans_closed args s f stk c₁ _ (answered_left hA) h₂
        (by simp)
      obtain ⟨-, rfl, rfl⟩ := endR_ok_inv hend
      by_cases hn : fl.IsNormal
      · obtain ⟨stk₁, rfl⟩ : ∃ stk₁, fl = .normal stk₁ := by
          cases fl <;> first | exact ⟨_, rfl⟩ | exact absurd hn id
        have h₃' : Pend (run' (opC callEv i f₁ stk₁ : M (CallSig H) H Res) ⟨s₁⟩) c₂ m := h₃
        cases hci : callIdx? i with
        | none => simp only [opC, hci] at h₃'; exact absurd h₃' not_pendR_flatK
        | some x =>
          have hix : i = .call x := by cases i <;> simp_all [callIdx?]
          subst hix
          simp only [opC, hci] at h₃'
          obtain ⟨a, fi, ps, rs, hfi, hty, -, rfl⟩ := pend_callEv_inv h₃'
          exact .here (eval_of_evalO hev) hfi hty
      · rw [thenK_pass_eq hn] at h₃
        exact absurd h₃ not_pendR_pure
  · rcases hQ with ⟨hn, -⟩ | ⟨s₁, f₁, stk₁, hev, ⟨hi, hflat⟩ | ⟨x, a, fi, ps, rs, rfl, hfi, hty, hc⟩⟩
    · exact absurd trivial hn
    · exact .opK hi (eval_of_evalO hev) hflat hk
    · rcases hc with ⟨fl, vs, hC, hvs, hr₀⟩ | ⟨-, hr₀⟩ | ⟨t, -, hr₀⟩
      · simp only [Prod.mk.injEq, Flow.normal.injEq] at hr₀
        obtain ⟨-, rfl, rfl⟩ := hr₀
        rw [closedCall_eq] at hC
        obtain ⟨fi', fn, ps', rs', f₃, hfi', hcode, hty', hbody⟩ := hC
        rw [funcs_of_func? hfi] at hfi'
        obtain rfl := Option.some.inj hfi'
        rw [hty] at hty'
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hty')
        exact .callK (eval_of_evalO hev) hfi hcode hty hbody hvs hk
      · simp at hr₀
      · simp at hr₀

theorem block_pend {bt : BlockType} {body es : List BExpr} (hbody : PRe (H := H) body) (hes : PRe (H := H) es)
    {s : Store H} {f : Frame} {stk : List Val} {cs : List (Call (CallSig H))}
    {m : (CallSig H).Op} (hA : Answered closedCall cs)
    (h : Pend (run' (denC callEv (.block bt body) f stk >>= thenK (denListC callEv es)) ⟨s⟩) cs m) :
    Reach s f stk (.block bt body :: es) (opOf m) := by
  rw [denC_block] at h
  cases har : arity f bt with
  | none =>
    simp only [har] at h
    rcases pendR_bind_inv h with h₁ | ⟨_, _, _, _, _, h₁, _⟩
    · exact absurd h₁ not_pendR_stuck
    · exact absurd (path_stuck_inv h₁) (by simp)
  | some p =>
    obtain ⟨np, nr⟩ := p
    simp only [har] at h
    rcases cont_pend (Q := BlockHead closedCall s f stk bt body) hes hA h
      (fun cs₁ v hA₁ h₁ => by
        obtain ⟨s₁, f₁, fl, hev, hend⟩ := blockArm_ans (lans_closed body) cs₁ v hA₁ h₁
        exact ⟨_, ⟨np, nr, s₁, f₁, fl, har, hev, rfl⟩, hend⟩) with h₁ |
      ⟨s₂, f₂, stk₂, ⟨np', nr', s₁, f₁, fl, har', hev, hr₀⟩, hk⟩
    · rcases pendR_bind_inv h₁ with h₂ | ⟨c₁, c₂, a, t, rfl, -, h₃⟩
      · exact .block har (hbody s f _ cs m hA h₂)
      · obtain ⟨⟨f', fl'⟩⟩ := a
        rw [blockK_eq] at h₃
        exact absurd h₃ not_pendR_pure
    · rw [har] at har'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj har')
      simp only [Prod.mk.injEq] at hr₀
      obtain ⟨rfl, rfl, hfl⟩ := hr₀
      cases fl with
      | normal vs =>
        simp only [blockFlow, Flow.normal.injEq] at hfl
        subst hfl
        exact .blockK har (eval_of_evalO hev) rfl hk
      | brk k vs =>
        cases k with
        | zero =>
          simp only [blockFlow, Flow.normal.injEq] at hfl
          subst hfl
          exact .blockK har (eval_of_evalO hev) rfl hk
        | succ k => simp [blockFlow] at hfl
      | _ => simp [blockFlow] at hfl

theorem if_pend {bt : BlockType} {c t el es : List BExpr} (hc : PRe (H := H) c)
    (ht : PRe (H := H) t) (hel : PRe (H := H) el) (hes : PRe (H := H) es)
    {s : Store H} {f : Frame} {stk : List Val} {cs : List (Call (CallSig H))}
    {m : (CallSig H).Op} (hA : Answered closedCall cs)
    (h : Pend (run' (denC callEv (.if_ bt c t el) f stk >>= thenK (denListC callEv es)) ⟨s⟩) cs m) :
    Reach s f stk (.if_ bt c t el :: es) (opOf m) := by
  rw [denC_if] at h
  rcases cont_pend (Q := IfHead closedCall s f stk bt c t el) hes hA h
    (ifHead_ans (lans_closed c) (lans_closed t) (lans_closed el)) with h₁ |
    ⟨s₂, f₂, stk₂, hQ, hk⟩
  · rcases pendR_bind_inv h₁ with h₂ | ⟨c₁, c₂, a, t', rfl, h₂, h₃⟩
    · exact .cond (hc s f stk cs m hA h₂)
    · obtain ⟨⟨s₁, f₁, fl⟩, hev, hend⟩ := lans_closed c s f stk c₁ _ (answered_left hA) h₂
        (by simp)
      obtain ⟨-, rfl, rfl⟩ := endR_ok_inv hend
      by_cases hn : fl.IsNormal
      · obtain ⟨stk₁, rfl⟩ : ∃ stk₁, fl = .normal stk₁ := by
          cases fl <;> first | exact ⟨_, rfl⟩ | exact absurd hn id
        rcases stk₁ with _ | ⟨cv, stk₁⟩
        · exact absurd h₃ not_pendR_stuck
        cases hb : truthy cv with
        | none => simp only [hb] at h₃; exact absurd h₃ not_pendR_stuck
        | some b =>
          cases har : arity f₁ bt with
          | none => simp only [hb, har] at h₃; exact absurd h₃ not_pendR_stuck
          | some p =>
            obtain ⟨np, nr⟩ := p
            simp only [hb, har] at h₃
            rcases pendR_bind_inv h₃ with h₄ | ⟨_, c₄, a', _, _, -, h₄⟩
            · refine .arm (eval_of_evalO hev) hb har ?_
              cases b
              · exact hel _ _ _ _ m (answered_right hA) h₄
              · exact ht _ _ _ _ m (answered_right hA) h₄
            · obtain ⟨⟨f', fl'⟩⟩ := a'
              rw [blockK_eq] at h₄
              exact absurd h₄ not_pendR_pure
      · have h₃' : Pend (run' (pure ⟨(f₁, fl)⟩ : M (CallSig H) H Res) ⟨s₁⟩) c₂ m := by
          cases fl <;> first | exact absurd trivial hn | exact h₃
        exact absurd h₃' not_pendR_pure
  · rcases hQ with ⟨hn, -⟩ | ⟨s₁, f₁, cv, stk₁, b, np, nr, s₃, f₃, fl, hev, hb, har, hev₂, hr₀⟩
    · exact absurd trivial hn
    · simp only [Prod.mk.injEq] at hr₀
      obtain ⟨rfl, rfl, hfl⟩ := hr₀
      cases fl with
      | normal vs =>
        simp only [blockFlow, Flow.normal.injEq] at hfl
        subst hfl
        exact .ifK (eval_of_evalO hev) hb har (eval_of_evalO hev₂) rfl hk
      | brk k vs =>
        cases k with
        | zero =>
          simp only [blockFlow, Flow.normal.injEq] at hfl
          subst hfl
          exact .ifK (eval_of_evalO hev) hb har (eval_of_evalO hev₂) rfl hk
        | succ k => simp [blockFlow] at hfl
      | _ => simp [blockFlow] at hfl

theorem loop_pend {bt : BlockType} {body es : List BExpr} (hbody : PRe (H := H) body)
    (hes : PRe (H := H) es) {s : Store H} {f : Frame} {stk : List Val}
    {cs : List (Call (CallSig H))} {m : (CallSig H).Op} (hA : Answered closedCall cs)
    (h : Pend (run' (denC callEv (.loop bt body) f stk >>= thenK (denListC callEv es)) ⟨s⟩) cs m) :
    Reach s f stk (.loop bt body :: es) (opOf m) := by
  let G := loopTree (loopBodyC (callEv (H := H)) bt body)
  have hloop : ∀ f stk s, run' (denC callEv (.loop bt body) f stk : M (CallSig H) H Res) ⟨s⟩ =
      iterT G (⟨(f, stk)⟩, ⟨s⟩) := by
    intro f stk s
    rw [denC_loop]
    exact Silmaril.Wasm.Abstract.BodyTrace.run_iter _ _ _
  -- pending calls inside the loop
  have kin : ∀ (p : ULift.{1} (Frame × List Val) × St H) cs m, IterPend G p cs m →
      Answered closedCall cs → Reach p.2.down p.1.down.1 p.1.down.2 (.loop bt body :: es) (opOf m) := by
    intro p cs m hp
    induction hp with
    | @inside p cs m hp =>
      intro hA
      rcases pend_bind_inv hp with h₁ | ⟨_, _, _, _, _, h₂⟩
      · obtain ⟨⟨f, stk⟩, ⟨s⟩⟩ := p
        have h₁' : Pend (run' (loopBodyC callEv bt body ⟨(f, stk)⟩ : M (CallSig H) H _) ⟨s⟩) cs m := h₁
        simp only [loopBodyC] at h₁'
        cases har : arity f bt with
        | none => simp only [har] at h₁'; exact absurd h₁' not_pendR_stuck
        | some q =>
          obtain ⟨np, nr⟩ := q
          simp only [har] at h₁'
          rcases pendR_bind_inv h₁' with h₂ | ⟨_, _, a, _, _, _, h₃⟩
          · exact .loop har (hbody s f _ cs m hA h₂)
          · obtain ⟨⟨f', fl'⟩⟩ := a
            rw [loopK_eq] at h₃
            exact absurd h₃ not_pendR_pure
      · exact absurd h₂ not_pend_ret
    | @step p cs₁ p' cs₂ m hp _ ih =>
      intro hA
      obtain ⟨r', hp', hm⟩ := path_map_inv hp
      have hr'' := loopEnd_inr hm.symm
      obtain ⟨np, nr, s₁, f₁, fl, har, hev, ⟨-, hr'⟩ | ⟨hnt, hr'⟩⟩ :=
        loopIter_ans (lans_closed body) (answered_left hA) hp' (by rw [hr'']; simp)
      · rw [hr''] at hr'; cases hr'
      · rw [hr''] at hr'
        simp only [PathEnd.val.injEq, Except.ok.injEq, Prod.mk.injEq] at hr'
        obtain ⟨hlo, hs⟩ := hr'
        obtain ⟨vs, rfl, hc⟩ := loopOut_inr hlo.symm
        have := ih (answered_right hA)
        rw [hc, hs] at this
        exact .loopBack har (eval_of_evalO hev) this
  -- pending calls in the continuation after the loop
  let kk : Except PUnit.{2} (Res × St H) → Tree (SigEv (CallSig H)) (Except PUnit.{2} (Res × St H)) :=
    fun r => match r with
      | .ok (a, s') => run' (thenK (denListC callEv es) a) s'
      | .error e => pure (.error e)
  have kout : ∀ (p : ULift.{1} (Frame × List Val) × St H) cs₁ (r : PathEnd (Except PUnit.{2} (Res × St H))),
      IterPath G p cs₁ r → ∀ v, r = .val v → ∀ cs₂ m, Answered closedCall (cs₁ ++ cs₂) →
      Pend (kk v) cs₂ m → Reach p.2.down p.1.down.1 p.1.down.2 (.loop bt body :: es) (opOf m) := by
    intro p cs₁ r hit
    induction hit with
    | @exit p cs y hp =>
      intro v hv cs₂ m hA h₂
      cases hv
      obtain ⟨r', hp', hm⟩ := path_map_inv hp
      rcases loopEnd_inl hm.symm with ⟨e, rfl, rfl⟩ | ⟨b, s', rfl, rfl⟩
      · exact absurd h₂ not_pend_ret
      · obtain ⟨np, nr, s₁, f₁, fl, har, hev, ⟨-, hr'⟩ | ⟨hnt, hr'⟩⟩ :=
          loopIter_ans (lans_closed body) (answered_left hA) hp' (by simp)
        · cases hr'
        · simp only [PathEnd.val.injEq, Except.ok.injEq, Prod.mk.injEq] at hr'
          obtain ⟨hlo, rfl⟩ := hr'
          rcases loopOut_inl hlo.symm with ⟨vs, rfl, rfl⟩ | ⟨k, vs, rfl, rfl⟩ | ⟨hesc, rfl⟩
          · exact .loopK har (eval_of_evalO hev) (hes s₁ f₁ _ cs₂ m (answered_right hA) h₂)
          · have h₂' : Pend (run' (pure ⟨(f₁, .brk k vs)⟩ : M (CallSig H) H Res) ⟨s₁⟩) cs₂ m := h₂
            exact absurd h₂' not_pendR_pure
          · rw [show kk (.ok (⟨(f₁, fl)⟩, ⟨s₁⟩)) = run' (pure ⟨(f₁, fl)⟩ : M (CallSig H) H Res) ⟨s₁⟩
              from congrArg (fun x => run' x ⟨s₁⟩)
                (thenK_pass_eq (Flow.not_normal_of_escapes hesc))] at h₂
            exact absurd h₂ not_pendR_pure
    | div _ => intro v hv; cases hv
    | @step p cs₁ p' cs₂' r hp _ ih =>
      intro v hv cs₂ m hA h₂
      obtain ⟨r', hp', hm⟩ := path_map_inv hp
      have hr'' := loopEnd_inr hm.symm
      obtain ⟨np, nr, s₁, f₁, fl, har, hev, ⟨-, hr'⟩ | ⟨hnt, hr'⟩⟩ :=
        loopIter_ans (lans_closed body) (answered_left (answered_left (by rw [List.append_assoc] at hA ⊢; exact hA)))
          hp' (by rw [hr'']; simp)
      · rw [hr''] at hr'; cases hr'
      · rw [hr''] at hr'
        simp only [PathEnd.val.injEq, Except.ok.injEq, Prod.mk.injEq] at hr'
        obtain ⟨hlo, hs⟩ := hr'
        obtain ⟨vs, rfl, hc⟩ := loopOut_inr hlo.symm
        have := ih v hv cs₂ m (by rw [List.append_assoc] at hA; exact answered_right hA) h₂
        rw [hc, hs] at this
        exact .loopBack har (eval_of_evalO hev) this
    | spin _ _ _ => intro v hv; cases hv
  rcases pendR_bind_inv h with h₁ | ⟨cs₁, cs₂, a, s₁, rfl, h₁, h₂⟩
  · rw [hloop] at h₁
    exact kin _ cs m (pend_iterPend h₁) hA
  · rw [hloop] at h₁
    exact kout _ cs₁ _ (path_iter_iff.1 h₁) (.ok (a, s₁)) rfl cs₂ m hA h₂

mutual

theorem tree_pend : ∀ (e : BExpr) (es : List BExpr), PRe (H := H) es →
    ∀ (s : Store H) (f : Frame) (stk : List Val) (cs : List (Call (CallSig H)))
      (m : (CallSig H).Op), Answered closedCall cs →
    Pend (run' (denC callEv e f stk >>= thenK (denListC callEv es)) ⟨s⟩) cs m →
    Reach s f stk (e :: es) (opOf m)
  | .op i args, es, hes, _, _, _, _, _, hA, h => op_pend (list_pend args) hes hA h
  | .block bt body, es, hes, _, _, _, _, _, hA, h => block_pend (list_pend body) hes hA h
  | .loop bt body, es, hes, _, _, _, _, _, hA, h => loop_pend (list_pend body) hes hA h
  | .if_ bt c t el, es, hes, _, _, _, _, _, hA, h =>
    if_pend (list_pend c) (list_pend t) (list_pend el) hes hA h
  | .tryTable .., _, _, _, _, _, _, _, _, h => by
    rw [denC.eq_def] at h
    rcases pendR_bind_inv h with h₁ | ⟨_, _, _, _, _, h₁, _⟩
    · exact absurd h₁ not_pendR_stuck
    · exact absurd (path_stuck_inv h₁) (by simp)

theorem list_pend : ∀ (es : List BExpr), PRe (H := H) es
  | [] => fun _ _ _ _ _ _ h => absurd h not_pendR_pure
  | e :: es => fun s f stk cs m hA h => by
    rw [denListC_cons] at h
    exact tree_pend e es (list_pend es) s f stk cs m hA h

end

/-! ## Infinite descent chains diverge -/

/-- An infinite chain of native descents makes the first call diverge. -/
theorem funDiv_of_chain {g : Nat → (wasmOShape H).self.Op} (hg : ∀ n, BodyReach (g n) (g (n + 1))) :
    Interp.FunDiv (g 0).2.2 (g 0).1 (g 0).2.1 := by
  let X : Interp.Problem H := fun s f stk es => ∃ n, Reach s f stk es (g n)
  have hX : X ≤ Interp.EvalDiv := by
    refine Interp.evalDiv_of_coind ?_
    rintro s f stk es ⟨n, hr⟩
    generalize hy : g n = y at hr
    cases hr with
    | @here s s₁ f f₁ stk stk₁ x args es a fi ps rs hargs hfi hty =>
      obtain ⟨fi', fn, hfi', hcode, hreach⟩ := hg n
      rw [hy] at hfi' hreach
      simp only at hfi'
      rw [funcs_of_func? hfi] at hfi'
      obtain rfl := Option.some.inj hfi'
      exact .callee hargs hfi hcode hty ⟨n + 1, hreach⟩
    | args h' => exact .args ⟨n, hy ▸ h'⟩
    | callK hargs hfi hcode hty hbody hvs h' =>
      exact .callRet hargs hfi hcode hty hbody hvs ⟨n, hy ▸ h'⟩
    | opK hi hargs hflat h' => exact .opK hi hargs hflat ⟨n, hy ▸ h'⟩
    | block har h' => exact .block har ⟨n, hy ▸ h'⟩
    | blockK har hbody hvs h' => exact .blockK har hbody hvs ⟨n, hy ▸ h'⟩
    | loop har h' => exact .loop har ⟨n, hy ▸ h'⟩
    | loopK har hbody h' => exact .loopK har hbody ⟨n, hy ▸ h'⟩
    | loopBack har hbody h' => exact .loopBack har hbody ⟨n, hy ▸ h'⟩
    | cond h' => exact .cond ⟨n, hy ▸ h'⟩
    | arm hc hb har h' => exact .arm hc hb har ⟨n, hy ▸ h'⟩
    | ifK hc hb har harm hvs h' => exact .ifK hc hb har harm hvs ⟨n, hy ▸ h'⟩
  obtain ⟨fi, fn, hfi, hcode, hreach⟩ := hg 0
  exact ⟨fi, fn, hfi, hcode, hX _ _ _ _ ⟨1, hreach⟩⟩

end Silmaril.Proofs.Wasm.Abstract.StoreCall

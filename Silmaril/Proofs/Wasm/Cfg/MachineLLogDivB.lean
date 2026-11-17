module

public import Silmaril.Proofs.Wasm.Cfg.MachineLLogDiv
public import Silmaril.Proofs.Wasm.Cfg.MachineLDivI

@[expose] public section

/-!
# Machine divergence after a log is native divergence after a log (H2, proofs)

`reach_logDiv`: a pending call reached by lifted code after a session log, whose callee diverges at
the frame, is divergence after the canonical reading of that log (`LogDivXP`).
-/

namespace Silmaril.Wasm.Cfg.Proofs.MachineLLogDivB

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.MachineL
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Abstract (EvalLXPS EvalLXPh SCall OCall LogDivXP ReachLXPS evalLXPS_canonical)
open Silmaril.Wasm.Abstract.CallXP (POut EvalOXP)
open Silmaril.Wasm.Abstract.XRecursionP (closedCallXP)
open Silmaril.Wasm.Abstract.XDivergeP (EvalDivXP FunDivXP evalDivXP_iff_step)
open Silmaril.Wasm.Cfg.Proofs.MachineLBwd (Pos lift_op lift_block lift_loop lift_if lift_try nil_inv)
open Silmaril.Wasm.Cfg.Proofs.MachineLLogDiv (ne_trap_of_blockVals)
open Silmaril.Wasm.Cfg.Proofs.MachineLClosed (logged_closed allOk_nil)

variable {H : Type}

/-- Lifted code. -/
def Lifted (es : List BExpr) : Prop := ∃ c, es = liftInstrs c

theorem lifted_cons {hd : BExpr} {tl : List BExpr} (h : Lifted (hd :: tl)) :
    (∃ e, hd = liftInstr e) ∧ Lifted tl := by
  obtain ⟨c, hc⟩ := h
  rcases c with _ | ⟨e, c⟩
  · simp [liftInstrs] at hc
  · simp only [liftInstrs, List.cons.injEq] at hc
    exact ⟨⟨e, hc.1⟩, c, hc.2⟩

theorem lifted_op {i : Instr} {args tl : List BExpr} (h : Lifted (.op i args :: tl)) :
    args = [] ∧ Lifted tl := by
  obtain ⟨⟨e, he⟩, ht⟩ := lifted_cons h
  exact ⟨(lift_op he.symm).2.1, ht⟩

theorem lifted_lift (c : List Instr) : Lifted (liftInstrs c) := ⟨c, rfl⟩

theorem nil_normal {s s' : Store H} {f f' : Frame} {N N' : List Val} {l : List (SCall H)}
    (h : EvalLXPS s f N [] l (s', f', .flow (.normal N'))) : s = s' ∧ f = f' ∧ N = N' ∧ l = [] := by
  obtain ⟨h1, h2, h3, h4⟩ := MachineLBwd.nil_inv_normal h
  exact ⟨h1.symm, h2.symm, h3.symm, h4⟩

theorem closed_nil' {s : Store H} {f : Frame} {N : List Val} :
    EvalOXP closedCallXP s f N [] (s, f, .flow (.normal N)) :=
  logged_closed .nil (allOk_nil _)

theorem canon {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {l : List (SCall H)} {s₁ : Store H} {f₁ : Frame} {fl : Flow} {vs : List Val}
    (h : EvalLXPS s f stk es l (s₁, f₁, .flow fl)) (hvs : fl.blockVals = some vs) :
    ∃ l', l = l'.map OCall.toS ∧ EvalLXPh s f stk es l' (s₁, f₁, .flow fl) :=
  evalLXPS_canonical h (ne_trap_of_blockVals hvs)

/-- **A pending call into a diverging callee, reached by lifted code, is divergence after the
canonical reading of the log.** -/
theorem reach_logDiv {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {l : List (SCall H)} {z : (Abstract.wasmOShape H).self.Op} (h : ReachLXPS s f stk es l z)
    (hY : FunDivXP z.2.2 z.1 z.2.1) :
    Lifted es → ∃ L, l = L.map OCall.toS ∧ LogDivXP s f stk es L := by
  induction h with
  | call hargs hfi hty =>
    intro hl
    obtain ⟨rfl, -⟩ := lifted_op hl
    obtain ⟨rfl, rfl, rfl, rfl⟩ := nil_normal hargs
    exact ⟨[], rfl, .div (evalDivXP_iff_step.2 (.callee closed_nil' hfi hty hY))⟩
  | ind hargs hres hfi hty hy =>
    intro hl
    obtain ⟨rfl, -⟩ := lifted_op hl
    obtain ⟨rfl, rfl, rfl, rfl⟩ := nil_normal hargs
    exact ⟨[], rfl, .div (evalDivXP_iff_step.2 (.callIndCallee closed_nil' hres hfi hty hy hY))⟩
  | ref hargs hfi hty hy =>
    intro hl
    obtain ⟨rfl, -⟩ := lifted_op hl
    obtain ⟨rfl, rfl, rfl, rfl⟩ := nil_normal hargs
    exact ⟨[], rfl, .div (evalDivXP_iff_step.2 (.callRefCallee closed_nil' hfi hty hy hY))⟩
  | args h _ =>
    intro hl
    obtain ⟨rfl, -⟩ := lifted_op hl
    cases h
  | @callK s s₁ s₂ f f₁ stk stk₁ ws x args es a fi ps rs l₁ l₂ z hargs hfi hty _ ih =>
    intro hl
    obtain ⟨rfl, ht⟩ := lifted_op hl
    obtain ⟨rfl, rfl, rfl, rfl⟩ := nil_normal hargs
    obtain ⟨L, rfl, hL⟩ := ih hY ht
    exact ⟨OCall.mk a (stk.take ps.length).reverse s (.inl ws) s₂ :: L, by simp,
      by simpa using LogDivXP.callK .nil hfi hty hL⟩
  | @indK s s₁ s₂ f f₁ stk stk₁ ws x y args es ad iv fa fi ps rs l₁ l₂ z hargs hres hfi hty hy _
      ih =>
    intro hl
    obtain ⟨rfl, ht⟩ := lifted_op hl
    obtain ⟨rfl, rfl, rfl, rfl⟩ := nil_normal hargs
    obtain ⟨L, rfl, hL⟩ := ih hY ht
    exact ⟨OCall.mk fa (stk₁.take ps.length).reverse s (.inl ws) s₂ :: L, by simp,
      by simpa using LogDivXP.indK .nil hres hfi hty hy hL⟩
  | @refK s s₁ s₂ f f₁ stk stk₁ ws y args es fa fi ps rs l₁ l₂ z hargs hfi hty hy _ ih =>
    intro hl
    obtain ⟨rfl, ht⟩ := lifted_op hl
    obtain ⟨rfl, rfl, rfl, rfl⟩ := nil_normal hargs
    obtain ⟨L, rfl, hL⟩ := ih hY ht
    exact ⟨OCall.mk fa (stk₁.take ps.length).reverse s (.inl ws) s₂ :: L, by simp,
      by simpa using LogDivXP.refK .nil hfi hty hy hL⟩
  | opK hi hargs hflat _ ih =>
    intro hl
    obtain ⟨rfl, ht⟩ := lifted_op hl
    obtain ⟨rfl, rfl, rfl, rfl⟩ := nil_normal hargs
    obtain ⟨L, rfl, hL⟩ := ih hY ht
    exact ⟨L, by simp, by simpa using LogDivXP.opK hi .nil hflat hL⟩
  | block har _ ih =>
    intro hl
    obtain ⟨⟨e, he⟩, -⟩ := lifted_cons hl
    obtain ⟨b₀, -, rfl⟩ := lift_block he.symm
    obtain ⟨L, rfl, hL⟩ := ih hY (lifted_lift b₀)
    exact ⟨L, rfl, .block har hL⟩
  | blockK har hbody hvs _ ih =>
    intro hl
    obtain ⟨-, ht⟩ := lifted_cons hl
    obtain ⟨L₁, rfl, h₁⟩ := canon hbody hvs
    obtain ⟨L₂, rfl, hL⟩ := ih hY ht
    exact ⟨L₁ ++ L₂, by simp, .blockK har h₁ hvs hL⟩
  | loop har _ ih =>
    intro hl
    obtain ⟨⟨e, he⟩, -⟩ := lifted_cons hl
    obtain ⟨b₀, -, rfl⟩ := lift_loop he.symm
    obtain ⟨L, rfl, hL⟩ := ih hY (lifted_lift b₀)
    exact ⟨L, rfl, .loop har hL⟩
  | loopK har hbody _ ih =>
    intro hl
    obtain ⟨-, ht⟩ := lifted_cons hl
    obtain ⟨L₁, rfl, h₁⟩ := canon hbody (vs := _) rfl
    obtain ⟨L₂, rfl, hL⟩ := ih hY ht
    exact ⟨L₁ ++ L₂, by simp, .loopK har h₁ hL⟩
  | loopBack har hbody _ ih =>
    intro hl
    obtain ⟨L₁, rfl, h₁⟩ := canon hbody (vs := _) rfl
    obtain ⟨L₂, rfl, hL⟩ := ih hY hl
    exact ⟨L₁ ++ L₂, by simp, .loopBack har h₁ hL⟩
  | cond h _ =>
    intro hl
    obtain ⟨⟨e, he⟩, -⟩ := lifted_cons hl
    obtain ⟨t₀, e₀, -, rfl, -, -⟩ := lift_if he.symm
    cases h
  | @arm s s₁ f f₁ stk stk₁ cv b bt c t el es np nr l₁ l₂ z hc hb har _ ih =>
    intro hl
    obtain ⟨⟨e, he⟩, -⟩ := lifted_cons hl
    obtain ⟨t₀, e₀, -, rfl, rfl, rfl⟩ := lift_if he.symm
    obtain ⟨rfl, rfl, rfl, rfl⟩ := nil_normal hc
    obtain ⟨L, rfl, hL⟩ := ih hY ⟨if b then t₀ else e₀, by cases b <;> rfl⟩
    exact ⟨L, by simp, by simpa using LogDivXP.arm .nil hb har hL⟩
  | ifK hc hb har harm hvs _ ih =>
    intro hl
    obtain ⟨⟨e, he⟩, ht⟩ := lifted_cons hl
    obtain ⟨t₀, e₀, -, rfl, rfl, rfl⟩ := lift_if he.symm
    obtain ⟨rfl, rfl, rfl, rfl⟩ := nil_normal hc
    obtain ⟨L₂, rfl, h₂⟩ := canon harm hvs
    obtain ⟨L₃, rfl, hL⟩ := ih hY ht
    exact ⟨L₂ ++ L₃, by simp, by simpa using LogDivXP.ifK .nil hb har h₂ hvs hL⟩
  | handler har _ ih =>
    intro hl
    obtain ⟨⟨e, he⟩, -⟩ := lifted_cons hl
    obtain ⟨b₀, -, rfl⟩ := lift_try he.symm
    obtain ⟨L, rfl, hL⟩ := ih hY (lifted_lift b₀)
    exact ⟨L, rfl, .handler har hL⟩
  | tryK har hbody hvs _ ih =>
    intro hl
    obtain ⟨-, ht⟩ := lifted_cons hl
    obtain ⟨L₁, rfl, h₁⟩ := canon hbody hvs
    obtain ⟨L₂, rfl, hL⟩ := ih hY ht
    exact ⟨L₁ ++ L₂, by simp, .tryK har h₁ hvs hL⟩

/-! ## A finished instruction, then divergence after a log -/

/-- **One instruction run natively to a normal end, then divergence after the rest's log**, is
divergence after both logs (the `…K` constructors, and `loopBack` for loop iterations). -/
theorem logDiv_cons {s : Store H} {f : Frame} {N : List Val} {es : List BExpr}
    {l : List (SCall H)} {r : Store H × Frame × POut} (h : EvalLXPS s f N es l r) :
    ∀ {e : Instr} {rest : List BExpr} {s₂ : Store H} {f₂ : Frame} {N₂ : List Val}
      {L₂ : List (OCall H)}, es = [liftInstr e] → r = (s₂, f₂, .flow (.normal N₂)) →
      LogDivXP s₂ f₂ N₂ rest L₂ →
      ∃ L₁, l = L₁.map OCall.toS ∧ LogDivXP s f N (liftInstr e :: rest) (L₁ ++ L₂) := by
  induction h with
  | @callRet s s₁ s₂ f f₁ stk stk₁ ws x args es a fi ps rs l₁ l₂ r hargs hfi hty hk _ _ =>
    intro e rest s₂' f₂ N₂ L₂ hes hr hL
    obtain ⟨hhd, rfl⟩ := List.cons.inj hes
    obtain ⟨-, rfl, -⟩ := lift_op hhd.symm
    rw [← hhd]
    obtain ⟨rfl, rfl, rfl, rfl⟩ := nil_normal hargs
    subst hr
    obtain ⟨rfl, rfl, h3, rfl⟩ := nil_inv hk
    simp only [POut.flow.injEq, Flow.normal.injEq] at h3; subst h3
    exact ⟨[OCall.mk a (stk.take ps.length).reverse s (.inl ws) s₂'], by simp,
      by simpa using LogDivXP.callK .nil hfi hty hL⟩
  | @indRet s s₁ s₂ f f₁ stk stk₁ ws x y args es ad iv fa fi ps rs l₁ l₂ r hargs hres hfi hty hy hk
      _ _ =>
    intro e rest s₂' f₂ N₂ L₂ hes hr hL
    obtain ⟨hhd, rfl⟩ := List.cons.inj hes
    obtain ⟨-, rfl, -⟩ := lift_op hhd.symm
    rw [← hhd]
    obtain ⟨rfl, rfl, rfl, rfl⟩ := nil_normal hargs
    subst hr
    obtain ⟨rfl, rfl, h3, rfl⟩ := nil_inv hk
    simp only [POut.flow.injEq, Flow.normal.injEq] at h3; subst h3
    exact ⟨[OCall.mk fa (stk₁.take ps.length).reverse s (.inl ws) s₂'], by simp,
      by simpa using LogDivXP.indK .nil hres hfi hty hy hL⟩
  | @refRet s s₁ s₂ f f₁ stk stk₁ ws y args es fa fi ps rs l₁ l₂ r hargs hfi hty hy hk _ _ =>
    intro e rest s₂' f₂ N₂ L₂ hes hr hL
    obtain ⟨hhd, rfl⟩ := List.cons.inj hes
    obtain ⟨-, rfl, -⟩ := lift_op hhd.symm
    rw [← hhd]
    obtain ⟨rfl, rfl, rfl, rfl⟩ := nil_normal hargs
    subst hr
    obtain ⟨rfl, rfl, h3, rfl⟩ := nil_inv hk
    simp only [POut.flow.injEq, Flow.normal.injEq] at h3; subst h3
    exact ⟨[OCall.mk fa (stk₁.take ps.length).reverse s (.inl ws) s₂'], by simp,
      by simpa using LogDivXP.refK .nil hfi hty hy hL⟩
  | opOk hi hargs hflat hk _ _ =>
    intro e rest s₂' f₂ N₂ L₂ hes hr hL
    obtain ⟨hhd, rfl⟩ := List.cons.inj hes
    obtain ⟨-, rfl, -⟩ := lift_op hhd.symm
    rw [← hhd]
    obtain ⟨rfl, rfl, rfl, rfl⟩ := nil_normal hargs
    subst hr
    obtain ⟨rfl, rfl, h3, rfl⟩ := nil_inv hk
    simp only [POut.flow.injEq, Flow.normal.injEq] at h3; subst h3
    exact ⟨[], by simp, by simpa using LogDivXP.opK hi .nil hflat hL⟩
  | blockOk har hbody hvs hk _ _ =>
    intro e rest s₂' f₂ N₂ L₂ hes hr hL
    obtain ⟨hhd, rfl⟩ := List.cons.inj hes
    rw [← hhd]
    subst hr
    obtain ⟨rfl, rfl, h3, rfl⟩ := nil_inv hk
    simp only [POut.flow.injEq, Flow.normal.injEq] at h3; subst h3
    obtain ⟨L₁, rfl, h₁⟩ := canon hbody hvs
    exact ⟨L₁, by simp, .blockK har h₁ hvs hL⟩
  | loopOk har hbody hk _ _ =>
    intro e rest s₂' f₂ N₂ L₂ hes hr hL
    obtain ⟨hhd, rfl⟩ := List.cons.inj hes
    rw [← hhd]
    subst hr
    obtain ⟨rfl, rfl, h3, rfl⟩ := nil_inv hk
    simp only [POut.flow.injEq, Flow.normal.injEq] at h3; subst h3
    obtain ⟨L₁, rfl, h₁⟩ := canon hbody (vs := _) rfl
    exact ⟨L₁, by simp, .loopK har h₁ hL⟩
  | loopBack har hbody hk _ ihk =>
    intro e rest s₂' f₂ N₂ L₂ hes hr hL
    obtain ⟨hhd, rfl⟩ := List.cons.inj hes
    obtain ⟨L₁', rfl, hL'⟩ := ihk hes hr hL
    rw [← hhd] at hL' ⊢
    obtain ⟨L₁, rfl, h₁⟩ := canon hbody (vs := _) rfl
    exact ⟨L₁ ++ L₁', by simp, by simpa using LogDivXP.loopBack har h₁ hL'⟩
  | ifOk hc hb har harm hvs hk _ _ _ =>
    intro e rest s₂' f₂ N₂ L₂ hes hr hL
    obtain ⟨hhd, rfl⟩ := List.cons.inj hes
    obtain ⟨t₀, e₀, -, rfl, rfl, rfl⟩ := lift_if hhd.symm
    rw [← hhd]
    obtain ⟨rfl, rfl, rfl, rfl⟩ := nil_normal hc
    subst hr
    obtain ⟨rfl, rfl, h3, rfl⟩ := nil_inv hk
    simp only [POut.flow.injEq, Flow.normal.injEq] at h3; subst h3
    obtain ⟨L₁, rfl, h₁⟩ := canon harm hvs
    exact ⟨L₁, by simp, by simpa using LogDivXP.ifK .nil hb har h₁ hvs hL⟩
  | tryOk har hbody hvs hk _ _ =>
    intro e rest s₂' f₂ N₂ L₂ hes hr hL
    obtain ⟨hhd, rfl⟩ := List.cons.inj hes
    rw [← hhd]
    subst hr
    obtain ⟨rfl, rfl, h3, rfl⟩ := nil_inv hk
    simp only [POut.flow.injEq, Flow.normal.injEq] at h3; subst h3
    obtain ⟨L₁, rfl, h₁⟩ := canon hbody hvs
    exact ⟨L₁, by simp, .tryK har h₁ hvs hL⟩
  | blockEsc _ _ ho _ | loopEsc _ _ ho _ | ifEsc _ _ _ _ ho _ _ | tryEsc _ _ ho _ _ =>
    intro e rest s₂' f₂ N₂ L₂ hes hr
    simp only [Prod.mk.injEq] at hr
    obtain ⟨-, -, rfl⟩ := hr
    exact absurd ho (by simp [POut.Escapes, Flow.Escapes])
  | ifAbort _ ho _ =>
    intro e rest s₂' f₂ N₂ L₂ hes hr
    simp only [Prod.mk.injEq] at hr
    obtain ⟨-, -, rfl⟩ := hr
    exact absurd trivial ho
  | argsAbort _ ho _ =>
    intro e rest s₂' f₂ N₂ L₂ hes hr
    simp only [Prod.mk.injEq] at hr
    obtain ⟨-, -, rfl⟩ := hr
    exact absurd trivial ho
  | opStop _ _ _ hfl _ =>
    intro e rest s₂' f₂ N₂ L₂ hes hr
    simp only [Prod.mk.injEq, POut.flow.injEq] at hr
    obtain ⟨-, -, rfl⟩ := hr
    exact absurd trivial hfl
  | nil => intro e rest s₂' f₂ N₂ L₂ hes; simp at hes
  | _ => intro e rest s₂' f₂ N₂ L₂ hes hr; simp at hr

/-! ## Depths -/

open Silmaril.Wasm.Cfg.Proofs.MachineLRel (MStepS DispS)
open Silmaril.Wasm.Cfg.Proofs.MachineLDivI (gotoN_lbls gotoN_entry_block)
open Silmaril.Wasm.Cfg.Proofs.Machine (lookup_eq seg_of_lookup)
open Silmaril.Wasm.Cfg.Proofs.MachineLFwd (mstep_ok)

theorem branchN_depth {body : Expr} {b : BlockId} {ls : List LFrame} {k : Nat} {L : LFrame}
    {N : List Val} {s : Store H} {f : Frame} {st' : MState H}
    (h : branchN body b ls k L N s f = some st') (hk : k < ls.length) :
    st'.lbls.length ≤ ls.length - k := by
  simp only [branchN, Option.bind_eq_some_iff] at h
  obtain ⟨a, -, h⟩ := h
  split at h
  · rw [gotoN_lbls h]; simp; omega
  · rw [gotoN_lbls h]; simp; omega

/-- **A step landing at depth at least `δ + 1` stays at depth `δ`.** -/
theorem mstepS_of_depth {body : Expr} {δ : Nat} {st st' : MState H} {l : List (SCall H)}
    (h : MStepL body st l st') (hd : δ + 1 ≤ st'.lbls.length) : MStepS body δ st l st' := by
  have hdisp : ∀ {b : BlockId} {ls : List LFrame} {r : Store H × Frame × POut},
      DispL body b ls r st' → DispS body δ b ls r st' := by
    intro b ls r hd'
    cases hd' with
    | next hg => exact .next hg (by omega)
    | br hL hg =>
      have hk := (List.getElem?_eq_some_iff.mp hL).1
      have := branchN_depth hg hk
      exact .br hL hg (by omega) (by omega)
    | catch_ hpass hL hT hc hL' hg =>
      have hk := (List.getElem?_eq_some_iff.mp hL').1
      have := branchN_depth hg hk
      exact .catch_ hpass hL hT hc hL' hg (by omega) (by omega)
    | brOut => simp at hd
    | ret => simp at hd
    | trap => simp at hd
    | raise => simp at hd
    | catchOut => simp at hd
  cases h with
  | run hb ht hr hd' => exact .run hb ht hr (hdisp hd')
  | abort hb hr hn hd' => exact .abort hb hr hn (hdisp hd')
  | enter hb ht harm hkind hr hsel har hg => exact .enter hb ht harm hkind hr hsel har hg (by omega)

/-- **The arm entry of a loop**, at the sequence at `p`, entered on `N`. -/
def ArmEntry (body : Expr) (st : MState H) : Prop :=
  ∃ (p : List SeqStep) (c : List Instr) (i : Nat) (sg : Segment) (bt : BlockType)
    (b₀ : List Instr) (sg₀ : Segment) (ls : List LFrame) (np nr : Nat) (N : List Val)
    (s : Store H) (f : Frame),
    Pos body p c i sg sg.body [.loop bt b₀] ∧ (segment b₀)[0]? = some sg₀ ∧
      FramesOk body p.reverse ls ∧ arity f bt = some (np, nr) ∧
      st = ⟨.block ⟨p ++ [(i, 0)], 0⟩, (N.take np).reverse,
        ⟨np, (N.drop np).reverse, true, false, [], bt⟩ :: ls, s, f⟩

/-- **A branch to a loop's label landing at the depth of its arm** re-enters the loop. -/
theorem branch_reentry {body : Expr} {b : BlockId} {ls : List LFrame} {k : Nat} {L : LFrame}
    {N : List Val} {s : Store H} {f : Frame} {st' : MState H}
    (hok : FramesOk body b.seq.reverse ls) (hL : ls[k]? = some L)
    (hg : branchN body b ls k L N s f = some st') (hd' : st'.lbls.length = ls.length - k)
    (hblk : ∃ b', st'.node = .block b') :
    ArmEntry body st' ∧ st'.lbls.length = (ls.drop (k + 1)).length + 1 := by
  have hk := (List.getElem?_eq_some_iff.mp hL).1
  have hLk := (List.getElem?_eq_some_iff.mp hL).2
  have hlen := Proofs.Machine.framesOk_length _ _ hok
  simp only [List.length_reverse] at hlen
  obtain ⟨x, rp', hx⟩ : ∃ x rp', b.seq.reverse.drop k = x :: rp' := by
    cases h : b.seq.reverse.drop k with
    | nil => simp at h; omega
    | cons x rp' => exact ⟨x, rp', rfl⟩
  obtain ⟨m, a⟩ := x
  have hokd := Proofs.Machine.framesOk_drop k _ _ hok
  rw [hx, List.drop_eq_getElem_cons hk, hLk] at hokd
  have hlev := Proofs.Machine.levelLoop_of_framesOk k _ _ hok hL
  obtain ⟨⟨pc, sg, t, c, hpc, hsg, ht, harm, hkind⟩, hok'⟩ := hokd
  have hrp : rp'.length = ls.length - k - 1 := by
    have := congrArg List.length hx; simp at this; omega
  simp only [branchN, Option.bind_eq_some_iff] at hg
  obtain ⟨⟨np, nr⟩, har, hg⟩ := hg
  rw [show labels body b.seq = labelsRev body b.seq.reverse from rfl,
    Proofs.Machine.labelsRev_getD k _ hx] at hg
  simp only [levelLoop, hx] at hlev
  cases hloop : L.loop
  · simp only [hloop, Bool.false_eq_true, ↓reduceIte] at hg
    have := gotoN_lbls hg
    rw [this] at hd'; simp at hd'; omega
  · simp only [hloop, ↓reduceIte] at hg
    rw [hlev, hloop] at hg
    simp only [↓reduceIte] at hg
    obtain ⟨ar, ou, lp, tt, cs, bt⟩ := L
    simp only at hloop hkind har hg
    subst hloop
    cases hkind
    rename_i b₀
    simp only [armOf] at harm
    rcases a with _ | a
    · simp only [Option.some.injEq] at harm; subst harm
      rw [show b.seq.length - k = rp'.reverse.length + 1 by simp [hrp]; omega] at hg
      obtain ⟨hlk, hst⟩ := gotoN_entry_block (p := rp'.reverse ++ [(m, 0)]) (by simpa using hg)
        hblk (by rw [hd']; simp; omega) (by simp; omega)
      obtain ⟨sg₀, hsg₀⟩ := Option.isSome_iff_exists.mp hlk
      have hcA : seqAt body (rp'.reverse ++ [(m, 0)]) = some b₀ := by
        rw [Proofs.Machine.seqAt_append]; simp [hpc, hsg, ht, armOf]
      rw [lookup_eq, hcA] at hsg₀
      simp only [Option.bind_some] at hsg₀
      refine ⟨⟨rp'.reverse, pc, m, sg, bt, b₀, sg₀, ls.drop (k + 1), np, nr,
        N.take np ++ ou.reverse, s, f, ⟨by simpa using hpc, hsg, by simp [Segment.instrs, ht],
          by simp, fun _ _ _ => by simp⟩, hsg₀, by simpa using hok', har, ?_⟩, ?_⟩
      · rw [hst]
      · rw [hst]; simp
    · simp at harm

/-- **A step landing at depth `D`, not staying at `D`, re-enters a loop** whose arm is at
depth `D`. -/
theorem reentry_data {body : Expr} {D : Nat} {st st' : MState H} {l : List (SCall H)}
    (h : MStepL body st l st') (hok : MInv body st) (hd : D ≤ st.lbls.length)
    (hd' : st'.lbls.length = D) (hnot : ¬ MStepS body D st l st')
    (hblk : ∃ b, st'.node = .block b) : ArmEntry body st' := by
  have hdisp : ∀ {b : BlockId} {ls : List LFrame} {r : Store H × Frame × POut},
      FramesOk body b.seq.reverse ls → D ≤ ls.length → DispL body b ls r st' →
      ¬ DispS body D b ls r st' → ArmEntry body st' := by
    intro b ls r hok' hdl hd₁ hnd
    cases hd₁ with
    | next hg => exact (hnd (.next hg (by omega))).elim
    | @br _ _ _ k _ _ hL hg =>
      have hk := (List.getElem?_eq_some_iff.mp hL).1
      have := branchN_depth hg hk
      by_cases hkD : k + D < ls.length
      · exact (hnd (.br hL hg hkD (by omega))).elim
      · exact (branch_reentry hok' hL hg (by omega) hblk).1
    | @catch_ _ _ _ j _ _ _ l' _ hpass hL hT hc hL' hg =>
      have hk := (List.getElem?_eq_some_iff.mp hL').1
      have := branchN_depth hg hk
      by_cases hkD : j + 1 + l'.toNat + D < ls.length
      · exact (hnd (.catch_ hpass hL hT hc hL' hg hkD (by omega))).elim
      · exact (branch_reentry hok' hL' hg (by omega) hblk).1
    | brOut => obtain ⟨_, hb⟩ := hblk; cases hb
    | ret => obtain ⟨_, hb⟩ := hblk; cases hb
    | trap => obtain ⟨_, hb⟩ := hblk; cases hb
    | raise => obtain ⟨_, hb⟩ := hblk; cases hb
    | catchOut => obtain ⟨_, hb⟩ := hblk; cases hb
  cases h with
  | run hb ht hr hd₁ => exact hdisp hok hd hd₁ (fun h' => hnot (.run hb ht hr h'))
  | abort hb hr hn hd₁ => exact hdisp hok hd hd₁ (fun h' => hnot (.abort hb hr hn h'))
  | enter hb ht harm hkind hr hsel har hg =>
    exact (hnot (.enter hb ht harm hkind hr hsel har hg (by omega))).elim

theorem mstate_eta {st : MState H} {b : BlockId} (h : st.node = .block b) :
    st = ⟨.block b, st.stk, st.lbls, st.store, st.frame⟩ := by
  cases st; simp_all

theorem mstepL_lookup {body : Expr} {b : BlockId} {stk : List Val} {ls : List LFrame}
    {s : Store H} {f : Frame} {l : List (SCall H)} {st' : MState H}
    (h : MStepL body ⟨.block b, stk, ls, s, f⟩ l st') : ∃ sg, lookup body b = some sg := by
  cases h with
  | run hb => exact ⟨_, hb⟩
  | abort hb => exact ⟨_, hb⟩
  | enter hb => exact ⟨_, hb⟩

open Silmaril.Wasm.Cfg.Proofs.MachineLDivI (StaysK mstepL_block mstepS_zero)

/-- **An infinite oracle-answered run eventually never leaves a sequence**: from some time on, every
step stays at the depth of a block (a block point), or at the depth of a loop whose arm the run
then re-enters forever (a loop arm-entry point). -/
theorem stays_point {body : Expr} {g : ℕ → MState H} (hg : ∀ n, StepK body (g n) (g (n + 1)))
    (hok : MInv body (g 0)) :
    ∃ n₀, (∃ (p : List SeqStep) (c : List Instr) (i : Nat) (sg : Segment) (stk : List Val)
        (ls : List LFrame) (s : Store H) (f : Frame), g n₀ = ⟨.block ⟨p, i⟩, stk, ls, s, f⟩ ∧
        seqAt body p = some c ∧ (segment c)[i]? = some sg ∧ FramesOk body p.reverse ls ∧
        ∀ m, n₀ ≤ m → StaysK body p.length (g m) (g (m + 1))) ∨
      (ArmEntry body (g n₀) ∧
        ∀ m, n₀ ≤ m → StaysK body ((g n₀).lbls.length - 1) (g m) (g (m + 1))) := by
  have hinv : ∀ n, MInv body (g n) := by
    intro n
    induction n with
    | zero => exact hok
    | succ n ih => obtain ⟨l, hs, -⟩ := hg n; exact mstep_ok hs ih
  have hblk : ∀ n, ∃ b, (g n).node = .block b := fun n => by
    obtain ⟨l, hs, -⟩ := hg n; exact mstepL_block hs
  have hex : ∃ v, ∃ n, (g n).lbls.length = v := ⟨_, 0, rfl⟩
  classical
  obtain ⟨m₀, hm₀⟩ := Nat.find_spec hex
  have hmin : ∀ n, Nat.find hex ≤ (g n).lbls.length := fun n => Nat.find_min' hex ⟨n, rfl⟩
  set D := Nat.find hex with hD
  have F1 : ∀ r, ¬ StaysK body D (g r) (g (r + 1)) → (g (r + 1)).lbls.length = D := by
    intro r hre
    by_contra hne
    obtain ⟨l, hs, hl⟩ := hg r
    exact hre ⟨hmin r, l, mstepS_of_depth hs (by have := hmin (r + 1); omega), hl⟩
  by_cases hQ : ∃ t, (g t).lbls.length = D ∧ ∀ r, t ≤ r → StaysK body D (g r) (g (r + 1))
  · obtain ⟨t, hdt, hst⟩ := hQ
    obtain ⟨b, hb⟩ := hblk t
    have hgt := mstate_eta hb
    have hokt : FramesOk body b.seq.reverse (g t).lbls := by
      have := hinv t; rw [hgt] at this; exact this
    have hlen := Proofs.Machine.framesOk_length _ _ hokt
    obtain ⟨l, hs, -⟩ := hg t
    rw [hgt] at hs
    obtain ⟨sg, hsg⟩ := mstepL_lookup hs
    obtain ⟨c, hc, hsgc⟩ := seg_of_lookup hsg
    refine ⟨t, .inl ⟨b.seq, c, b.idx, sg, _, _, _, _, hgt, hc, hsgc, hokt, fun m hm => ?_⟩⟩
    have : b.seq.length = D := by simp at hlen; omega
    rw [this]; exact hst m hm
  · push Not at hQ
    obtain ⟨r₁, hr₁, hre⟩ := hQ m₀ hm₀
    have hD1 : 1 ≤ D := by
      by_contra h0
      have h0' : D = 0 := by omega
      obtain ⟨l, hs, hl⟩ := hg r₁
      obtain ⟨b, hb⟩ := hblk (r₁ + 1)
      exact hre (by rw [h0']; exact ⟨Nat.zero_le _, l, mstepS_zero hs ⟨b, hb⟩, hl⟩)
    obtain ⟨l, hs, hl⟩ := hg r₁
    have hnot : ¬ MStepS body D (g r₁) l (g (r₁ + 1)) := fun h => hre ⟨hmin r₁, l, h, hl⟩
    have hdr := F1 r₁ hre
    refine ⟨r₁ + 1, .inr ⟨reentry_data hs (hinv r₁) (hmin r₁) hdr hnot (hblk _), fun m hm => ?_⟩⟩
    rw [hdr]
    obtain ⟨l', hs', hl'⟩ := hg m
    exact ⟨by have := hmin m; omega, l', mstepS_of_depth hs' (by have := hmin (m + 1); omega), hl'⟩

end Silmaril.Wasm.Cfg.Proofs.MachineLLogDivB

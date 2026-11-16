module

public import Silmaril.Proofs.Wasm.Interp.XDivCore

/-!
# Extended divergence is Core 3.0 divergence, with tail calls (proofs)

`XDivCore` for the tail checker `tExt` (`TypedT`): every call form, the three tail forms
included. The problem now runs inside a frame (`InFrame`: labels and suffixes below a frame).
A diverging tail callee: the pending `return_call_ref` leaves the labels
(`returnCallRefLabel`, `bubble`), replaces the frame by its callee
(`returnCallRefFrameAddr`), and the callee is entered: at least one Core step, into the
callee's body inside a new frame.
-/

@[expose] public section

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXT Silmaril.Wasm.Abstract.XRecursion
open Silmaril.Wasm.Abstract.XDiverge

variable {H : Type} {P : Numerics.Profile}

/-- Contexts inside a frame: labels and suffixes below a frame. -/
inductive InFrame : Sim.ActiveCtx → Prop
  | frame {n : Nat} {f : Frame} {vs : List Val} {rest : List Admin} {E : Sim.ActiveCtx} :
      InFrame (.frame n f vs rest E)
  | suffix {rest : List Admin} {E : Sim.ActiveCtx} : InFrame E → InFrame (.suffix rest E)
  | label {n : Nat} {cont : List Instr} {vs : List Val} {rest : List Admin} {E : Sim.ActiveCtx} :
      InFrame E → InFrame (.label n cont vs rest E)

/-- **A pending tail call reaches its frame**, through the labels and suffixes. -/
theorem bubble {E : Sim.ActiveCtx} (hE : InFrame E) {s : Store H} {F : Frame} {a : Nat}
    {c : Admin} (hc : c.IsReturnCallRef) : ∀ (ws : List Val) (R : List Admin),
    ∃ (Eo : Sim.ActiveCtx) (n : Nat) (fo : Frame) (vsO : List Val) (restO : List Admin)
      (pre : List Val) (R' : List Admin),
      Relation.ReflTransGen (Step P noHostX) (E.plug ⟨s, F, vals ws ++ .ref (.func a) :: c :: R⟩)
        (Eo.plug ⟨s, fo, vals vsO ++ [.frame n F (vals (pre ++ ws) ++ .ref (.func a) :: c :: R')] ++
          restO⟩) := by
  induction hE with
  | @frame n f vs rest E =>
    intro ws R
    exact ⟨E, n, f, vs, rest, [], R, by simpa [Sim.ActiveCtx.plug] using .refl⟩
  | @suffix rest E _ ih =>
    intro ws R
    obtain ⟨Eo, n, fo, vsO, restO, pre, R', h⟩ := ih ws (R ++ rest)
    exact ⟨Eo, n, fo, vsO, restO, pre, R', by simpa [Sim.ActiveCtx.plug, List.append_assoc] using h⟩
  | @label n cont vs rest E _ ih =>
    intro ws R
    obtain ⟨Eo, n', fo, vsO, restO, pre, R', h⟩ := ih (vs ++ ws) rest
    refine ⟨Eo, n', fo, vsO, restO, pre ++ vs, R', ?_⟩
    have st : Step P noHostX ⟨s, F, vals vs ++ [.label n cont (vals ws ++ .ref (.func a) :: c :: R)] ++
        rest⟩ ⟨s, F, vals (vs ++ ws) ++ .ref (.func a) :: c :: rest⟩ := by
      have e₁ : vals ws ++ .ref (.func a) :: c :: R = vals (ws ++ [.ref (.func a)]) ++ [c] ++ R := by
        simp [vals, Val.toAdmin]
      have e₂ : vals (vs ++ ws) ++ .ref (.func a) :: c :: rest =
          vals vs ++ (vals (ws ++ [.ref (.func a)]) ++ [c]) ++ rest := by
        simp [vals, Val.toAdmin]
      rw [e₁, e₂]
      exact Step.ctx vs rest (Step.returnCallRefLabel hc)
    have h' := Relation.ReflTransGen.head (E.step st) h
    simpa [Sim.ActiveCtx.plug, List.append_assoc] using h'

omit P in
/-- The head of a typed problem, as a typed problem. -/
theorem head_typedT {s : Store H} {f : Frame} {stk : List Val} {e : Binaryen.BExpr}
    {es : List Binaryen.BExpr} (ht : TypedT s f stk (e :: es)) : TypedT s f stk [e] := by
  obtain ⟨rest, labels, ret, out, hS, hc, hct, hTF, hTM⟩ := ht
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  refine ⟨expression (Binaryen.BExpr.lowerList es) ++ rest, labels, ret, o, hS,
    chk_consE.mpr ⟨o, h1, chkE_nil_selfT o⟩, ?_, hTF, hTM⟩
  rw [code_consX] at hct
  simpa only [List.append_assoc] using hct

/-- **A head tree that runs normally**: Core runs the problem to the rest, typed. -/
theorem head_stepsT {s s₂ : Store H} {f f₂ : Frame} {stk stk₂ : List Val} {e : Binaryen.BExpr}
    {es : List Binaryen.BExpr} (d : EvalOX closedCallX s f stk [e] (s₂, f₂, .normal stk₂))
    (ht : TypedT s f stk (e :: es)) :
    Steps P noHostX ⟨s, f, xcode stk (e :: es)⟩ ⟨s₂, f₂, xcode stk₂ es⟩ ∧ TypedT s₂ f₂ stk₂ es := by
  have ht₁ := head_typedT ht
  obtain ⟨-, hG⟩ := evalOX_closed_typed_goodT (P := P) d ht₁
  obtain ⟨rest, labels, ret, out, hS, hc, -, -, -⟩ := id ht₁
  obtain ⟨c', o, hrun, he, hm⟩ := run_of_wp (by simpa only [matchT_normal] using hG hS hc)
  have hc' := ends_normal hm he
  subst hc'
  refine ⟨?_, cont_typedT (P := P) oracleSoundT_typedClosed keepsTy_CX
    (evalOXT_restrictT (P := P) oracleSoundT_typedClosed keepsTy_closedCallX d ht₁) ht⟩
  have := Steps.append (expression (Binaryen.BExpr.lowerList es)) hrun
  simpa [xcode, expression, List.append_assoc] using this

/-- **A typed terminating prefix**: its Core run, and the store check after it. -/
theorem prefix_runT {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val}
    {es : List Binaryen.BExpr} (d : EvalOX closedCallX s f stk es (s₁, f₁, .normal stk₁))
    (ht : TypedT s f stk es) :
    Steps P noHostX ⟨s, f, xcode stk es⟩ ⟨s₁, f₁, vals stk₁.reverse⟩ ∧ StoreChkE tExt s₁.funcs := by
  obtain ⟨hA, hG⟩ := evalOX_closed_typed_goodT (P := P) d ht
  obtain ⟨rest, labels, ret, out, hS, hc, -, -, -⟩ := ht
  obtain ⟨c', o, hrun, he, hm⟩ := run_of_wp (by simpa only [matchT_normal] using hG hS hc)
  have hc' := ends_normal hm he
  subst hc'
  exact ⟨hrun, storeChk_inv (hA hS hc).2 hS⟩

/-- **A typed callee body is a typed problem.** -/
theorem callee_typedT {s : Store H} {a : Nat} {us : List Val} {fi : FuncInst H} {fn : Func}
    {ps rs : List Validation.CValType} (hS : StoreChkE tExt s.funcs) (hE : TypedEntry s a us)
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hn : us.length = ps.length) :
    TypedT s (Frame.forCall fi.module us fn.locals) [] (Binaryen.liftInstrs fn.body) := by
  have hct := hE fi fn hfi hcode
  obtain ⟨-, -, -, hsok, -, -, -⟩ := Sim.ContextTyped.fragment_types hct
  have hend := hS a fi fn ps rs hfi hcode hty
  obtain ⟨ob, hb, -⟩ := endsAt_eq hend
  have hlen : (Frame.forCall fi.module us fn.locals).locals.length =
      ps.length + fn.locals.length := forCall_length _ _ hn
  refine ⟨[], [rs.length], rs.length, ob, hS, by rw [hlen]; exact hb, ?_,
    fun a fi hfi => PC.StoreOk.func_tyOk hsok hfi, tyTypes_of_storeOkX hsok hfi hcode⟩
  simpa [vals, Binaryen.lowerList_liftInstrs] using hct


/-- The goal of one progress round. -/
def AdvancesT (P : Numerics.Profile) (c : Config H) : Prop :=
  ∃ (s' : Store H) (f' : Frame) (stk' : List Val) (es' : List Binaryen.BExpr) (E' : Sim.ActiveCtx),
    InFrame E' ∧ Relation.TransGen (Step P noHostX) c (E'.plug ⟨s', f', xcode stk' es'⟩) ∧
      EvalDivX s' f' stk' es' ∧ TypedT s' f' stk' es'

/-- **Progress**: a typed, extended-diverging problem takes at least one Core step, in any
context, to another one. -/
theorem progressT : ∀ (n : Nat) {s : Store H} {f : Frame} {stk : List Val}
    {es : List Binaryen.BExpr}, sizeOf es = n → EvalDivX s f stk es → TypedT s f stk es →
    ∀ E : Sim.ActiveCtx, InFrame E → AdvancesT P (E.plug ⟨s, f, xcode stk es⟩) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s f stk es hn hd ht E hE
  have hC := (oracleSoundT_typedClosed (P := P) (H := H))
  have cont : ∀ {e : Binaryen.BExpr} {es₀ : List Binaryen.BExpr} {s₂ : Store H} {f₂ : Frame}
      {stk₂ : List Val}, es = e :: es₀ → EvalOX closedCallX s f stk [e] (s₂, f₂, .normal stk₂) →
      EvalDivX s₂ f₂ stk₂ es₀ → AdvancesT P (E.plug ⟨s, f, xcode stk es⟩) := by
    rintro e es₀ s₂ f₂ stk₂ rfl d hk
    obtain ⟨hst, ht₂⟩ := head_stepsT (P := P) d ht
    rcases Relation.ReflTransGen.cases_head hst with heq | ⟨c, st, rest⟩
    · rw [heq]
      exact ih (sizeOf es₀) (by rw [← hn]; simp) rfl hk ht₂ E hE
    · exact ⟨_, _, _, _, E, hE, ActiveCtx.transGen E (Relation.TransGen.head' st rest), hk, ht₂⟩
  have callee : ∀ {s₁ : Store H} {f₁ : Frame} {ws : List Val} {a : Nat} {c : Admin}
      {R : List Admin} {fi : FuncInst H} {fn : Func} {ps rs : List Validation.CValType},
      Relation.ReflTransGen (Step P noHostX) ⟨s, f, xcode stk es⟩
        ⟨s₁, f₁, vals ws.reverse ++ [.ref (.func a), c] ++ R⟩ →
      c.IsCallRef → s₁.funcs[a]? = some fi → fi.code = .wasm fn →
      Validation.DefType.funcType? fi.type = some (ps, rs) → ps.length ≤ ws.length →
      StoreChkE tExt s₁.funcs → TypedEntry s₁ a (ws.take ps.length).reverse →
      EvalDivX s₁ (Frame.forCall fi.module (ws.take ps.length).reverse fn.locals) []
        (Binaryen.liftInstrs fn.body) →
      AdvancesT P (E.plug ⟨s, f, xcode stk es⟩) := by
    intro s₁ f₁ ws a c R fi fn ps rs hpre hcr hfi hcode hty hp hS₁ hE hd'
    refine ⟨_, _, _, _, calleeCtx E rs.length f₁ (ws.drop ps.length).reverse R, .label .frame, ?_, hd',
      callee_typedT hS₁ hE hfi hcode hty (by simp only [List.length_reverse, List.length_take]; omega)⟩
    rw [calleeCtx_plug]
    exact ActiveCtx.transGen E (Relation.TransGen.tail' hpre (enter_ref hcr hfi hcode hty hp))
  cases evalDivX_iff_step.1 hd with
  | @args _ _ _ i args es h =>
    have e : E.plug ⟨s, f, xcode stk (.op i args :: es)⟩ =
        (Sim.ActiveCtx.suffix (.plain i :: expression (Binaryen.BExpr.lowerList es)) E).plug
          ⟨s, f, xcode stk args⟩ := by
      simp only [Sim.ActiveCtx.plug, xcode, code_op]
    rw [e]
    exact ih (sizeOf args) (by rw [← hn]; simp; omega) rfl h (args_typedT ht) _ (.suffix hE)
  | opK hi hargs hflat hk => exact cont rfl (.opOk hi hargs hflat .nil) hk
  | @callRet _ s₁ s₂ _ f₁ f₂ _ stk₁ vs x args es a fi fn ps rs fl hargs hfi hcode hty hbody hvs hk =>
    have hcall : closedCallX s₁ a (stk₁.take ps.length).reverse (s₂, fl) := by
      rw [closedCallX_fixpoint]; exact ⟨fi, fn, ps, rs, f₂, funcs_of_func? hfi, hcode, hty, hbody⟩
    exact cont rfl (.callOk hargs hfi hty hcall hvs .nil) hk
  | blockK har hbody hvs hk => exact cont rfl (.blockOk har hbody hvs .nil) hk
  | loopK har hbody hk => exact cont rfl (.loopOk har hbody .nil) hk
  | ifK hc hb har harm hvs hk => exact cont rfl (.ifOk hc hb har harm hvs .nil) hk
  | @callIndRet _ s₁ s₂ _ f₁ f₂ _ stk₁ vs x y args es ad i fa fi fn ps rs fl hargs hres hfi hcode hty
      hbody hvs hk =>
    have hcall : closedCallX s₁ fa (stk₁.take ps.length).reverse (s₂, fl) := by
      rw [closedCallX_fixpoint]; exact ⟨fi, fn, ps, rs, f₂, hfi, hcode, hty, hbody⟩
    exact cont rfl (.callIndOk hargs hres hfi hty hcall hvs .nil) hk
  | @callRefRet _ s₁ s₂ _ f₁ f₂ _ stk₁ vs y args es fa fi fn ps rs fl hargs hfi hcode hty hbody hvs hk =>
    have hcall : closedCallX s₁ fa (stk₁.take ps.length).reverse (s₂, fl) := by
      rw [closedCallX_fixpoint]; exact ⟨fi, fn, ps, rs, f₂, hfi, hcode, hty, hbody⟩
    exact cont rfl (.callRefOk hargs hfi hty hcall hvs .nil) hk
  | @cond _ _ _ bt c t el es h =>
    have e : E.plug ⟨s, f, xcode stk (.if_ bt c t el :: es)⟩ =
        (Sim.ActiveCtx.suffix (.plain (.if_ bt (Binaryen.BExpr.lowerList t)
          (Binaryen.BExpr.lowerList el)) :: expression (Binaryen.BExpr.lowerList es)) E).plug
          ⟨s, f, xcode stk c⟩ := by
      simp only [Sim.ActiveCtx.plug, xcode, code_if]
    rw [e]
    exact ih (sizeOf c) (by rw [← hn]; simp; omega) rfl h (cond_typedT ht) _ (.suffix hE)
  | @block _ _ _ bt body es np nr har h =>
    obtain ⟨rest, labels, ret, out, hS, hc, -⟩ := id ht
    obtain ⟨hp, -, -⟩ := arity_block_pre har hc
    have st := step_enter (P := P) (host := noHostX) (s := s) (f := f)
      (B := Binaryen.BExpr.lowerList body) hp (step_block har) (expression (Binaryen.BExpr.lowerList es))
    refine ⟨s, f, stk.take np, body, .label nr [] (stk.drop np).reverse
      (expression (Binaryen.BExpr.lowerList es)) E, .label hE, ?_, h, block_body_typedT (P := P) har ht⟩
    have e : E.plug ⟨s, f, xcode stk (.block bt body :: es)⟩ = E.plug ⟨s, f, vals stk.reverse ++
        .plain (.block bt (Binaryen.BExpr.lowerList body)) :: expression (Binaryen.BExpr.lowerList es)⟩ := by
      rw [xcode, code_block]
    rw [e]
    simpa [Sim.ActiveCtx.plug, xcode] using Relation.TransGen.single (E.step st)
  | @loop _ _ _ bt body es np nr har h =>
    obtain ⟨rest, labels, ret, out, hS, hc, -⟩ := id ht
    obtain ⟨hp, -, -⟩ := arity_loop_pre har hc
    have st := step_enter (P := P) (host := noHostX) (s := s) (f := f)
      (B := Binaryen.BExpr.lowerList body) hp (step_loop har) (expression (Binaryen.BExpr.lowerList es))
    refine ⟨s, f, stk.take np, body, .label np [.loop bt (Binaryen.BExpr.lowerList body)]
      (stk.drop np).reverse (expression (Binaryen.BExpr.lowerList es)) E, .label hE, ?_, h,
      loop_body_typedT (P := P) har ht⟩
    have e : E.plug ⟨s, f, xcode stk (.loop bt body :: es)⟩ = E.plug ⟨s, f, vals stk.reverse ++
        .plain (.loop bt (Binaryen.BExpr.lowerList body)) :: expression (Binaryen.BExpr.lowerList es)⟩ := by
      rw [xcode, code_loop]
    rw [e]
    simpa [Sim.ActiveCtx.plug, xcode] using Relation.TransGen.single (E.step st)
  | @loopBack _ s₁ _ f₁ _ vs bt body es np nr har hbody hk =>
    obtain ⟨rest, labels, ret, out, hS, hc, -⟩ := id ht
    obtain ⟨hp, hb, -⟩ := arity_loop_pre har hc
    obtain ⟨ob, hb', -⟩ := endsAt_eq hb
    have hb'' : chkE tExt s.funcs f.module f.locals.length ret (np :: labels)
        (some (stk.take np).length) body = some ob := by rw [take_length_of_le hp]; exact hb'
    have hbt := loop_body_typedT (P := P) har ht
    obtain ⟨hA, hG⟩ := evalOX_closed_typed_goodT (P := P) hbody hbt
    obtain ⟨hok, -⟩ := hA hS hb''
    obtain ⟨n', hn', hnv⟩ := hok
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hn'
    subst hn'
    obtain ⟨c', o, hrun, he, hm⟩ := run_of_wp (by simpa only [matchT_brk] using hG hS hb'')
    have hst := tg_loop_back (P := P) (host := noHostX)
      (rest := expression (Binaryen.BExpr.lowerList es)) har hp hrun he hm hnv
    refine ⟨_, _, _, _, E, hE, ?_, hk, loop_back_typedT (P := P) hC keepsTy_CX har
      (evalOXT_restrictT (P := P) hC keepsTy_closedCallX hbody hbt) ht⟩
    have e : ∀ st', xcode st' (.loop bt body :: es) = vals st'.reverse ++
        .plain (.loop bt (Binaryen.BExpr.lowerList body)) :: expression (Binaryen.BExpr.lowerList es) :=
      fun st' => by rw [xcode, code_loop]
    rw [e, e]
    exact ActiveCtx.transGen E hst
  | @arm _ s₁ _ f₁ _ stk₁ cv b bt c t el es np nr hc hb har h =>
    obtain ⟨rest, labels, ret, out, hS, hck, -⟩ := id ht
    have htc := cond_typedT ht
    obtain ⟨hA, -⟩ := evalOX_closed_typed_goodT (P := P) hc htc
    obtain ⟨-, hp, -, -⟩ := arity_if_pre (b := b) hS (fun hS' hc' => hA hS' hc') har hck
    obtain ⟨hpre, -⟩ := prefix_runT (P := P) hc htc
    obtain ⟨c₀, rfl, rfl⟩ := truthy_eq hb
    let R := expression (Binaryen.BExpr.lowerList es)
    have hif : Step P noHostX ⟨s₁, f₁, vals (Val.i32 c₀ :: stk₁).reverse ++
        .plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el)) :: R⟩
        ⟨s₁, f₁, vals stk₁.reverse ++
          .plain (.block bt (Binaryen.BExpr.lowerList (if (c₀ != 0) then t else el))) :: R⟩ := by
      have e : vals (Val.i32 c₀ :: stk₁).reverse ++
          .plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el)) :: R =
          vals stk₁.reverse ++ [constI32 c₀,
            .plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el))] ++ R := by
        simp [vals, constI32]
      rw [e]
      by_cases h0 : c₀ = 0
      · subst h0
        simpa using Step.ctx (P := P) (host := noHostX) stk₁.reverse R
          (Step.ifFalse (s := s₁) (f := f₁) (bt := bt) (b₁ := Binaryen.BExpr.lowerList t)
            (b₂ := Binaryen.BExpr.lowerList el))
      · have h1 : (c₀ != 0) = true := by simpa using h0
        simp only [h1, ↓reduceIte]
        simpa using Step.ctx (P := P) (host := noHostX) stk₁.reverse R
          (Step.ifTrue (s := s₁) (f := f₁) (bt := bt) (b₁ := Binaryen.BExpr.lowerList t)
            (b₂ := Binaryen.BExpr.lowerList el) h0)
    have hst := step_enter (P := P) (host := noHostX) (s := s₁) (f := f₁) hp
      (step_block (B := Binaryen.BExpr.lowerList (if (c₀ != 0) then t else el)) har) R
    refine ⟨s₁, f₁, stk₁.take np, (if (c₀ != 0) then t else el),
      .label nr [] (stk₁.drop np).reverse R E, .label hE, ?_, h,
      arm_typedT (P := P) hC keepsTy_CX
        (evalOXT_restrictT (P := P) hC keepsTy_closedCallX hc htc) hb har ht⟩
    have e : E.plug ⟨s, f, xcode stk (.if_ bt c t el :: es)⟩ =
        E.plug ⟨s, f, xcode stk c ++ (.plain (.if_ bt (Binaryen.BExpr.lowerList t)
          (Binaryen.BExpr.lowerList el)) :: R)⟩ := by
      rw [xcode, code_if]
    rw [e]
    have h₁ := ActiveCtx.steps E (Steps.append (.plain (.if_ bt (Binaryen.BExpr.lowerList t)
      (Binaryen.BExpr.lowerList el)) :: R) hpre)
    have h₂ : Relation.TransGen (Step P noHostX) (E.plug ⟨s₁, f₁, vals (Val.i32 c₀ :: stk₁).reverse ++
        .plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el)) :: R⟩)
        ((Sim.ActiveCtx.label nr [] (stk₁.drop np).reverse R E).plug
          ⟨s₁, f₁, xcode (stk₁.take np) (if (c₀ != 0) then t else el)⟩) := by
      refine (Relation.TransGen.single (E.step hif)).tail ?_
      simpa [Sim.ActiveCtx.plug, xcode] using E.step hst
    exact Relation.TransGen.trans_right h₁ h₂
  | @callee _ s₁ _ f₁ _ stk₁ x args es a fi fn ps rs hargs hfi hcode hty h =>
    have hta := args_typedT ht
    obtain ⟨hpre, hS₁⟩ := prefix_runT (P := P) hargs hta
    obtain ⟨rest₀, hsite, -, -, labels, ret, o, -, hf⟩ := site_typedT (P := P) hC keepsTy_CX
      (evalOXT_restrictT (P := P) hC keepsTy_closedCallX hargs hta) ht
    obtain ⟨p, q, hpq, hp, -⟩ := flatChk_call (flatChkE_call hf)
    rw [callArity_eq hfi hty, Option.some.injEq, Prod.mk.injEq] at hpq
    obtain ⟨rfl, rfl⟩ := hpq
    obtain ⟨hx, hf'⟩ := func?_inv hfi
    let R := expression (Binaryen.BExpr.lowerList es)
    have hcl : Relation.ReflTransGen (Step P noHostX) ⟨s, f, xcode stk (.op (.call x) args :: es)⟩
        ⟨s₁, f₁, vals stk₁.reverse ++ [.ref (.func a), .callRefType fi.type] ++ R⟩ := by
      have h₁ := Steps.append (.plain (.call x) :: R) hpre
      rw [xcode, code_op]
      refine h₁.tail ?_
      simpa using Step.ctx (P := P) (host := noHostX) stk₁.reverse R (Step.call hx hf')
    exact callee hcl trivial (funcs_of_func? hfi) hcode hty hp hS₁
      (entry_of_call_siteT (P := P) hsite hfi hty hf) h
  | @callIndCallee _ s₁ _ f₁ _ stk₁ x y args es ad i fa fi fn ps rs hargs hres hfi hcode hty h =>
    have hta := args_typedT ht
    obtain ⟨hpre, hS₁⟩ := prefix_runT (P := P) hargs hta
    obtain ⟨rest₀, hsite, hTF, hTM, labels, ret, o, -, hf⟩ := site_typedT (P := P) hC keepsTy_CX
      (evalOXT_restrictT (P := P) hC keepsTy_closedCallX hargs hta) ht
    have hy := typeArity_of_indRes hres hfi hty hTF hTM (types_some_of_flatChkT hf)
    obtain ⟨hp, -⟩ := flatChk_irT (.inl ⟨_, rfl⟩) hy hf
    simp only [List.length_cons] at hp
    let R := expression (Binaryen.BExpr.lowerList es)
    have hcl : Relation.ReflTransGen (Step P noHostX)
        ⟨s, f, xcode stk (.op (.callIndirect x y) args :: es)⟩
        ⟨s₁, f₁, vals stk₁.reverse ++ [.ref (.func fa), .plain (.callRef y)] ++ R⟩ := by
      have h₁ := Steps.append (.plain (.callIndirect x y) :: R) hpre
      rw [xcode, code_op]
      refine h₁.trans ?_
      have e : vals (Val.num ⟨.int ad.intType, i⟩ :: stk₁).reverse ++ .plain (.callIndirect x y) :: R =
          vals stk₁.reverse ++ [aconst ad i, .plain (.callIndirect x y)] ++ R := by
        rw [List.reverse_cons, vals_append, Silmaril.Wasm.Abstract.CallRes.aconst_eq]; simp
      rw [e]
      exact Steps.ctx (P := P) (host := noHostX) stk₁.reverse R
        (Silmaril.Wasm.Abstract.CallRes.steps_callIndirect_func hres)
    exact callee hcl trivial hfi hcode hty (by omega) hS₁
      (entry_of_ind_siteT (P := P) hsite hres hfi hty hy hf) h
  | @callRefCallee _ s₁ _ f₁ _ stk₁ y args es fa fi fn ps rs hargs hfi hcode hty h =>
    have hta := args_typedT ht
    obtain ⟨hpre, hS₁⟩ := prefix_runT (P := P) hargs hta
    obtain ⟨rest₀, hsite, hTF, hTM, labels, ret, o, -, hf⟩ := site_typedT (P := P) hC keepsTy_CX
      (evalOXT_restrictT (P := P) hC keepsTy_closedCallX hargs hta) ht
    have hy := typeArity_of_callRef_site hsite hTM hfi hty (hTF _ _ hfi)
    obtain ⟨hp, -⟩ := flatChk_irT (.inr rfl) hy hf
    simp only [List.length_cons] at hp
    let R := expression (Binaryen.BExpr.lowerList es)
    have hcl : Relation.ReflTransGen (Step P noHostX) ⟨s, f, xcode stk (.op (.callRef y) args :: es)⟩
        ⟨s₁, f₁, vals stk₁.reverse ++ [.ref (.func fa), .plain (.callRef y)] ++ R⟩ := by
      have h₁ := Steps.append (.plain (.callRef y) :: R) hpre
      rw [xcode, code_op]
      simpa [vals, Val.toAdmin] using h₁
    exact callee hcl trivial hfi hcode hty (by omega) hS₁
      (entry_of_callRef_siteT (P := P) hsite hfi hty hy hf) h
  | @tailCallee _ s₁ _ f₁ _ stk₁ i args es fa fi fn ps rs hargs hres hfi hcode hty h =>
    have hta := args_typedT ht
    obtain ⟨hpre, hS₁⟩ := prefix_runT (P := P) hargs hta
    obtain ⟨rest₀, hsite, hTF, hTM, labels, ret, o, -, hf⟩ := site_typedT (P := P) hC keepsTy_CX
      (evalOXT_restrictT (P := P) hC keepsTy_closedCallX hargs hta) ht
    have hy := tailAnn_typed hres hsite hfi hty hTF hTM hf
    obtain ⟨hp, -, -⟩ := flatChk_tailForm (tExt_tail hres hfi hty hy) hf
    obtain ⟨c, hcr, -, hpre₂⟩ := tailRes_steps (P := P) (host := noHostX) hres
    have hEn := entry_of_tail_site (P := P) hsite hres hfi hty hy hTF hTM hf
    let R := expression (Binaryen.BExpr.lowerList es)
    let ws := (stk₁.drop (tailPop i)).reverse
    let args' := ((stk₁.drop (tailPop i)).take ps.length).reverse
    -- the run inside the caller's frame, to the pending tail call
    have h₁ : Relation.ReflTransGen (Step P noHostX) ⟨s, f, xcode stk (.op i args :: es)⟩
        ⟨s₁, f₁, vals ws ++ .ref (.func fa) :: c :: R⟩ := by
      have hA := Steps.append (.plain i :: R) hpre
      rw [xcode, code_op]
      refine hA.trans ?_
      have e : vals stk₁.reverse ++ .plain i :: R = vals ws ++
          (vals (stk₁.take (tailPop i)).reverse ++ [.plain i]) ++ R := by
        rw [rev_take_drop stk₁ (tailPop i)]; simp [ws]
      rw [e]
      simpa using Steps.ctx (P := P) (host := noHostX) ws R hpre₂
    -- up to the frame
    obtain ⟨Eo, n, fo, vsO, restO, pre, R', h₂⟩ := bubble (P := P) hE (s := s₁) (F := f₁) hcr ws R
    -- the frame is replaced by the callee call
    obtain ⟨ps', rs', hex, hpl, -⟩ := expand_of_funcType hty
    have hlen : args'.length = ps'.length := by
      simp only [args', List.length_reverse, List.length_take, List.length_drop]; omega
    have hsplit : vals (pre ++ ws) ++ .ref (.func fa) :: c :: R' = vals (pre ++
        ((stk₁.drop (tailPop i)).drop ps.length).reverse) ++ vals args' ++ [.ref (.func fa), c] ++ R' := by
      simp only [ws, args']
      rw [rev_take_drop (stk₁.drop (tailPop i)) ps.length]
      simp
    have h₃ : Step P noHostX
        (Eo.plug ⟨s₁, fo, vals vsO ++ [.frame n f₁ (vals (pre ++ ws) ++ .ref (.func fa) :: c :: R')] ++ restO⟩)
        (Eo.plug ⟨s₁, fo, vals vsO ++ (vals args' ++ [.ref (.func fa), c.retToCallIn f₁.module]) ++ restO⟩) := by
      rw [hsplit]
      exact Eo.step (Step.ctx vsO restO (Step.returnCallRefFrameAddr hcr hfi hex hlen))
    -- and the callee entered
    have hargs' : ((vsO ++ args').reverse.take ps.length).reverse = args' := by
      rw [List.reverse_append, List.take_left' (by simp [args']; omega), List.reverse_reverse]
    have hvsO : ((vsO ++ args').reverse.drop ps.length).reverse = vsO := by
      rw [List.reverse_append, List.drop_left' (by simp [args']; omega), List.reverse_reverse]
    have h₄ := enter_ref (P := P) (s := s₁) (f := fo) (stk := (vsO ++ args').reverse) (rest := restO)
      (isCallRef_retToCallIn hcr f₁.module) hfi hcode hty (by simp [args']; omega)
    rw [hargs', hvsO] at h₄
    have hlenA : args'.length = ps.length := by
      simp only [args', List.length_reverse, List.length_take, List.length_drop]; omega
    refine ⟨_, _, _, _, calleeCtx Eo rs.length fo vsO restO, .label .frame, ?_, h,
      callee_typedT hS₁ hEn hfi hcode hty hlenA⟩
    rw [calleeCtx_plug]
    have h₃' := Relation.TransGen.tail (Relation.TransGen.single h₃) (Eo.step (by simpa using h₄))
    exact Relation.TransGen.trans_right ((ActiveCtx.steps E h₁).trans h₂) (by simpa using h₃')

/-- **Extended divergence is Core 3.0 divergence, tail calls included**, for typed problems of
`tExt`-checked code inside a frame, at every profile. -/
theorem diverges_of_evalDivT {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr}
    (hd : EvalDivX s f stk es) (ht : TypedT s f stk es) {E : Sim.ActiveCtx} (hE : InFrame E) :
    Diverges P noHostX (E.plug ⟨s, f, xcode stk es⟩) := by
  refine InfiniteTrace.coinduct (fun c => ∃ (s : Store H) (f : Frame) (stk : List Val)
    (es : List Binaryen.BExpr) (E : Sim.ActiveCtx), InFrame E ∧ EvalDivX s f stk es ∧
      TypedT s f stk es ∧ Relation.ReflTransGen (Step P noHostX) c (E.plug ⟨s, f, xcode stk es⟩)) ?_
    ⟨s, f, stk, es, E, hE, hd, ht, .refl⟩
  rintro c ⟨s, f, stk, es, E, hE, hd, ht, hp⟩
  rcases Relation.ReflTransGen.cases_head hp with rfl | ⟨c₁, hstep, hp'⟩
  · obtain ⟨s', f', stk', es', E', hE', hc', hd', ht'⟩ := progressT (P := P) _ rfl hd ht E hE
    obtain ⟨c₁, hstep, hp'⟩ := Relation.TransGen.head'_iff.mp hc'
    exact ⟨c₁, hstep, s', f', stk', es', E', hE', hd', ht', hp'⟩
  · exact ⟨c₁, hstep, s, f, stk, es, E, hE, hd, ht, hp'⟩

/-- **A diverging callee body makes its typed invocation diverge in Core 3.0**, every call
form included (`tExt`-checked store), at every profile. -/
theorem invoke_diverges_of_funDivT {s : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hok : InvokeOk s a vs) (hS : StoreChkE tExt s.funcs) (hd : FunDivX s a vs) :
    Diverges P noHostX (invoke s a vs) := by
  obtain ⟨fi, fn, hfi, hcode, hdiv⟩ := hd
  obtain ⟨fi', ps, rs, hfi', he, hvs⟩ := hok
  rw [hfi] at hfi'; cases hfi'
  have hty : Validation.DefType.funcType? fi.type = some (ps.toList, rs.toList) := by
    unfold Validation.DefType.funcType?; rw [Validation.Expand.iff.mp he]
  have hlen : ps.toList.length = vs.length := hvs.length_eq.symm
  have st := enter_ref (P := P) (s := s) (f := {}) (stk := vs.reverse) (rest := [])
    (c := .callRefType fi.type) trivial hfi hcode hty (by simp [hlen])
  have hE := entry_of_invokeOk (P := P) hs ⟨fi, ps, rs, hfi, he, hvs⟩
  have htake : (vs.reverse.take ps.toList.length).reverse = vs := by
    rw [hlen, List.take_of_length_le (by simp), List.reverse_reverse]
  have hdrop : (vs.reverse.drop ps.toList.length).reverse = [] := by
    rw [hlen]; simp
  rw [htake, hdrop] at st
  have ht := callee_typedT hS hE hfi hcode hty (by rw [hlen])
  have hD := diverges_of_evalDivT (P := P) hdiv ht
    (E := calleeCtx .hole rs.toList.length {} [] []) (.label .frame)
  rw [calleeCtx_plug] at hD
  refine InfiniteTrace.fold ?_ hD
  simpa [invoke, hfi, vals, Sim.ActiveCtx.plug] using st

end Silmaril.Wasm.Interp

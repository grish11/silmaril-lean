module

public import Silmaril.Proofs.Wasm.Abstract.CallX.Expose
public import Silmaril.Proofs.Wasm.Abstract.StoreCall.Answer

/-!
Proofs for `Silmaril.Wasm.Abstract.CallX.Thms`: every finished path of the
exposed body `denListX` whose call events are answered by `C` is an `EvalOX C`
derivation (`list_ansX`). With `evalOX_path` this makes the exposure of the
extended relation exact.

The structural cases (blocks, conditionals, loops) are `StoreCall`'s, read for
`denListX`; the operator case adds the indirect, reference and tail call heads
(`HeadX`), each inverted through its resolution (`resolveInd`, `resolveTail`)
and its call event (`callAt`, `tailAt`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.CallX

open Silmaril.Wasm Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract
  Silmaril.Wasm.Abstract.Body Silmaril.Wasm.Abstract.BodyTrace Silmaril.Wasm.Binaryen
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall
  Silmaril.Wasm.Abstract.CallX Silmaril.Elgot.ITree Silmaril.Proofs.Wasm.Abstract.StoreBody
  Silmaril.Proofs.Wasm.Abstract.BodyTrace Silmaril.Proofs.Wasm.Abstract.StoreCall

variable {H : Type}

/-! ## Resolutions and call events, inverted -/

theorem resolveInd_spec {s : Store H} {f : Frame} {x : TableIdx} {y : TypeIdx} {stk : List Val}
    {p : Option Nat × List Val} (h : resolveInd s f x y stk = some p) : IndResS s f x y stk p := by
  unfold resolveInd at h
  split at h
  · rename_i hex
    cases h
    exact Classical.choose_spec hex
  · cases h

theorem resolveTail_spec {s : Store H} {f : Frame} {i : Instr} {stk : List Val}
    {o : Option (Nat × List Val)} (h : resolveTail s f i stk = some o) : TailRes s f i stk o := by
  unfold resolveTail at h
  split at h
  · rename_i hex
    cases h
    exact Classical.choose_spec hex
  · cases h

theorem tailRes_drop {s : Store H} {f : Frame} {i : Instr} {stk stk' : List Val} {fa : Nat}
    (h : TailRes s f i stk (some (fa, stk'))) : stk' = stk.drop (tailPop i) := by
  cases h <;> rfl

theorem tailFlow_notNormal (n : Nat) (fl : Flow) : ¬ (tailFlow n fl).IsNormal := by
  cases fl with
  | brk k vs => cases k <;> exact id
  | _ => exact id

theorem path_callAt_inv {fa : Nat} {f : Frame} {stk : List Val} {s : Store H}
    {cs : List (Call (CallSig H))} {e : PathEnd (Except PUnit.{2} (Res × St H))}
    (h : Path (run' (callAt fa f stk) ⟨s⟩) cs e) (he : e ≠ .div) :
    ∃ fi ps rs ans cs', s.funcs[fa]? = some fi ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) ∧
      cs = ⟨(fa, (stk.take ps.length).reverse, s), ans⟩ :: cs' ∧
      Path (run' (callAns f stk ps rs ans) ⟨s⟩) cs' e := by
  cases hfi : s.funcs[fa]? with
  | none =>
    rw [callAt, run_getState_bind] at h
    simp only [hfi] at h
    exact absurd (path_stuck_inv h) he
  | some fi =>
    cases hty : Validation.DefType.funcType? fi.type with
    | none =>
      rw [callAt, run_getState_bind] at h
      simp only [hfi, hty] at h
      exact absurd (path_stuck_inv h) he
    | some p =>
      obtain ⟨ps, rs⟩ := p
      rw [run_callAt_vis hfi hty] at h
      obtain ⟨n, cs', rfl, hp⟩ := Silmaril.Wasm.Abstract.BodyTrace.path_vis_inv h
      exact ⟨fi, ps, rs, n, cs', rfl, hty, rfl, hp⟩

theorem path_tailAt_inv {fa : Nat} {f : Frame} {stk : List Val} {s : Store H}
    {cs : List (Call (CallSig H))} {e : PathEnd (Except PUnit.{2} (Res × St H))}
    (h : Path (run' (tailAt fa f stk) ⟨s⟩) cs e) (he : e ≠ .div) :
    ∃ fi ps rs ans cs', s.funcs[fa]? = some fi ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) ∧
      cs = ⟨(fa, (stk.take ps.length).reverse, s), ans⟩ :: cs' ∧
      Path (run' (tailAns f rs ans) ⟨s⟩) cs' e := by
  cases hfi : s.funcs[fa]? with
  | none =>
    rw [tailAt, run_getState_bind] at h
    simp only [hfi] at h
    exact absurd (path_stuck_inv h) he
  | some fi =>
    cases hty : Validation.DefType.funcType? fi.type with
    | none =>
      rw [tailAt, run_getState_bind] at h
      simp only [hfi, hty] at h
      exact absurd (path_stuck_inv h) he
    | some p =>
      obtain ⟨ps, rs⟩ := p
      rw [run_tailAt_vis hfi hty] at h
      obtain ⟨n, cs', rfl, hp⟩ := Silmaril.Wasm.Abstract.BodyTrace.path_vis_inv h
      exact ⟨fi, ps, rs, n, cs', rfl, hty, rfl, hp⟩

theorem path_tailAns_inv {f : Frame} {rs : List Validation.CValType} {ans : Store H × Flow}
    {s : St H} {cs : List (Call (CallSig H))} {e : PathEnd (Except PUnit.{2} (Res × St H))}
    (h : Path (run' (tailAns f rs ans) s) cs e) (he : e ≠ .div) :
    cs = [] ∧ ((∃ vs, ans.2.retVals = some vs) ∨ ans.2.Abrupt) ∧
      e = endR (ans.1, f, tailFlow rs.length ans.2) := by
  obtain ⟨s₂, fl⟩ := ans
  cases fl with
  | trap =>
    obtain ⟨rfl, rfl⟩ := path_ret_inv (run_trapS s) h
    exact ⟨rfl, .inr trivial, rfl⟩
  | throw t =>
    obtain ⟨rfl, rfl⟩ := path_ret_inv (run_set_pure _ _ _) h
    exact ⟨rfl, .inr trivial, rfl⟩
  | normal ws =>
    obtain ⟨rfl, rfl⟩ := path_ret_inv (run_set_pure _ _ _) h
    exact ⟨rfl, .inl ⟨ws, rfl⟩, rfl⟩
  | ret ws =>
    obtain ⟨rfl, rfl⟩ := path_ret_inv (run_set_pure _ _ _) h
    exact ⟨rfl, .inl ⟨ws, rfl⟩, rfl⟩
  | brk k ws =>
    cases k with
    | zero =>
      obtain ⟨rfl, rfl⟩ := path_ret_inv (run_set_pure _ _ _) h
      exact ⟨rfl, .inl ⟨ws, rfl⟩, rfl⟩
    | succ k => exact absurd (path_stuck_inv h) he

theorem path_indEv_inv {x : TableIdx} {y : TypeIdx} {f : Frame} {stk : List Val} {s : Store H}
    {cs : List (Call (CallSig H))} {e : PathEnd (Except PUnit.{2} (Res × St H))}
    (h : Path (run' (indEv x y f stk) ⟨s⟩) cs e) (he : e ≠ .div) :
    (∃ fa stk₁, IndResS s f x y stk (some fa, stk₁) ∧ Path (run' (callAt fa f stk₁) ⟨s⟩) cs e) ∨
      (∃ stk₁, IndResS s f x y stk (none, stk₁) ∧ cs = [] ∧ e = .val (.error ⟨⟩)) := by
  rw [indEv, run_getState_bind] at h
  cases hr : resolveInd s f x y stk with
  | none =>
    simp only [hr] at h
    exact absurd (path_stuck_inv h) he
  | some p =>
    obtain ⟨o, stk₁⟩ := p
    have hs := resolveInd_spec hr
    cases o with
    | some fa =>
      simp only [hr] at h
      exact .inl ⟨fa, stk₁, hs, h⟩
    | none =>
      simp only [hr] at h
      obtain ⟨rfl, rfl⟩ := path_ret_inv (run_trapS _) h
      exact .inr ⟨stk₁, hs, rfl, rfl⟩

theorem path_refEv_inv {f : Frame} {stk : List Val} {s : Store H}
    {cs : List (Call (CallSig H))} {e : PathEnd (Except PUnit.{2} (Res × St H))}
    (h : Path (run' (refEv f stk) ⟨s⟩) cs e) (he : e ≠ .div) :
    (∃ fa stk₁, stk = .ref (.func fa) :: stk₁ ∧ Path (run' (callAt fa f stk₁) ⟨s⟩) cs e) ∨
      (∃ stk₁, stk = .ref .null :: stk₁ ∧ cs = [] ∧ e = .val (.error ⟨⟩)) := by
  unfold refEv at h
  split at h
  · exact .inl ⟨_, _, rfl, h⟩
  · obtain ⟨rfl, rfl⟩ := path_ret_inv (run_trapS _) h
    exact .inr ⟨_, rfl, rfl, rfl⟩
  · exact absurd (path_stuck_inv h) he

theorem path_tailEv_inv {i : Instr} {f : Frame} {stk : List Val} {s : Store H}
    {cs : List (Call (CallSig H))} {e : PathEnd (Except PUnit.{2} (Res × St H))}
    (h : Path (run' (tailEv i f stk) ⟨s⟩) cs e) (he : e ≠ .div) :
    (∃ fa stk₁, TailRes s f i stk (some (fa, stk₁)) ∧ Path (run' (tailAt fa f stk₁) ⟨s⟩) cs e) ∨
      (TailRes s f i stk none ∧ cs = [] ∧ e = .val (.error ⟨⟩)) := by
  rw [tailEv, run_getState_bind] at h
  cases hr : resolveTail s f i stk with
  | none =>
    simp only [hr] at h
    exact absurd (path_stuck_inv h) he
  | some o =>
    have hs := resolveTail_spec hr
    cases o with
    | some p =>
      obtain ⟨fa, stk₁⟩ := p
      simp only [hr] at h
      exact .inl ⟨fa, stk₁, hs, h⟩
    | none =>
      simp only [hr] at h
      obtain ⟨rfl, rfl⟩ := path_ret_inv (run_trapS _) h
      exact .inr ⟨hs, rfl, rfl⟩

/-! ## The converse for the extended relation -/

section
variable {C : CallRel H}

/-- Finished, answered paths of the exposed body of `es` are `EvalOX C` derivations. -/
def LAnsX (C : CallRel H) (es : List BExpr) : Prop :=
  ∀ s f stk cs e, Answered C cs →
    Path (run' (denListX es f stk : M (CallSig H) H Res) ⟨s⟩) cs e → e ≠ .div →
    ∃ r, EvalOX C s f stk es r ∧ endR r = e

/-- A head computation followed by the continuation `es`. -/
theorem cont_ansX {es : List BExpr} (hes : LAnsX C es) {x : M (CallSig H) H Res} {s : St H}
    {cs : List (Call (CallSig H))} {ee : PathEnd (Except PUnit.{2} (Res × St H))}
    {Q : Store H × Frame × Flow → Prop} (hA : Answered C cs)
    (h : Path (run' (x >>= thenK (denListX es)) s) cs ee) (he : ee ≠ .div)
    (hx : ∀ cs₁ v, Answered C cs₁ → Path (run' x s) cs₁ (.val v) →
      ∃ r₀, Q r₀ ∧ endR r₀ = .val v) :
    ∃ r₀, Q r₀ ∧ (∀ stk', r₀.2.2 = .normal stk' →
        ∃ r, EvalOX C r₀.1 r₀.2.1 stk' es r ∧ endR r = ee) ∧
      (¬ r₀.2.2.IsNormal → ee = endR r₀) := by
  rcases path_run_bind_inv h he with ⟨cs₁, cs₂, a, s₁, rfl, h₁, h₂⟩ | ⟨h₁, rfl⟩
  · obtain ⟨⟨s₀, f₀, fl⟩, hQ, hend⟩ := hx cs₁ _ (answered_left hA) h₁
    obtain ⟨-, rfl, rfl⟩ := endR_ok_inv hend
    refine ⟨_, hQ, fun stk' hn => ?_, fun hn => ?_⟩
    · simp only at hn; subst hn
      exact hes s₀ f₀ stk' cs₂ ee (answered_right hA) h₂ he
    · rw [thenK_pass_eq hn] at h₂
      obtain ⟨-, rfl⟩ := path_pure_inv h₂
      exact hend.symm
  · obtain ⟨⟨s₀, f₀, fl⟩, hQ, hend⟩ := hx cs _ hA h₁
    obtain rfl := endR_err_inv hend
    exact ⟨_, hQ, fun _ hn => (by cases hn), fun _ => hend.symm⟩

/-- The outcome of an operator on the stack `stk₁` its arguments left, every call
answered by `C`. -/
inductive HeadX (C : CallRel H) (s₁ : Store H) (f₁ : Frame) (stk₁ : List Val) :
    Instr → Store H × Frame × Flow → Prop
  | flat {i : Instr} {r₀ : Store H × Frame × Flow} (hi : ∀ x, i ≠ .call x)
      (hflat : evalFlat s₁ f₁ stk₁ i = some r₀) : HeadX C s₁ f₁ stk₁ i r₀
  | callRet {x : FuncIdx} {a : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      {s₂ : Store H} {fl : Flow} {vs : List Val}
      (hfi : s₁.func? f₁ x = some (a, fi)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hC : C s₁ a (stk₁.take ps.length).reverse (s₂, fl)) (hvs : fl.retVals = some vs) :
      HeadX C s₁ f₁ stk₁ (.call x) (s₂, f₁, .normal (vs.take rs.length ++ stk₁.drop ps.length))
  | callTrap {x : FuncIdx} {a : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      {s₂ : Store H}
      (hfi : s₁.func? f₁ x = some (a, fi)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hC : C s₁ a (stk₁.take ps.length).reverse (s₂, .trap)) :
      HeadX C s₁ f₁ stk₁ (.call x) (s₂, f₁, .trap)
  | callThrow {x : FuncIdx} {a : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      {s₂ : Store H} {t : Nat}
      (hfi : s₁.func? f₁ x = some (a, fi)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hC : C s₁ a (stk₁.take ps.length).reverse (s₂, .throw t)) :
      HeadX C s₁ f₁ stk₁ (.call x) (s₂, f₁, .throw t)
  | indRet {x : TableIdx} {y : TypeIdx} {fa : Nat} {stk' : List Val} {fi : FuncInst H}
      {ps rs : List Validation.CValType} {s₂ : Store H} {fl : Flow} {vs : List Val}
      (hres : IndResS s₁ f₁ x y stk₁ (some fa, stk')) (hfi : s₁.funcs[fa]? = some fi)
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hC : C s₁ fa (stk'.take ps.length).reverse (s₂, fl)) (hvs : fl.retVals = some vs) :
      HeadX C s₁ f₁ stk₁ (.callIndirect x y)
        (s₂, f₁, .normal (vs.take rs.length ++ stk'.drop ps.length))
  | indStop {x : TableIdx} {y : TypeIdx} {fa : Nat} {stk' : List Val} {fi : FuncInst H}
      {ps rs : List Validation.CValType} {s₂ : Store H} {fl : Flow}
      (hres : IndResS s₁ f₁ x y stk₁ (some fa, stk')) (hfi : s₁.funcs[fa]? = some fi)
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hC : C s₁ fa (stk'.take ps.length).reverse (s₂, fl)) (hfl : fl.Abrupt) :
      HeadX C s₁ f₁ stk₁ (.callIndirect x y) (s₂, f₁, fl)
  | indRes {x : TableIdx} {y : TypeIdx} {stk' : List Val}
      (hres : IndResS s₁ f₁ x y stk₁ (none, stk')) :
      HeadX C s₁ f₁ stk₁ (.callIndirect x y) (s₁, f₁, .trap)
  | refRet {y : TypeIdx} {fa : Nat} {stk' : List Val} {fi : FuncInst H}
      {ps rs : List Validation.CValType} {s₂ : Store H} {fl : Flow} {vs : List Val}
      (hstk : stk₁ = .ref (.func fa) :: stk') (hfi : s₁.funcs[fa]? = some fi)
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hC : C s₁ fa (stk'.take ps.length).reverse (s₂, fl)) (hvs : fl.retVals = some vs) :
      HeadX C s₁ f₁ stk₁ (.callRef y) (s₂, f₁, .normal (vs.take rs.length ++ stk'.drop ps.length))
  | refStop {y : TypeIdx} {fa : Nat} {stk' : List Val} {fi : FuncInst H}
      {ps rs : List Validation.CValType} {s₂ : Store H} {fl : Flow}
      (hstk : stk₁ = .ref (.func fa) :: stk') (hfi : s₁.funcs[fa]? = some fi)
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hC : C s₁ fa (stk'.take ps.length).reverse (s₂, fl)) (hfl : fl.Abrupt) :
      HeadX C s₁ f₁ stk₁ (.callRef y) (s₂, f₁, fl)
  | refNull {y : TypeIdx} {stk' : List Val} (hstk : stk₁ = .ref .null :: stk') :
      HeadX C s₁ f₁ stk₁ (.callRef y) (s₁, f₁, .trap)
  | tail {i : Instr} {fa : Nat} {stk' : List Val} {fi : FuncInst H}
      {ps rs : List Validation.CValType} {s₂ : Store H} {fl : Flow}
      (hres : TailRes s₁ f₁ i stk₁ (some (fa, stk'))) (hfi : s₁.funcs[fa]? = some fi)
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hC : C s₁ fa (stk'.take ps.length).reverse (s₂, fl))
      (hfl : (∃ vs, fl.retVals = some vs) ∨ fl.Abrupt) :
      HeadX C s₁ f₁ stk₁ i (s₂, f₁, tailFlow rs.length fl)
  | tailRes {i : Instr} (hres : TailRes s₁ f₁ i stk₁ none) :
      HeadX C s₁ f₁ stk₁ i (s₁, f₁, .trap)

/-- The outcomes of an operator node's head. -/
def OpHeadX (C : CallRel H) (s : Store H) (f : Frame) (stk : List Val) (i : Instr)
    (args : List BExpr) (r₀ : Store H × Frame × Flow) : Prop :=
  (¬ r₀.2.2.IsNormal ∧ EvalOX C s f stk args r₀) ∨
  ∃ s₁ f₁ stk₁, EvalOX C s f stk args (s₁, f₁, .normal stk₁) ∧ HeadX C s₁ f₁ stk₁ i r₀

/-- A returning call at an address, inverted. -/
theorem callAt_ans {fa : Nat} {f : Frame} {stk : List Val} {s : Store H}
    {cs : List (Call (CallSig H))} {v : Except PUnit.{2} (Res × St H)} (hA : Answered C cs)
    (h : Path (run' (callAt fa f stk) ⟨s⟩) cs (.val v)) :
    ∃ fi ps rs, s.funcs[fa]? = some fi ∧ Validation.DefType.funcType? fi.type = some (ps, rs) ∧
      ∃ s₂ fl, C s fa (stk.take ps.length).reverse (s₂, fl) ∧
        ((∃ vs, fl.retVals = some vs ∧
            .val v = endR (s₂, f, .normal (vs.take rs.length ++ stk.drop ps.length))) ∨
          (fl.Abrupt ∧ .val v = endR (s₂, f, fl))) := by
  obtain ⟨fi, ps, rs, ans, cs', hfi, hty, rfl, hp⟩ := path_callAt_inv h (by simp)
  have hAns : C s fa (stk.take ps.length).reverse ans := hA _ (List.mem_cons_self ..)
  obtain ⟨-, hcase⟩ := path_callAns_inv hp (by simp)
  obtain ⟨s₂, fl₂⟩ := ans
  refine ⟨fi, ps, rs, hfi, hty, s₂, fl₂, hAns, ?_⟩
  rcases hcase with ⟨rfl, hv⟩ | ⟨t, rfl, hv⟩ | ⟨vs, hvs, hv⟩
  · exact .inr ⟨trivial, hv⟩
  · exact .inr ⟨trivial, hv⟩
  · exact .inl ⟨vs, hvs, hv⟩

/-- The head of an operator node, on the stack its arguments left. -/
theorem headX_ans {i : Instr} {s₀ : Store H} {f₀ : Frame} {stk₁ : List Val}
    {c₂ : List (Call (CallSig H))} {v : Except PUnit.{2} (Res × St H)} (hA : Answered C c₂)
    (h : Path (run' (opCX i f₀ stk₁ : M (CallSig H) H Res) ⟨s₀⟩) c₂ (.val v)) :
    ∃ r₀, HeadX C s₀ f₀ stk₁ i r₀ ∧ endR r₀ = .val v := by
  by_cases hc : ∃ x, i = .call x
  · obtain ⟨x, rfl⟩ := hc
    obtain ⟨a', fi, ps, rs, ans, cs', hfi, hty, hc, hp⟩ := path_callEv_inv h (by simp)
    have hAns : C s₀ a' (stk₁.take ps.length).reverse ans := by
      rw [hc] at hA
      exact hA _ (List.mem_cons_self ..)
    obtain ⟨-, hcase⟩ := path_callAns_inv hp (by simp)
    obtain ⟨s₂, fl₂⟩ := ans
    rcases hcase with ⟨rfl, hv⟩ | ⟨t, rfl, hv⟩ | ⟨vs, hvs, hv⟩ <;> cases hv
    · exact ⟨_, .callTrap hfi hty hAns, rfl⟩
    · exact ⟨_, .callThrow hfi hty hAns, rfl⟩
    · exact ⟨_, .callRet hfi hty hAns hvs, rfl⟩
  have hi : ∀ x, i ≠ .call x := fun x hx => hc ⟨x, hx⟩
  cases hx : isXCall i with
  | false =>
    rw [opCX_flat hi hx] at h
    obtain ⟨r₀, hflat, -, hr₀⟩ := path_flatK_inv h (by simp)
    exact ⟨r₀, .flat hi hflat, hr₀.symm⟩
  | true =>
    obtain ⟨x, y, rfl⟩ | ⟨y, rfl⟩ | htail :
        (∃ x y, i = .callIndirect x y) ∨ (∃ y, i = .callRef y) ∨ isXTail i := by
      cases i <;> simp_all [isXCall, isXTail]
    · rcases path_indEv_inv h (by simp) with ⟨fa, stk', hres, hp⟩ | ⟨stk', hres, -, hv⟩
      · obtain ⟨fi, ps, rs, hfi, hty, s₂, fl, hC, ⟨vs, hvs, hv⟩ | ⟨hfl, hv⟩⟩ := callAt_ans hA hp
        · exact ⟨_, .indRet hres hfi hty hC hvs, hv.symm⟩
        · exact ⟨_, .indStop hres hfi hty hC hfl, hv.symm⟩
      · cases hv
        exact ⟨_, .indRes hres, rfl⟩
    · rcases path_refEv_inv h (by simp) with ⟨fa, stk', hstk, hp⟩ | ⟨stk', hstk, -, hv⟩
      · obtain ⟨fi, ps, rs, hfi, hty, s₂, fl, hC, ⟨vs, hvs, hv⟩ | ⟨hfl, hv⟩⟩ := callAt_ans hA hp
        · exact ⟨_, .refRet hstk hfi hty hC hvs, hv.symm⟩
        · exact ⟨_, .refStop hstk hfi hty hC hfl, hv.symm⟩
      · cases hv
        exact ⟨_, .refNull hstk, rfl⟩
    · rw [opCX_tail htail] at h
      rcases path_tailEv_inv h (by simp) with ⟨fa, stk', hres, hp⟩ | ⟨hres, -, hv⟩
      · obtain ⟨fi, ps, rs, ans, cs', hfi, hty, rfl, hp'⟩ := path_tailAt_inv hp (by simp)
        have hAns : C s₀ fa (stk'.take ps.length).reverse ans := hA _ (List.mem_cons_self ..)
        obtain ⟨-, hfl, hv⟩ := path_tailAns_inv hp' (by simp)
        obtain ⟨s₂, fl⟩ := ans
        exact ⟨_, .tail hres hfi hty hAns hfl, hv.symm⟩
      · cases hv
        exact ⟨_, .tailRes hres, rfl⟩

theorem opHeadX_ans {i : Instr} {args : List BExpr} (hargs : LAnsX C args) {s : Store H}
    {f : Frame} {stk : List Val} (cs₁ : List (Call (CallSig H)))
    (v : Except PUnit.{2} (Res × St H)) (hA : Answered C cs₁)
    (h : Path (run' (denListX args f stk >>= thenK (opCX i) : M (CallSig H) H Res)
      ⟨s⟩) cs₁ (.val v)) :
    ∃ r₀, OpHeadX C s f stk i args r₀ ∧ endR r₀ = .val v := by
  rcases path_run_bind_inv h (by simp) with ⟨c₁, c₂, a, s₁, rfl, h₁, h₂⟩ | ⟨h₁, hv⟩
  · obtain ⟨⟨s₀, f₀, fl⟩, hev, hend⟩ := hargs s f stk c₁ _ (answered_left hA) h₁ (by simp)
    obtain ⟨hnt, rfl, rfl⟩ := endR_ok_inv hend
    by_cases hn : fl.IsNormal
    · obtain ⟨stk₁, rfl⟩ : ∃ stk₁, fl = .normal stk₁ := by
        cases fl <;> first | exact ⟨_, rfl⟩ | exact absurd hn id
      have h₂' : Path (run' (opCX i f₀ stk₁ : M (CallSig H) H Res) ⟨s₀⟩) c₂ (.val v) := h₂
      obtain ⟨r₀, hhead, hr₀⟩ := headX_ans (answered_right hA) h₂'
      exact ⟨r₀, .inr ⟨s₀, f₀, stk₁, hev, hhead⟩, hr₀⟩
    · rw [thenK_pass_eq hn] at h₂
      obtain ⟨-, hv⟩ := path_pure_inv h₂
      cases hv
      exact ⟨_, .inl ⟨hn, hev⟩, hend⟩
  · obtain ⟨⟨s₀, f₀, fl⟩, hev, hend⟩ := hargs s f stk cs₁ _ hA h₁ (by simp)
    obtain rfl := endR_err_inv hend
    cases hv
    exact ⟨_, .inl ⟨Flow.notNormal_trap, hev⟩, hend⟩

/-- An `op` tree with its continuation. -/
theorem op_ansX {i : Instr} {args es : List BExpr} (hargs : LAnsX C args) (hes : LAnsX C es)
    {s : Store H} {f : Frame} {stk : List Val} {cs : List (Call (CallSig H))}
    {ee : PathEnd (Except PUnit.{2} (Res × St H))} (hA : Answered C cs)
    (h : Path (run' (denX (.op i args) f stk >>= thenK (denListX es)) ⟨s⟩) cs ee)
    (he : ee ≠ .div) : ∃ r, EvalOX C s f stk (.op i args :: es) r ∧ endR r = ee := by
  rw [denX_op] at h
  obtain ⟨r₀, hQ, hnorm, hnon⟩ := cont_ansX hes hA h he (opHeadX_ans hargs)
  rcases hQ with ⟨hn, hev⟩ | ⟨s₁, f₁, stk₁, hev, hhead⟩
  · exact ⟨r₀, .argsAbort hev hn, (hnon hn).symm⟩
  cases hhead with
  | @flat i r₀ hi hflat =>
    obtain ⟨s₂, f₂, fl₂⟩ := r₀
    by_cases hn : fl₂.IsNormal
    · obtain ⟨stk₂, rfl⟩ : ∃ stk₂, fl₂ = .normal stk₂ := by
        cases fl₂ <;> first | exact ⟨_, rfl⟩ | exact absurd hn id
      obtain ⟨r, hk, hr⟩ := hnorm stk₂ rfl
      exact ⟨r, .opOk hi hev hflat hk, hr⟩
    · exact ⟨_, .opStop hi hev hflat hn, (hnon hn).symm⟩
  | callRet hfi hty hC hvs =>
    obtain ⟨r, hk, hr⟩ := hnorm _ rfl
    exact ⟨r, .callOk hev hfi hty hC hvs hk, hr⟩
  | callTrap hfi hty hC =>
    exact ⟨_, .callTrap hev hfi hty hC, (hnon Flow.notNormal_trap).symm⟩
  | callThrow hfi hty hC =>
    exact ⟨_, .callThrow hev hfi hty hC, (hnon Flow.notNormal_throw).symm⟩
  | indRet hres hfi hty hC hvs =>
    obtain ⟨ad, j, rfl, hres⟩ := hres
    obtain ⟨r, hk, hr⟩ := hnorm _ rfl
    exact ⟨r, .callIndOk hev hres hfi hty hC hvs hk, hr⟩
  | @indStop x y fa stk' fi ps rs s₂ fl hres hfi hty hC hfl =>
    obtain ⟨ad, j, rfl, hres⟩ := hres
    have hn : ¬ fl.IsNormal := by cases fl <;> first | exact absurd hfl id | exact id
    exact ⟨_, .callIndStop hev hres hfi hty hC hfl, (hnon hn).symm⟩
  | indRes hres =>
    obtain ⟨ad, j, rfl, hres⟩ := hres
    exact ⟨_, .callIndRes hev hres, (hnon Flow.notNormal_trap).symm⟩
  | refRet hstk hfi hty hC hvs =>
    subst hstk
    obtain ⟨r, hk, hr⟩ := hnorm _ rfl
    exact ⟨r, .callRefOk hev hfi hty hC hvs hk, hr⟩
  | @refStop y fa stk' fi ps rs s₂ fl hstk hfi hty hC hfl =>
    subst hstk
    have hn : ¬ fl.IsNormal := by cases fl <;> first | exact absurd hfl id | exact id
    exact ⟨_, .callRefStop hev hfi hty hC hfl, (hnon hn).symm⟩
  | refNull hstk =>
    subst hstk
    exact ⟨_, .callRefNull hev, (hnon Flow.notNormal_trap).symm⟩
  | @tail i fa stk' fi ps rs s₂ fl hres hfi hty hC hfl =>
    obtain rfl := tailRes_drop hres
    exact ⟨_, .tail hev hres hfi hty hC hfl, (hnon (tailFlow_notNormal _ _)).symm⟩
  | tailRes hres =>
    exact ⟨_, .tailRes hev hres, (hnon Flow.notNormal_trap).symm⟩

end

section
variable {C : CallRel H}

def BlockHeadX (C : CallRel H) (s : Store H) (f : Frame) (stk : List Val) (bt : BlockType)
    (body : List BExpr) (r₀ : Store H × Frame × Flow) : Prop :=
  ∃ np nr s₁ f₁ fl, arity f bt = some (np, nr) ∧ EvalOX C s f (stk.take np) body (s₁, f₁, fl) ∧
    r₀ = (s₁, f₁, blockFlow np nr stk fl)

theorem blockArm_ansX {L : List BExpr} (hL : LAnsX C L) {np nr : Nat} {stk : List Val}
    {s : Store H} {f : Frame} {stk' : List Val} (cs₁ : List (Call (CallSig H)))
    (v : Except PUnit.{2} (Res × St H)) (hA : Answered C cs₁)
    (h : Path (run' (denListX L f stk' >>= blockK np nr stk : M (CallSig H) H Res) ⟨s⟩)
      cs₁ (.val v)) :
    ∃ s₁ f₁ fl, EvalOX C s f stk' L (s₁, f₁, fl) ∧ endR (s₁, f₁, blockFlow np nr stk fl) = .val v := by
  rcases path_run_bind_inv h (by simp) with ⟨c₁, c₂, a, t, rfl, h₁, h₂⟩ | ⟨h₁, hv⟩
  · obtain ⟨⟨s₁, f₁, fl⟩, hev, hend⟩ := hL s f stk' c₁ _ (answered_left hA) h₁ (by simp)
    obtain ⟨hnt, rfl, rfl⟩ := endR_ok_inv hend
    rw [blockK_eq] at h₂
    obtain ⟨-, hv⟩ := path_pure_inv h₂
    cases hv
    exact ⟨s₁, f₁, fl, hev, endR_ok (fun h => hnt (blockFlow_trap.1 h))⟩
  · obtain ⟨⟨s₁, f₁, fl⟩, hev, hend⟩ := hL s f stk' cs₁ _ hA h₁ (by simp)
    obtain rfl := endR_err_inv hend
    cases hv
    exact ⟨s₁, f₁, .trap, hev, rfl⟩

theorem block_ansX {bt : BlockType} {body es : List BExpr} (hbody : LAnsX C body) (hes : LAnsX C es)
    {s : Store H} {f : Frame} {stk : List Val} {cs : List (Call (CallSig H))}
    {ee : PathEnd (Except PUnit.{2} (Res × St H))} (hA : Answered C cs)
    (h : Path (run' (denX (.block bt body) f stk >>= thenK (denListX es)) ⟨s⟩) cs ee)
    (he : ee ≠ .div) : ∃ r, EvalOX C s f stk (.block bt body :: es) r ∧ endR r = ee := by
  rw [denX_block] at h
  cases har : arity f bt with
  | none =>
    simp only [har] at h
    rcases path_run_bind_inv h he with ⟨_, _, _, _, _, h₁, _⟩ | ⟨h₁, _⟩
    · exact absurd (path_stuck_inv h₁) (by simp)
    · exact absurd (path_stuck_inv h₁) (by simp)
  | some p =>
    obtain ⟨np, nr⟩ := p
    simp only [har] at h
    obtain ⟨r₀, ⟨np', nr', s₁, f₁, fl, har', hev, rfl⟩, hnorm, hnon⟩ :=
      cont_ansX (Q := BlockHeadX C s f stk bt body) hes hA h he fun cs₁ v hA₁ h₁ => by
        obtain ⟨s₁, f₁, fl, hev, hend⟩ := blockArm_ansX hbody cs₁ v hA₁ h₁
        exact ⟨_, ⟨np, nr, s₁, f₁, fl, har, hev, rfl⟩, hend⟩
    rw [har] at har'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj har')
    cases fl with
    | normal vs =>
      obtain ⟨r, hk, hr⟩ := hnorm _ rfl
      exact ⟨r, .blockOk har hev rfl hk, hr⟩
    | brk k vs =>
      cases k with
      | zero =>
        obtain ⟨r, hk, hr⟩ := hnorm _ rfl
        exact ⟨r, .blockOk har hev rfl hk, hr⟩
      | succ k => exact ⟨_, .blockBrk har hev, (hnon Flow.notNormal_brk).symm⟩
    | ret vs => exact ⟨_, .blockEsc har hev trivial, (hnon Flow.notNormal_ret).symm⟩
    | trap => exact ⟨_, .blockEsc har hev trivial, (hnon Flow.notNormal_trap).symm⟩
    | throw t => exact ⟨_, .blockEsc har hev trivial, (hnon Flow.notNormal_throw).symm⟩

end

section
variable {C : CallRel H}

/-- The outcomes of an `if`'s head. -/
def IfHeadX (C : CallRel H) (s : Store H) (f : Frame) (stk : List Val) (bt : BlockType)
    (c t el : List BExpr) (r₀ : Store H × Frame × Flow) : Prop :=
  (¬ r₀.2.2.IsNormal ∧ EvalOX C s f stk c r₀) ∨
  ∃ s₁ f₁ cv stk₁ b np nr s₂ f₂ fl, EvalOX C s f stk c (s₁, f₁, .normal (cv :: stk₁)) ∧
    truthy cv = some b ∧ arity f₁ bt = some (np, nr) ∧
    EvalOX C s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, fl) ∧
    r₀ = (s₂, f₂, blockFlow np nr stk₁ fl)

theorem ifHead_ansX {bt : BlockType} {c t el : List BExpr} (hc : LAnsX C c) (ht : LAnsX C t)
    (hel : LAnsX C el) {s : Store H} {f : Frame} {stk : List Val} (cs₁ : List (Call (CallSig H)))
    (v : Except PUnit.{2} (Res × St H)) (hA₁ : Answered C cs₁)
    (h₁ : Path (run' (denListX c f stk >>= fun r =>
        match r with
        | ⟨(f₁, .normal (cv :: stk₁))⟩ =>
          match truthy cv, arity f₁ bt with
          | some b, some (np, nr) =>
            (if b then denListX t f₁ (stk₁.take np) else
              denListX el f₁ (stk₁.take np)) >>= blockK np nr stk₁
          | _, _ => stuck
        | ⟨(_, .normal [])⟩ => stuck
        | r => pure r : M (CallSig H) H Res) ⟨s⟩) cs₁ (.val v)) :
    ∃ r₀, IfHeadX C s f stk bt c t el r₀ ∧ endR r₀ = .val v := by
  rcases path_run_bind_inv h₁ (by simp) with ⟨c₁, c₂, a, t', rfl, h₁, h₂⟩ | ⟨h₁, hv⟩
  · obtain ⟨⟨s₁, f₁, fl⟩, hev, hend⟩ := hc s f stk c₁ _ (answered_left hA₁) h₁ (by simp)
    obtain ⟨hnt, rfl, rfl⟩ := endR_ok_inv hend
    by_cases hn : fl.IsNormal
    · obtain ⟨stk₁, rfl⟩ : ∃ stk₁, fl = .normal stk₁ := by
        cases fl <;> first | exact ⟨_, rfl⟩ | exact absurd hn id
      rcases stk₁ with _ | ⟨cv, stk₁⟩
      · exact absurd (path_stuck_inv h₂) (by simp)
      cases hb : truthy cv with
      | none => simp only [hb] at h₂; exact absurd (path_stuck_inv h₂) (by simp)
      | some b =>
        cases har : arity f₁ bt with
        | none => simp only [hb, har] at h₂; exact absurd (path_stuck_inv h₂) (by simp)
        | some p =>
          obtain ⟨np, nr⟩ := p
          simp only [hb, har] at h₂
          have hL : LAnsX C (if b then t else el) := by cases b <;> assumption
          have h₂' : Path (run' (denListX (if b then t else el) f₁ (stk₁.take np) >>=
              blockK np nr stk₁ : M (CallSig H) H Res) ⟨s₁⟩) c₂ (.val v) := by
            cases b <;> exact h₂
          obtain ⟨s₂, f₂, fl, hev₂, hend₂⟩ := blockArm_ansX hL c₂ v (answered_right hA₁) h₂'
          exact ⟨_, .inr ⟨s₁, f₁, cv, stk₁, b, np, nr, s₂, f₂, fl, hev, hb, har, hev₂, rfl⟩,
            hend₂⟩
    · have h₂' : Path (run' (pure ⟨(f₁, fl)⟩ : M (CallSig H) H Res) ⟨s₁⟩) c₂ (.val v) := by
        cases fl <;> first | exact absurd trivial hn | exact h₂
      obtain ⟨-, hv⟩ := path_pure_inv h₂'
      cases hv
      exact ⟨_, .inl ⟨hn, hev⟩, hend⟩
  · obtain ⟨⟨s₁, f₁, fl⟩, hev, hend⟩ := hc s f stk cs₁ _ hA₁ h₁ (by simp)
    obtain rfl := endR_err_inv hend
    cases hv
    exact ⟨_, .inl ⟨Flow.notNormal_trap, hev⟩, hend⟩

theorem if_ansX {bt : BlockType} {c t el es : List BExpr} (hc : LAnsX C c) (ht : LAnsX C t)
    (hel : LAnsX C el) (hes : LAnsX C es)
    {s : Store H} {f : Frame} {stk : List Val} {cs : List (Call (CallSig H))}
    {ee : PathEnd (Except PUnit.{2} (Res × St H))} (hA : Answered C cs)
    (h : Path (run' (denX (.if_ bt c t el) f stk >>= thenK (denListX es)) ⟨s⟩) cs ee)
    (he : ee ≠ .div) : ∃ r, EvalOX C s f stk (.if_ bt c t el :: es) r ∧ endR r = ee := by
  rw [denX_if] at h
  obtain ⟨r₀, hQ, hnorm, hnon⟩ := cont_ansX (Q := IfHeadX C s f stk bt c t el) hes hA h he
    (ifHead_ansX hc ht hel)
  rcases hQ with ⟨hn, hev⟩ | ⟨s₁, f₁, cv, stk₁, b, np, nr, s₂, f₂, fl, hev, hb, har, hev₂, rfl⟩
  · exact ⟨r₀, .ifAbort hev hn, (hnon hn).symm⟩
  · cases fl with
    | normal vs =>
      obtain ⟨r, hk, hr⟩ := hnorm _ rfl
      exact ⟨r, .ifOk hev hb har hev₂ rfl hk, hr⟩
    | brk k vs =>
      cases k with
      | zero =>
        obtain ⟨r, hk, hr⟩ := hnorm _ rfl
        exact ⟨r, .ifOk hev hb har hev₂ rfl hk, hr⟩
      | succ k => exact ⟨_, .ifBrk hev hb har hev₂, (hnon Flow.notNormal_brk).symm⟩
    | ret vs => exact ⟨_, .ifEsc hev hb har hev₂ trivial, (hnon Flow.notNormal_ret).symm⟩
    | trap => exact ⟨_, .ifEsc hev hb har hev₂ trivial, (hnon Flow.notNormal_trap).symm⟩
    | throw a => exact ⟨_, .ifEsc hev hb har hev₂ trivial, (hnon Flow.notNormal_throw).symm⟩

end

section
variable {C : CallRel H}

theorem loopOut_inl {np nr : Nat} {stk : List Val} {f₁ : Frame} {fl : Flow} {b : Res}
    (h : loopOut np nr stk f₁ fl = .inl b) :
    (∃ vs, fl = .normal vs ∧ b = ⟨(f₁, .normal (vs.take nr ++ stk.drop np))⟩) ∨
      (∃ k vs, fl = .brk (k + 1) vs ∧ b = ⟨(f₁, .brk k vs)⟩) ∨ (fl.Escapes ∧ b = ⟨(f₁, fl)⟩) := by
  cases fl with
  | normal vs => cases h; exact .inl ⟨vs, rfl, rfl⟩
  | brk k vs =>
    cases k with
    | zero => cases h
    | succ k => cases h; exact .inr (.inl ⟨k, vs, rfl, rfl⟩)
  | ret vs => cases h; exact .inr (.inr ⟨trivial, rfl⟩)
  | trap => cases h; exact .inr (.inr ⟨trivial, rfl⟩)
  | throw a => cases h; exact .inr (.inr ⟨trivial, rfl⟩)

theorem loopOut_inr {np nr : Nat} {stk : List Val} {f₁ : Frame} {fl : Flow}
    {c : ULift.{1} (Frame × List Val)} (h : loopOut np nr stk f₁ fl = .inr c) :
    ∃ vs, fl = .brk 0 vs ∧ c = ⟨(f₁, vs.take np ++ stk.drop np)⟩ := by
  cases fl with
  | brk k vs =>
    cases k with
    | zero => cases h; exact ⟨vs, rfl, rfl⟩
    | succ k => cases h
  | _ => cases h

/-- One loop iteration's path, inverted: the body runs to an `EvalO` outcome. -/
theorem loopIter_ansX {bt : BlockType} {body : List BExpr} (hbody : LAnsX C body)
    {p : ULift.{1} (Frame × List Val) × St H} {cs : List (Call (CallSig H))}
    {r' : PathEnd (Except PUnit.{2} ((Res ⊕ ULift.{1} (Frame × List Val)) × St H))}
    (hA : Answered C cs) (h : Path (run' (loopBodyX bt body p.1) p.2) cs r')
    (hr : r' ≠ .div) :
    ∃ np nr s₁ f₁ fl, arity p.1.down.1 bt = some (np, nr) ∧
      EvalOX C p.2.down p.1.down.1 (p.1.down.2.take np) body (s₁, f₁, fl) ∧
      ((fl = .trap ∧ r' = .val (.error ⟨⟩)) ∨
       (fl ≠ .trap ∧ r' = .val (.ok (loopOut np nr p.1.down.2 f₁ fl, ⟨s₁⟩)))) := by
  obtain ⟨⟨f, stk⟩, ⟨s⟩⟩ := p
  simp only [loopBodyX] at h
  cases har : arity f bt with
  | none => simp only [har] at h; exact absurd (path_stuck_inv h) hr
  | some q =>
    obtain ⟨np, nr⟩ := q
    simp only [har] at h
    rcases path_run_bind_inv h hr with ⟨c₁, c₂, a, t, rfl, h₁, h₂⟩ | ⟨h₁, hv⟩
    · obtain ⟨⟨s₁, f₁, fl⟩, hev, hend⟩ := hbody s f (stk.take np) c₁ _ (answered_left hA) h₁
        (by simp)
      obtain ⟨hnt, rfl, rfl⟩ := endR_ok_inv hend
      rw [loopK_eq] at h₂
      obtain ⟨-, rfl⟩ := path_pure_inv h₂
      exact ⟨np, nr, s₁, f₁, fl, rfl, hev, .inr ⟨hnt, rfl⟩⟩
    · obtain ⟨⟨s₁, f₁, fl⟩, hev, hend⟩ := hbody s f (stk.take np) cs _ hA h₁ (by simp)
      obtain rfl := endR_err_inv hend
      exact ⟨np, nr, s₁, f₁, .trap, rfl, hev, .inl ⟨rfl, hv⟩⟩

/-- A loop with its continuation. -/
theorem loop_ansX {bt : BlockType} {body es : List BExpr} (hbody : LAnsX C body) (hes : LAnsX C es)
    {s : Store H} {f : Frame} {stk : List Val} {cs : List (Call (CallSig H))}
    {ee : PathEnd (Except PUnit.{2} (Res × St H))} (hA : Answered C cs)
    (h : Path (run' (denX (.loop bt body) f stk >>= thenK (denListX es)) ⟨s⟩) cs ee)
    (he : ee ≠ .div) : ∃ r, EvalOX C s f stk (.loop bt body :: es) r ∧ endR r = ee := by
  let G := loopTree (loopBodyX (H := H) bt body)
  let kk : Except PUnit.{2} (Res × St H) → Tree (SigEv (CallSig H)) (Except PUnit.{2} (Res × St H)) :=
    fun r => match r with
      | .ok (a, s') => run' (thenK (denListX es) a) s'
      | .error e => pure (.error e)
  have key : ∀ (p : ULift.{1} (Frame × List Val) × St H) cs₁ (r : PathEnd (Except PUnit.{2} (Res × St H))),
      IterPath G p cs₁ r → ∀ v, r = .val v → ∀ cs₂ ee, Answered C (cs₁ ++ cs₂) →
      Path (kk v) cs₂ ee → ee ≠ .div →
      ∃ r', EvalOX C p.2.down p.1.down.1 p.1.down.2 (.loop bt body :: es) r' ∧ endR r' = ee := by
    intro p cs₁ r hit
    induction hit with
    | @exit p cs y hp =>
      intro v hv cs₂ ee hA h₂ he
      cases hv
      obtain ⟨r', hp', hm⟩ := path_map_inv hp
      rcases loopEnd_inl hm.symm with ⟨e, rfl, rfl⟩ | ⟨b, s', rfl, rfl⟩
      · obtain ⟨np, nr, s₁, f₁, fl, har, hev, ⟨rfl, -⟩ | ⟨-, hr'⟩⟩ :=
          loopIter_ansX hbody (answered_left hA) hp' (by simp)
        · obtain ⟨-, rfl⟩ := path_ret_inv rfl h₂
          exact ⟨_, .loopEsc har hev trivial, rfl⟩
        · cases hr'
      · obtain ⟨np, nr, s₁, f₁, fl, har, hev, ⟨-, hr'⟩ | ⟨hnt, hr'⟩⟩ :=
          loopIter_ansX hbody (answered_left hA) hp' (by simp)
        · cases hr'
        · simp only [PathEnd.val.injEq, Except.ok.injEq, Prod.mk.injEq] at hr'
          obtain ⟨hlo, rfl⟩ := hr'
          rcases loopOut_inl hlo.symm with ⟨vs, rfl, rfl⟩ | ⟨k, vs, rfl, rfl⟩ | ⟨hesc, rfl⟩
          · obtain ⟨r, hk, hr⟩ := hes s₁ f₁ _ cs₂ ee (answered_right hA) h₂ he
            exact ⟨r, .loopOk har hev hk, hr⟩
          · have h₂' : Path (run' (pure ⟨(f₁, .brk k vs)⟩ : M (CallSig H) H Res) ⟨s₁⟩) cs₂ ee := h₂
            obtain ⟨-, rfl⟩ := path_pure_inv h₂'
            exact ⟨_, .loopBrk har hev, rfl⟩
          · rw [show kk (.ok (⟨(f₁, fl)⟩, ⟨s₁⟩)) = run' (pure ⟨(f₁, fl)⟩ : M (CallSig H) H Res) ⟨s₁⟩
              from congrArg (fun x => run' x ⟨s₁⟩)
                (thenK_pass_eq (Flow.not_normal_of_escapes hesc))] at h₂
            obtain ⟨-, rfl⟩ := path_pure_inv h₂
            exact ⟨_, .loopEsc har hev hesc, endR_ok hnt⟩
    | div _ => intro v hv; cases hv
    | @step p cs₁ p' cs₂' r hp _ ih =>
      intro v hv cs₂ ee hA h₂ he
      obtain ⟨r', hp', hm⟩ := path_map_inv hp
      have hr'' := loopEnd_inr hm.symm
      obtain ⟨np, nr, s₁, f₁, fl, har, hev, ⟨-, hr'⟩ | ⟨hnt, hr'⟩⟩ :=
        loopIter_ansX hbody (answered_left (answered_left (by rw [List.append_assoc] at hA ⊢; exact hA)))
          hp' (by rw [hr'']; simp)
      · rw [hr''] at hr'; cases hr'
      · rw [hr''] at hr'
        simp only [PathEnd.val.injEq, Except.ok.injEq, Prod.mk.injEq] at hr'
        obtain ⟨hlo, hs⟩ := hr'
        obtain ⟨vs, rfl, hc⟩ := loopOut_inr hlo.symm
        obtain ⟨r₁, hk, hr₁⟩ := ih v hv cs₂ ee
          (by rw [List.append_assoc] at hA; exact answered_right hA) h₂ he
        rw [hc, hs] at hk
        exact ⟨r₁, .loopBack har hev hk, hr₁⟩
    | spin _ _ _ => intro v hv; cases hv
  rw [denX_loop, StoreBody.run_bind] at h
  rcases path_bind_inv h with ⟨cs₁, cs₂, v, rfl, h₁, h₂⟩ | ⟨rfl, -⟩
  · have h₁' := h₁
    change Path ((((Silmaril.Elgot.iter (loopBodyX bt body) ⟨(f, stk)⟩ :
      M (CallSig H) H _).run ⟨s⟩).run)) cs₁ (.val v) at h₁'
    rw [Silmaril.Wasm.Abstract.BodyTrace.run_iter] at h₁'
    rcases v with e | ⟨a, s'⟩ <;> exact key _ _ _ (path_iter_iff.1 h₁') _ rfl cs₂ ee hA h₂ he
  · exact absurd rfl he

end

section
variable {C : CallRel H}

mutual

theorem tree_ansX : ∀ (e : BExpr) (es : List BExpr), LAnsX C es →
    ∀ (s : Store H) (f : Frame) (stk : List Val) (cs : List (Call (CallSig H)))
      (ee : PathEnd (Except PUnit.{2} (Res × St H))), Answered C cs →
    Path (run' (denX e f stk >>= thenK (denListX es)) ⟨s⟩) cs ee → ee ≠ .div →
    ∃ r, EvalOX C s f stk (e :: es) r ∧ endR r = ee
  | .op i args, es, hes, _, _, _, _, _, hA, h, he => op_ansX (list_ansX args) hes hA h he
  | .block bt body, es, hes, _, _, _, _, _, hA, h, he => block_ansX (list_ansX body) hes hA h he
  | .loop bt body, es, hes, _, _, _, _, _, hA, h, he => loop_ansX (list_ansX body) hes hA h he
  | .if_ bt c t el, es, hes, _, _, _, _, _, hA, h, he =>
    if_ansX (list_ansX c) (list_ansX t) (list_ansX el) hes hA h he
  | .tryTable .., _, _, _, _, _, _, _, _, h, he => by
    rw [denX.eq_def] at h
    rcases path_run_bind_inv h he with ⟨_, _, _, _, _, h₁, _⟩ | ⟨h₁, _⟩
    · exact absurd (path_stuck_inv h₁) (by simp)
    · exact absurd (path_stuck_inv h₁) (by simp)

theorem list_ansX : ∀ (es : List BExpr), LAnsX C es
  | [] => fun s f stk cs e _ h _ => by
    obtain ⟨rfl, rfl⟩ := path_pure_inv h
    exact ⟨(s, f, .normal stk), .nil, rfl⟩
  | e :: es => fun s f stk cs ee hA h he => by
    rw [denListX_cons] at h
    exact tree_ansX e es (list_ansX es) s f stk cs ee hA h he

end
end

end Silmaril.Proofs.Wasm.Abstract.CallX

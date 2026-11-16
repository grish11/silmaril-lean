module

public import Silmaril.Proofs.Wasm.Abstract.StoreCall.Expose
public import Silmaril.Proofs.Wasm.Abstract.BodyTrace.Iter

/-!
Proofs for `Silmaril.Wasm.Abstract.StoreCall.Thms`: every finished path of the
exposed abstract body whose call events are answered by `C` is an `EvalO C`
derivation (`list_ans`). With `evalO_path` this makes exposure exact.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.StoreCall

open Silmaril.Wasm Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract
  Silmaril.Wasm.Abstract.Body Silmaril.Wasm.Abstract.BodyTrace Silmaril.Wasm.Binaryen
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall
  Silmaril.Elgot.ITree Silmaril.Proofs.Wasm.Abstract.StoreBody Silmaril.Proofs.Wasm.Abstract.BodyTrace

variable {E : Sig.{0}} {H : Type}

/-- Paths of a bind: the first part returns a value, or traps. -/
theorem path_run_bind_inv {X Y : Type 1} {x : M E H X} {k : X → M E H Y} {s : St H}
    {cs : List (Call E)} {e : PathEnd (Except PUnit.{2} (Y × St H))}
    (h : Path (run' (x >>= k) s) cs e) (he : e ≠ .div) :
    (∃ cs₁ cs₂ a s₁, cs = cs₁ ++ cs₂ ∧ Path (run' x s) cs₁ (.val (.ok (a, s₁))) ∧
        Path (run' (k a) s₁) cs₂ e) ∨
      (Path (run' x s) cs (.val (.error ⟨⟩)) ∧ e = .val (.error ⟨⟩)) := by
  rw [StoreBody.run_bind] at h
  rcases path_bind_inv h with ⟨cs₁, cs₂, v, rfl, h₁, h₂⟩ | ⟨rfl, -⟩
  · rcases v with ⟨⟨⟩⟩ | ⟨a, s₁⟩
    · obtain ⟨rfl, rfl⟩ := path_ret_inv rfl h₂
      exact .inr ⟨by simpa using h₁, rfl⟩
    · exact .inl ⟨cs₁, cs₂, a, s₁, rfl, h₁, h₂⟩
  · exact absurd rfl he

theorem path_pure_inv {X : Type 1} {a : X} {s : St H} {cs : List (Call E)}
    {e : PathEnd (Except PUnit.{2} (X × St H))} (h : Path (run' (pure a : M E H X) s) cs e) :
    cs = [] ∧ e = .val (.ok (a, s)) :=
  path_ret_inv rfl h

theorem path_stuck_inv {X : Type 1} {s : St H} {cs : List (Call E)}
    {e : PathEnd (Except PUnit.{2} (X × St H))} (h : Path (run' (stuck : M E H X) s) cs e) :
    e = .div :=
  (path_diverge_inv h).2

theorem endR_ok_inv {s₁ : Store H} {f₁ : Frame} {fl : Flow} {a : Res} {t : St H}
    (h : endR (s₁, f₁, fl) = .val (.ok (a, t))) : fl ≠ .trap ∧ a = ⟨(f₁, fl)⟩ ∧ t = ⟨s₁⟩ := by
  cases fl <;> simp_all [endR]

theorem endR_err_inv {s₁ : Store H} {f₁ : Frame} {fl : Flow}
    (h : endR (s₁, f₁, fl) = .val (.error ⟨⟩)) : fl = .trap := by
  cases fl <;> simp_all [endR]

theorem answered_left {C : CallRel H} {a b : List (Call (CallSig H))} (h : Answered C (a ++ b)) :
    Answered C a := fun c hc => h c (List.mem_append_left _ hc)

theorem answered_right {C : CallRel H} {a b : List (Call (CallSig H))} (h : Answered C (a ++ b)) :
    Answered C b := fun c hc => h c (List.mem_append_right _ hc)

theorem blockK_eq (np nr : Nat) (stk : List Val) (f₁ : Frame) (fl : Flow) :
    (blockK np nr stk ⟨(f₁, fl)⟩ : M E H Res) = pure ⟨(f₁, blockFlow np nr stk fl)⟩ := by
  cases fl with
  | brk k vs => cases k <;> rfl
  | _ => rfl

/-- The outcome of a loop body's exits. -/
def loopOut (np nr : Nat) (stk : List Val) (f₁ : Frame) : Flow → Res ⊕ ULift.{1} (Frame × List Val)
  | .normal vs => .inl ⟨(f₁, .normal (vs.take nr ++ stk.drop np))⟩
  | .brk 0 vs => .inr ⟨(f₁, vs.take np ++ stk.drop np)⟩
  | .brk (k + 1) vs => .inl ⟨(f₁, .brk k vs)⟩
  | fl => .inl ⟨(f₁, fl)⟩

theorem loopK_eq (np nr : Nat) (stk : List Val) (f₁ : Frame) (fl : Flow) :
    (loopK np nr stk ⟨(f₁, fl)⟩ : M E H _) = pure (loopOut np nr stk f₁ fl) := by
  cases fl with
  | brk k vs => cases k <;> rfl
  | _ => rfl

theorem thenK_pass_eq {K : Frame → List Val → M E H Res} {f₁ : Frame} {fl : Flow}
    (h : ¬ fl.IsNormal) : thenK K ⟨(f₁, fl)⟩ = pure ⟨(f₁, fl)⟩ := by
  cases fl
  case normal => exact absurd trivial h
  all_goals rfl

theorem run_pure_bind {X Y : Type 1} (a : X) (k : X → M E H Y) (s : St H) :
    run' (pure a >>= k) s = run' (k a) s := by rw [pure_bind]

/-! ## Calls, inverted -/

theorem run_callEv_none {x : FuncIdx} {f : Frame} {stk : List Val} {s : Store H}
    (h : ∀ a fi ps rs, s.func? f x = some (a, fi) →
      Validation.DefType.funcType? fi.type = some (ps, rs) → False) :
    run' (callEv x f stk : M (CallSig H) H Res) ⟨s⟩ = diverge := by
  simp only [callEv, getState, run', StateT.run_bind, StateT.run_get, ExceptT.run_bind,
    ExceptT.run_pure]
  refine (pure_bind _ _).trans ?_
  dsimp only
  split
  · rename_i a fi hfi
    split
    · rename_i ps rs hty
      exact (h a fi ps rs hfi hty).elim
    · rfl
  · rfl

theorem path_callEv_inv {x : FuncIdx} {f : Frame} {stk : List Val} {s : Store H}
    {cs : List (Call (CallSig H))} {e : PathEnd (Except PUnit.{2} (Res × St H))}
    (h : Path (run' (callEv x f stk : M (CallSig H) H Res) ⟨s⟩) cs e) (he : e ≠ .div) :
    ∃ a fi ps rs ans cs', s.func? f x = some (a, fi) ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) ∧
      cs = ⟨(a, (stk.take ps.length).reverse, s), ans⟩ :: cs' ∧
      Path (run' (callAns f stk ps rs ans) ⟨s⟩) cs' e := by
  by_cases hex : ∃ a fi ps rs, s.func? f x = some (a, fi) ∧
      Validation.DefType.funcType? fi.type = some (ps, rs)
  · obtain ⟨a, fi, ps, rs, hfi, hty⟩ := hex
    rw [run_callEv_vis hfi hty] at h
    obtain ⟨n, cs', rfl, hp⟩ := Silmaril.Wasm.Abstract.BodyTrace.path_vis_inv h
    exact ⟨a, fi, ps, rs, n, cs', hfi, hty, rfl, hp⟩
  · rw [run_callEv_none (fun a fi ps rs h1 h2 => hex ⟨a, fi, ps, rs, h1, h2⟩)] at h
    exact absurd (path_diverge_inv h).2 he

theorem path_callAns_inv {f : Frame} {stk : List Val} {ps rs : List Validation.CValType}
    {ans : Store H × Flow} {s : St H} {cs : List (Call (CallSig H))}
    {e : PathEnd (Except PUnit.{2} (Res × St H))}
    (h : Path (run' (callAns f stk ps rs ans) s) cs e) (he : e ≠ .div) :
    cs = [] ∧ ((ans.2 = .trap ∧ e = .val (.error ⟨⟩)) ∨
      (∃ t, ans.2 = .throw t ∧ e = .val (.ok (⟨(f, .throw t)⟩, ⟨ans.1⟩))) ∨
      (∃ vs, ans.2.retVals = some vs ∧
        e = .val (.ok (⟨(f, .normal (vs.take rs.length ++ stk.drop ps.length))⟩, ⟨ans.1⟩)))) := by
  obtain ⟨s₂, fl⟩ := ans
  cases fl with
  | trap =>
    obtain ⟨rfl, rfl⟩ := path_ret_inv (run_trapS s) h
    exact ⟨rfl, .inl ⟨rfl, rfl⟩⟩
  | throw t =>
    obtain ⟨rfl, rfl⟩ := path_ret_inv (run_set_pure _ _ _) h
    exact ⟨rfl, .inr (.inl ⟨t, rfl, rfl⟩)⟩
  | normal ws =>
    obtain ⟨rfl, rfl⟩ := path_ret_inv (run_set_pure _ _ _) h
    exact ⟨rfl, .inr (.inr ⟨ws, rfl, rfl⟩)⟩
  | ret ws =>
    obtain ⟨rfl, rfl⟩ := path_ret_inv (run_set_pure _ _ _) h
    exact ⟨rfl, .inr (.inr ⟨ws, rfl, rfl⟩)⟩
  | brk k ws =>
    cases k with
    | zero =>
      obtain ⟨rfl, rfl⟩ := path_ret_inv (run_set_pure _ _ _) h
      exact ⟨rfl, .inr (.inr ⟨ws, rfl, rfl⟩)⟩
    | succ k => exact absurd (path_stuck_inv h) he

theorem path_flatK_inv {i : Instr} {f : Frame} {stk : List Val} {s : Store H}
    {cs : List (Call E)} {e : PathEnd (Except PUnit.{2} (Res × St H))}
    (h : Path (run' (flatK i f stk : M E H Res) ⟨s⟩) cs e) (he : e ≠ .div) :
    ∃ r, evalFlat s f stk i = some r ∧ cs = [] ∧ e = endR r := by
  rw [show run' (flatK i f stk : M E H Res) ⟨s⟩ = evalTree (evalFlat s f stk i) from
    run_flatK i f stk s] at h
  cases hr : evalFlat s f stk i with
  | none => rw [hr] at h; exact absurd (path_diverge_inv h).2 he
  | some r =>
    rw [hr] at h
    obtain ⟨s', f', fl⟩ := r
    refine ⟨_, rfl, ?_⟩
    cases fl <;> exact path_ret_inv rfl h

/-! ## The converse -/

section
variable {C : CallRel H}

/-- Finished, answered paths of the exposed body of `es` are `EvalO C` derivations. -/
def LAns (C : CallRel H) (es : List BExpr) : Prop :=
  ∀ s f stk cs e, Answered C cs →
    Path (run' (denListC callEv es f stk : M (CallSig H) H Res) ⟨s⟩) cs e → e ≠ .div →
    ∃ r, EvalO C s f stk es r ∧ endR r = e

/-- A head computation followed by the continuation `es`. -/
theorem cont_ans {es : List BExpr} (hes : LAns C es) {x : M (CallSig H) H Res} {s : St H}
    {cs : List (Call (CallSig H))} {ee : PathEnd (Except PUnit.{2} (Res × St H))}
    {Q : Store H × Frame × Flow → Prop} (hA : Answered C cs)
    (h : Path (run' (x >>= thenK (denListC callEv es)) s) cs ee) (he : ee ≠ .div)
    (hx : ∀ cs₁ v, Answered C cs₁ → Path (run' x s) cs₁ (.val v) →
      ∃ r₀, Q r₀ ∧ endR r₀ = .val v) :
    ∃ r₀, Q r₀ ∧ (∀ stk', r₀.2.2 = .normal stk' →
        ∃ r, EvalO C r₀.1 r₀.2.1 stk' es r ∧ endR r = ee) ∧
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

/-- The outcomes of an operator node's head. -/
def OpHead (C : CallRel H) (s : Store H) (f : Frame) (stk : List Val) (i : Instr)
    (args : List BExpr) (r₀ : Store H × Frame × Flow) : Prop :=
  (¬ r₀.2.2.IsNormal ∧ EvalO C s f stk args r₀) ∨
  ∃ s₁ f₁ stk₁, EvalO C s f stk args (s₁, f₁, .normal stk₁) ∧
    (((∀ x, i ≠ .call x) ∧ evalFlat s₁ f₁ stk₁ i = some r₀) ∨
     ∃ x a fi ps rs, i = .call x ∧ s₁.func? f₁ x = some (a, fi) ∧
       Validation.DefType.funcType? fi.type = some (ps, rs) ∧
       ((∃ fl vs, C s₁ a (stk₁.take ps.length).reverse (r₀.1, fl) ∧ fl.retVals = some vs ∧
          r₀ = (r₀.1, f₁, .normal (vs.take rs.length ++ stk₁.drop ps.length))) ∨
        (C s₁ a (stk₁.take ps.length).reverse (r₀.1, .trap) ∧ r₀ = (r₀.1, f₁, .trap)) ∨
        (∃ t, C s₁ a (stk₁.take ps.length).reverse (r₀.1, .throw t) ∧
          r₀ = (r₀.1, f₁, .throw t))))

theorem opHead_ans {i : Instr} {args : List BExpr} (hargs : LAns C args) {s : Store H}
    {f : Frame} {stk : List Val} (cs₁ : List (Call (CallSig H)))
    (v : Except PUnit.{2} (Res × St H)) (hA : Answered C cs₁)
    (h : Path (run' (denListC callEv args f stk >>= thenK (opC callEv i) : M (CallSig H) H Res)
      ⟨s⟩) cs₁ (.val v)) :
    ∃ r₀, OpHead C s f stk i args r₀ ∧ endR r₀ = .val v := by
  rcases path_run_bind_inv h (by simp) with ⟨c₁, c₂, a, s₁, rfl, h₁, h₂⟩ | ⟨h₁, hv⟩
  · obtain ⟨⟨s₀, f₀, fl⟩, hev, hend⟩ := hargs s f stk c₁ _ (answered_left hA) h₁ (by simp)
    obtain ⟨hnt, rfl, rfl⟩ := endR_ok_inv hend
    by_cases hn : fl.IsNormal
    · obtain ⟨stk₁, rfl⟩ : ∃ stk₁, fl = .normal stk₁ := by
        cases fl <;> first | exact ⟨_, rfl⟩ | exact absurd hn id
      have h₂' : Path (run' (opC callEv i f₀ stk₁ : M (CallSig H) H Res) ⟨s₀⟩) c₂ (.val v) := h₂
      cases hci : callIdx? i with
      | none =>
        have hi : ∀ x, i ≠ .call x := fun x hx => by subst hx; simp [callIdx?] at hci
        simp only [opC, hci] at h₂'
        obtain ⟨r₀, hflat, -, hr₀⟩ := path_flatK_inv h₂' (by simp)
        exact ⟨r₀, .inr ⟨s₀, f₀, stk₁, hev, .inl ⟨hi, hflat⟩⟩, hr₀.symm⟩
      | some x =>
        have hix : i = .call x := by
          cases i <;> simp_all [callIdx?]
        simp only [opC, hci] at h₂'
        obtain ⟨a', fi, ps, rs, ans, cs', hfi, hty, hc, hp⟩ := path_callEv_inv h₂' (by simp)
        have hAns : C s₀ a' (stk₁.take ps.length).reverse ans := by
          have := answered_right hA
          rw [hc] at this
          exact this _ (List.mem_cons_self ..)
        obtain ⟨-, hcase⟩ := path_callAns_inv hp (by simp)
        obtain ⟨s₂, fl₂⟩ := ans
        rcases hcase with ⟨rfl, hv⟩ | ⟨t, rfl, hv⟩ | ⟨vs, hvs, hv⟩ <;> cases hv
        · exact ⟨(s₂, f₀, .trap), .inr ⟨s₀, f₀, stk₁, hev, .inr ⟨x, a', fi, ps, rs, hix, hfi, hty,
            .inr (.inl ⟨hAns, rfl⟩)⟩⟩, rfl⟩
        · exact ⟨(s₂, f₀, .throw t), .inr ⟨s₀, f₀, stk₁, hev, .inr ⟨x, a', fi, ps, rs, hix, hfi, hty,
            .inr (.inr ⟨t, hAns, rfl⟩)⟩⟩, rfl⟩
        · exact ⟨(s₂, f₀, .normal (vs.take rs.length ++ stk₁.drop ps.length)),
            .inr ⟨s₀, f₀, stk₁, hev, .inr ⟨x, a', fi, ps, rs, hix, hfi, hty,
              .inl ⟨fl₂, vs, hAns, hvs, rfl⟩⟩⟩, rfl⟩
    · rw [thenK_pass_eq hn] at h₂
      obtain ⟨-, hv⟩ := path_pure_inv h₂
      cases hv
      exact ⟨_, .inl ⟨hn, hev⟩, hend⟩
  · obtain ⟨⟨s₀, f₀, fl⟩, hev, hend⟩ := hargs s f stk cs₁ _ hA h₁ (by simp)
    obtain rfl := endR_err_inv hend
    cases hv
    exact ⟨_, .inl ⟨Flow.notNormal_trap, hev⟩, hend⟩

end

section
variable {C : CallRel H}

theorem endR_ok {s₁ : Store H} {f₁ : Frame} {fl : Flow} (h : fl ≠ .trap) :
    endR (s₁, f₁, fl) = .val (.ok (⟨(f₁, fl)⟩, ⟨s₁⟩)) := by
  cases fl <;> first | exact absurd rfl h | rfl

theorem blockFlow_trap {np nr : Nat} {stk : List Val} {fl : Flow} :
    blockFlow np nr stk fl = .trap ↔ fl = .trap := by
  cases fl with
  | brk k vs => cases k <;> simp [blockFlow]
  | _ => simp [blockFlow]

/-- An `op` tree with its continuation. -/
theorem op_ans {i : Instr} {args es : List BExpr} (hargs : LAns C args) (hes : LAns C es)
    {s : Store H} {f : Frame} {stk : List Val} {cs : List (Call (CallSig H))}
    {ee : PathEnd (Except PUnit.{2} (Res × St H))} (hA : Answered C cs)
    (h : Path (run' (denC callEv (.op i args) f stk >>= thenK (denListC callEv es)) ⟨s⟩) cs ee)
    (he : ee ≠ .div) : ∃ r, EvalO C s f stk (.op i args :: es) r ∧ endR r = ee := by
  rw [denC_op] at h
  obtain ⟨r₀, hQ, hnorm, hnon⟩ := cont_ans hes hA h he (opHead_ans hargs)
  rcases hQ with ⟨hn, hev⟩ | ⟨s₁, f₁, stk₁, hev, ⟨hi, hflat⟩ | ⟨x, a, fi, ps, rs, rfl, hfi, hty, hc⟩⟩
  · exact ⟨r₀, .argsAbort hev hn, (hnon hn).symm⟩
  · obtain ⟨s₂, f₂, fl₂⟩ := r₀
    by_cases hn : fl₂.IsNormal
    · obtain ⟨stk₂, rfl⟩ : ∃ stk₂, fl₂ = .normal stk₂ := by
        cases fl₂ <;> first | exact ⟨_, rfl⟩ | exact absurd hn id
      obtain ⟨r, hk, hr⟩ := hnorm stk₂ rfl
      exact ⟨r, .opOk hi hev hflat hk, hr⟩
    · exact ⟨_, .opStop hi hev hflat hn, (hnon hn).symm⟩
  · rcases hc with ⟨fl, vs, hC, hvs, hr₀⟩ | ⟨hC, hr₀⟩ | ⟨t, hC, hr₀⟩
    · obtain ⟨r, hk, hr⟩ := hnorm _ (by rw [hr₀])
      rw [hr₀] at hk
      exact ⟨r, .callOk hev hfi hty hC hvs hk, hr⟩
    · refine ⟨_, .callTrap hev hfi hty hC, ?_⟩
      rw [hnon (by rw [hr₀]; exact Flow.notNormal_trap), hr₀]
    · refine ⟨_, .callThrow hev hfi hty hC, ?_⟩
      rw [hnon (by rw [hr₀]; exact Flow.notNormal_throw), hr₀]

/-- The outcomes of a block's head. -/
def BlockHead (C : CallRel H) (s : Store H) (f : Frame) (stk : List Val) (bt : BlockType)
    (body : List BExpr) (r₀ : Store H × Frame × Flow) : Prop :=
  ∃ np nr s₁ f₁ fl, arity f bt = some (np, nr) ∧ EvalO C s f (stk.take np) body (s₁, f₁, fl) ∧
    r₀ = (s₁, f₁, blockFlow np nr stk fl)

theorem blockArm_ans {L : List BExpr} (hL : LAns C L) {np nr : Nat} {stk : List Val}
    {s : Store H} {f : Frame} {stk' : List Val} (cs₁ : List (Call (CallSig H)))
    (v : Except PUnit.{2} (Res × St H)) (hA : Answered C cs₁)
    (h : Path (run' (denListC callEv L f stk' >>= blockK np nr stk : M (CallSig H) H Res) ⟨s⟩)
      cs₁ (.val v)) :
    ∃ s₁ f₁ fl, EvalO C s f stk' L (s₁, f₁, fl) ∧ endR (s₁, f₁, blockFlow np nr stk fl) = .val v := by
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

theorem block_ans {bt : BlockType} {body es : List BExpr} (hbody : LAns C body) (hes : LAns C es)
    {s : Store H} {f : Frame} {stk : List Val} {cs : List (Call (CallSig H))}
    {ee : PathEnd (Except PUnit.{2} (Res × St H))} (hA : Answered C cs)
    (h : Path (run' (denC callEv (.block bt body) f stk >>= thenK (denListC callEv es)) ⟨s⟩) cs ee)
    (he : ee ≠ .div) : ∃ r, EvalO C s f stk (.block bt body :: es) r ∧ endR r = ee := by
  rw [denC_block] at h
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
      cont_ans (Q := BlockHead C s f stk bt body) hes hA h he fun cs₁ v hA₁ h₁ => by
        obtain ⟨s₁, f₁, fl, hev, hend⟩ := blockArm_ans hbody cs₁ v hA₁ h₁
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
def IfHead (C : CallRel H) (s : Store H) (f : Frame) (stk : List Val) (bt : BlockType)
    (c t el : List BExpr) (r₀ : Store H × Frame × Flow) : Prop :=
  (¬ r₀.2.2.IsNormal ∧ EvalO C s f stk c r₀) ∨
  ∃ s₁ f₁ cv stk₁ b np nr s₂ f₂ fl, EvalO C s f stk c (s₁, f₁, .normal (cv :: stk₁)) ∧
    truthy cv = some b ∧ arity f₁ bt = some (np, nr) ∧
    EvalO C s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, fl) ∧
    r₀ = (s₂, f₂, blockFlow np nr stk₁ fl)

theorem ifHead_ans {bt : BlockType} {c t el : List BExpr} (hc : LAns C c) (ht : LAns C t)
    (hel : LAns C el) {s : Store H} {f : Frame} {stk : List Val} (cs₁ : List (Call (CallSig H)))
    (v : Except PUnit.{2} (Res × St H)) (hA₁ : Answered C cs₁)
    (h₁ : Path (run' (denListC callEv c f stk >>= fun r =>
        match r with
        | ⟨(f₁, .normal (cv :: stk₁))⟩ =>
          match truthy cv, arity f₁ bt with
          | some b, some (np, nr) =>
            (if b then denListC callEv t f₁ (stk₁.take np) else
              denListC callEv el f₁ (stk₁.take np)) >>= blockK np nr stk₁
          | _, _ => stuck
        | ⟨(_, .normal [])⟩ => stuck
        | r => pure r : M (CallSig H) H Res) ⟨s⟩) cs₁ (.val v)) :
    ∃ r₀, IfHead C s f stk bt c t el r₀ ∧ endR r₀ = .val v := by
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
          have hL : LAns C (if b then t else el) := by cases b <;> assumption
          have h₂' : Path (run' (denListC callEv (if b then t else el) f₁ (stk₁.take np) >>=
              blockK np nr stk₁ : M (CallSig H) H Res) ⟨s₁⟩) c₂ (.val v) := by
            cases b <;> exact h₂
          obtain ⟨s₂, f₂, fl, hev₂, hend₂⟩ := blockArm_ans hL c₂ v (answered_right hA₁) h₂'
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

theorem if_ans {bt : BlockType} {c t el es : List BExpr} (hc : LAns C c) (ht : LAns C t)
    (hel : LAns C el) (hes : LAns C es)
    {s : Store H} {f : Frame} {stk : List Val} {cs : List (Call (CallSig H))}
    {ee : PathEnd (Except PUnit.{2} (Res × St H))} (hA : Answered C cs)
    (h : Path (run' (denC callEv (.if_ bt c t el) f stk >>= thenK (denListC callEv es)) ⟨s⟩) cs ee)
    (he : ee ≠ .div) : ∃ r, EvalO C s f stk (.if_ bt c t el :: es) r ∧ endR r = ee := by
  rw [denC_if] at h
  obtain ⟨r₀, hQ, hnorm, hnon⟩ := cont_ans (Q := IfHead C s f stk bt c t el) hes hA h he
    (ifHead_ans hc ht hel)
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
theorem loopIter_ans {bt : BlockType} {body : List BExpr} (hbody : LAns C body)
    {p : ULift.{1} (Frame × List Val) × St H} {cs : List (Call (CallSig H))}
    {r' : PathEnd (Except PUnit.{2} ((Res ⊕ ULift.{1} (Frame × List Val)) × St H))}
    (hA : Answered C cs) (h : Path (run' (loopBodyC callEv bt body p.1) p.2) cs r')
    (hr : r' ≠ .div) :
    ∃ np nr s₁ f₁ fl, arity p.1.down.1 bt = some (np, nr) ∧
      EvalO C p.2.down p.1.down.1 (p.1.down.2.take np) body (s₁, f₁, fl) ∧
      ((fl = .trap ∧ r' = .val (.error ⟨⟩)) ∨
       (fl ≠ .trap ∧ r' = .val (.ok (loopOut np nr p.1.down.2 f₁ fl, ⟨s₁⟩)))) := by
  obtain ⟨⟨f, stk⟩, ⟨s⟩⟩ := p
  simp only [loopBodyC] at h
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
theorem loop_ans {bt : BlockType} {body es : List BExpr} (hbody : LAns C body) (hes : LAns C es)
    {s : Store H} {f : Frame} {stk : List Val} {cs : List (Call (CallSig H))}
    {ee : PathEnd (Except PUnit.{2} (Res × St H))} (hA : Answered C cs)
    (h : Path (run' (denC callEv (.loop bt body) f stk >>= thenK (denListC callEv es)) ⟨s⟩) cs ee)
    (he : ee ≠ .div) : ∃ r, EvalO C s f stk (.loop bt body :: es) r ∧ endR r = ee := by
  let G := loopTree (loopBodyC (callEv (H := H)) bt body)
  let kk : Except PUnit.{2} (Res × St H) → Tree (SigEv (CallSig H)) (Except PUnit.{2} (Res × St H)) :=
    fun r => match r with
      | .ok (a, s') => run' (thenK (denListC callEv es) a) s'
      | .error e => pure (.error e)
  have key : ∀ (p : ULift.{1} (Frame × List Val) × St H) cs₁ (r : PathEnd (Except PUnit.{2} (Res × St H))),
      IterPath G p cs₁ r → ∀ v, r = .val v → ∀ cs₂ ee, Answered C (cs₁ ++ cs₂) →
      Path (kk v) cs₂ ee → ee ≠ .div →
      ∃ r', EvalO C p.2.down p.1.down.1 p.1.down.2 (.loop bt body :: es) r' ∧ endR r' = ee := by
    intro p cs₁ r hit
    induction hit with
    | @exit p cs y hp =>
      intro v hv cs₂ ee hA h₂ he
      cases hv
      obtain ⟨r', hp', hm⟩ := path_map_inv hp
      rcases loopEnd_inl hm.symm with ⟨e, rfl, rfl⟩ | ⟨b, s', rfl, rfl⟩
      · obtain ⟨np, nr, s₁, f₁, fl, har, hev, ⟨rfl, -⟩ | ⟨-, hr'⟩⟩ :=
          loopIter_ans hbody (answered_left hA) hp' (by simp)
        · obtain ⟨-, rfl⟩ := path_ret_inv rfl h₂
          exact ⟨_, .loopEsc har hev trivial, rfl⟩
        · cases hr'
      · obtain ⟨np, nr, s₁, f₁, fl, har, hev, ⟨-, hr'⟩ | ⟨hnt, hr'⟩⟩ :=
          loopIter_ans hbody (answered_left hA) hp' (by simp)
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
        loopIter_ans hbody (answered_left (answered_left (by rw [List.append_assoc] at hA ⊢; exact hA)))
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
  rw [denC_loop, StoreBody.run_bind] at h
  rcases path_bind_inv h with ⟨cs₁, cs₂, v, rfl, h₁, h₂⟩ | ⟨rfl, -⟩
  · have h₁' := h₁
    change Path ((((Silmaril.Elgot.iter (loopBodyC callEv bt body) ⟨(f, stk)⟩ :
      M (CallSig H) H _).run ⟨s⟩).run)) cs₁ (.val v) at h₁'
    rw [Silmaril.Wasm.Abstract.BodyTrace.run_iter] at h₁'
    rcases v with e | ⟨a, s'⟩ <;> exact key _ _ _ (path_iter_iff.1 h₁') _ rfl cs₂ ee hA h₂ he
  · exact absurd rfl he

end

section
variable {C : CallRel H}

mutual

theorem tree_ans : ∀ (e : BExpr) (es : List BExpr), LAns C es →
    ∀ (s : Store H) (f : Frame) (stk : List Val) (cs : List (Call (CallSig H)))
      (ee : PathEnd (Except PUnit.{2} (Res × St H))), Answered C cs →
    Path (run' (denC callEv e f stk >>= thenK (denListC callEv es)) ⟨s⟩) cs ee → ee ≠ .div →
    ∃ r, EvalO C s f stk (e :: es) r ∧ endR r = ee
  | .op i args, es, hes, _, _, _, _, _, hA, h, he => op_ans (list_ans args) hes hA h he
  | .block bt body, es, hes, _, _, _, _, _, hA, h, he => block_ans (list_ans body) hes hA h he
  | .loop bt body, es, hes, _, _, _, _, _, hA, h, he => loop_ans (list_ans body) hes hA h he
  | .if_ bt c t el, es, hes, _, _, _, _, _, hA, h, he =>
    if_ans (list_ans c) (list_ans t) (list_ans el) hes hA h he
  | .tryTable .., _, _, _, _, _, _, _, _, h, he => by
    rw [denC.eq_def] at h
    rcases path_run_bind_inv h he with ⟨_, _, _, _, _, h₁, _⟩ | ⟨h₁, _⟩
    · exact absurd (path_stuck_inv h₁) (by simp)
    · exact absurd (path_stuck_inv h₁) (by simp)

theorem list_ans : ∀ (es : List BExpr), LAns C es
  | [] => fun s f stk cs e _ h _ => by
    obtain ⟨rfl, rfl⟩ := path_pure_inv h
    exact ⟨(s, f, .normal stk), .nil, rfl⟩
  | e :: es => fun s f stk cs ee hA h he => by
    rw [denListC_cons] at h
    exact tree_ans e es (list_ans es) s f stk cs ee hA h he

end

end

end Silmaril.Proofs.Wasm.Abstract.StoreCall

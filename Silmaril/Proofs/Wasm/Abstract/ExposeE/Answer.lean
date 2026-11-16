module

public import Silmaril.Proofs.Wasm.Abstract.ExposeE.Expose
public import Silmaril.Proofs.Wasm.Abstract.CallX.Answer

/-!
Proofs for `Silmaril.Wasm.Abstract.ExposeE.Thms`: every finished path of the exposed body
`denListXE` whose call events are answered by `C` is an `EvalOXE C` derivation
(`list_ansXE`). With `evalOXE_path` this makes the exposure of the relation with exceptions
exact.

The structural cases are `CallX`'s, read for `denListXE`; the operator case reuses `CallX`'s
inverted heads (`HeadX`, `headX_ans`) and adds `throw` and `throw_ref`; `try_table` inverts
the handler resolution (`resolveCatch`) to a `Cfg.Region.Catches` witness.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.ExposeE

open Silmaril.Wasm Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract
  Silmaril.Wasm.Abstract.Body Silmaril.Wasm.Abstract.BodyTrace Silmaril.Wasm.Binaryen
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall
  Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXE Silmaril.Wasm.Abstract.ExposeE
  Silmaril.Elgot.ITree Silmaril.Proofs.Wasm.Abstract.StoreBody
  Silmaril.Proofs.Wasm.Abstract.BodyTrace Silmaril.Proofs.Wasm.Abstract.StoreCall
  Silmaril.Proofs.Wasm.Abstract.CallX

variable {H : Type}

/-! ## Resolutions, inverted -/

theorem resolveThrow_spec {s : Store H} {f : Frame} {x : TagIdx} {stk : List Val}
    {p : Nat × Nat} (h : resolveThrow s f x stk = some p) : ThrowResS s f x stk p := by
  unfold resolveThrow at h
  split at h
  · rename_i hex
    cases h
    exact Classical.choose_spec hex
  · cases h

theorem resolveCatch_spec {s : Store H} {f : Frame} {a : Nat} {cs : List Catch}
    {r : Option (List Val × LabelIdx)} (h : resolveCatch s f a cs = some r) :
    Cfg.Region.Catches s f a cs r := by
  unfold resolveCatch at h
  split at h
  · rename_i hex
    cases h
    exact Classical.choose_spec hex
  · cases h

section
variable {C : CallRel H}

/-- Finished, answered paths of the exposed body of `es` are `EvalOXE C` derivations. -/
def LAnsXE (C : CallRel H) (es : List BExpr) : Prop :=
  ∀ s f stk cs e, Answered C cs →
    Path (run' (denListXE es f stk : M (CallSig H) H Res) ⟨s⟩) cs e → e ≠ .div →
    ∃ r, EvalOXE C s f stk es r ∧ endR r = e

/-- A head computation followed by the continuation `es`. -/
theorem cont_ansXE {es : List BExpr} (hes : LAnsXE C es) {x : M (CallSig H) H Res} {s : St H}
    {cs : List (Call (CallSig H))} {ee : PathEnd (Except PUnit.{2} (Res × St H))}
    {Q : Store H × Frame × Flow → Prop} (hA : Answered C cs)
    (h : Path (run' (x >>= thenK (denListXE es)) s) cs ee) (he : ee ≠ .div)
    (hx : ∀ cs₁ v, Answered C cs₁ → Path (run' x s) cs₁ (.val v) →
      ∃ r₀, Q r₀ ∧ endR r₀ = .val v) :
    ∃ r₀, Q r₀ ∧ (∀ stk', r₀.2.2 = .normal stk' →
        ∃ r, EvalOXE C r₀.1 r₀.2.1 stk' es r ∧ endR r = ee) ∧
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

/-- The outcome of an operator on the stack `stk₁` its arguments left, every call answered by
`C`: `CallX`'s heads, and the exception operators. -/
inductive HeadXE (C : CallRel H) (s₁ : Store H) (f₁ : Frame) (stk₁ : List Val) :
    Instr → Store H × Frame × Flow → Prop
  | ofX {i : Instr} {r₀ : Store H × Frame × Flow} (h : HeadX C s₁ f₁ stk₁ i r₀) :
      HeadXE C s₁ f₁ stk₁ i r₀
  | throw {x : TagIdx} {ta : Nat} {ti : TagInst} {ts : Validation.Ty (.list .val)}
      (ht : s₁.tag? f₁ x = some (ta, ti)) (he : Validation.Expand ti.type (.func ts .nil))
      (hn : ts.length ≤ stk₁.length) :
      HeadXE C s₁ f₁ stk₁ (.throw x)
        (s₁.addExn ⟨ta, (stk₁.take ts.length).reverse⟩, f₁, .throw s₁.exns.length)
  | throwRefNull {stk' : List Val} (hstk : stk₁ = .ref .null :: stk') :
      HeadXE C s₁ f₁ stk₁ .throwRef (s₁, f₁, .trap)
  | throwRefExn {a : Nat} {stk' : List Val} (hstk : stk₁ = .ref (.exn a) :: stk') :
      HeadXE C s₁ f₁ stk₁ .throwRef (s₁, f₁, .throw a)

/-- The outcomes of an operator node's head. -/
def OpHeadXE (C : CallRel H) (s : Store H) (f : Frame) (stk : List Val) (i : Instr)
    (args : List BExpr) (r₀ : Store H × Frame × Flow) : Prop :=
  (¬ r₀.2.2.IsNormal ∧ EvalOXE C s f stk args r₀) ∨
  ∃ s₁ f₁ stk₁, EvalOXE C s f stk args (s₁, f₁, .normal stk₁) ∧ HeadXE C s₁ f₁ stk₁ i r₀

/-- The head of an operator node, on the stack its arguments left. -/
theorem headXE_ans {i : Instr} {s₀ : Store H} {f₀ : Frame} {stk₁ : List Val}
    {c₂ : List (Call (CallSig H))} {v : Except PUnit.{2} (Res × St H)} (hA : Answered C c₂)
    (h : Path (run' (opCXE i f₀ stk₁ : M (CallSig H) H Res) ⟨s₀⟩) c₂ (.val v)) :
    ∃ r₀, HeadXE C s₀ f₀ stk₁ i r₀ ∧ endR r₀ = .val v := by
  cases hx : ehInstr i with
  | false =>
    rw [opCXE_eq_opCX hx] at h
    obtain ⟨r₀, hh, hr⟩ := headX_ans hA h
    exact ⟨r₀, .ofX hh, hr⟩
  | true =>
    obtain ⟨x, rfl⟩ | rfl : (∃ x, i = .throw x) ∨ i = .throwRef := by
      cases i <;> simp_all [ehInstr]
    · change Path (run' (throwEv x f₀ stk₁ : M (CallSig H) H Res) ⟨s₀⟩) c₂ (.val v) at h
      rw [throwEv, run_getState_bind] at h
      cases hr : resolveThrow s₀ f₀ x stk₁ with
      | none =>
        simp only [hr] at h
        exact absurd (path_stuck_inv h) (by simp)
      | some p =>
        obtain ⟨ta, n⟩ := p
        simp only [hr] at h
        obtain ⟨-, hv⟩ := path_ret_inv (run_set_pure _ _ _) h
        cases hv
        obtain ⟨ti, ts, ht, he, hl, hn⟩ := resolveThrow_spec hr
        dsimp only at ht hl hn
        subst hl
        exact ⟨_, .throw ht he hn, rfl⟩
    · change Path (run' (throwRefEv f₀ stk₁ : M (CallSig H) H Res) ⟨s₀⟩) c₂ (.val v) at h
      unfold throwRefEv at h
      split at h
      · obtain ⟨-, hv⟩ := path_ret_inv (run_trapS _) h
        cases hv
        exact ⟨_, .throwRefNull rfl, rfl⟩
      · obtain ⟨-, hv⟩ := path_pure_inv h
        cases hv
        exact ⟨_, .throwRefExn rfl, rfl⟩
      · exact absurd (path_stuck_inv h) (by simp)

theorem opHeadXE_ans {i : Instr} {args : List BExpr} (hargs : LAnsXE C args) {s : Store H}
    {f : Frame} {stk : List Val} (cs₁ : List (Call (CallSig H)))
    (v : Except PUnit.{2} (Res × St H)) (hA : Answered C cs₁)
    (h : Path (run' (denListXE args f stk >>= thenK (opCXE i) : M (CallSig H) H Res)
      ⟨s⟩) cs₁ (.val v)) :
    ∃ r₀, OpHeadXE C s f stk i args r₀ ∧ endR r₀ = .val v := by
  rcases path_run_bind_inv h (by simp) with ⟨c₁, c₂, a, s₁, rfl, h₁, h₂⟩ | ⟨h₁, hv⟩
  · obtain ⟨⟨s₀, f₀, fl⟩, hev, hend⟩ := hargs s f stk c₁ _ (answered_left hA) h₁ (by simp)
    obtain ⟨hnt, rfl, rfl⟩ := endR_ok_inv hend
    by_cases hn : fl.IsNormal
    · obtain ⟨stk₁, rfl⟩ : ∃ stk₁, fl = .normal stk₁ := by
        cases fl <;> first | exact ⟨_, rfl⟩ | exact absurd hn id
      have h₂' : Path (run' (opCXE i f₀ stk₁ : M (CallSig H) H Res) ⟨s₀⟩) c₂ (.val v) := h₂
      obtain ⟨r₀, hhead, hr₀⟩ := headXE_ans (answered_right hA) h₂'
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
theorem op_ansXE {i : Instr} {args es : List BExpr} (hargs : LAnsXE C args) (hes : LAnsXE C es)
    {s : Store H} {f : Frame} {stk : List Val} {cs : List (Call (CallSig H))}
    {ee : PathEnd (Except PUnit.{2} (Res × St H))} (hA : Answered C cs)
    (h : Path (run' (denXE (.op i args) f stk >>= thenK (denListXE es)) ⟨s⟩) cs ee)
    (he : ee ≠ .div) : ∃ r, EvalOXE C s f stk (.op i args :: es) r ∧ endR r = ee := by
  rw [denXE_op] at h
  obtain ⟨r₀, hQ, hnorm, hnon⟩ := cont_ansXE hes hA h he (opHeadXE_ans hargs)
  rcases hQ with ⟨hn, hev⟩ | ⟨s₁, f₁, stk₁, hev, hhead⟩
  · exact ⟨r₀, .argsAbort hev hn, (hnon hn).symm⟩
  cases hhead with
  | throw ht he hn => exact ⟨_, .throw hev ht he hn, (hnon Flow.notNormal_throw).symm⟩
  | throwRefNull hstk =>
    subst hstk
    exact ⟨_, .throwRefNull hev, (hnon Flow.notNormal_trap).symm⟩
  | throwRefExn hstk =>
    subst hstk
    exact ⟨_, .throwRefExn hev, (hnon Flow.notNormal_throw).symm⟩
  | ofX hh =>
    cases hh with
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

def BlockHeadXE (C : CallRel H) (s : Store H) (f : Frame) (stk : List Val) (bt : BlockType)
    (body : List BExpr) (r₀ : Store H × Frame × Flow) : Prop :=
  ∃ np nr s₁ f₁ fl, arity f bt = some (np, nr) ∧ EvalOXE C s f (stk.take np) body (s₁, f₁, fl) ∧
    r₀ = (s₁, f₁, blockFlow np nr stk fl)

theorem blockArm_ansXE {L : List BExpr} (hL : LAnsXE C L) {np nr : Nat} {stk : List Val}
    {s : Store H} {f : Frame} {stk' : List Val} (cs₁ : List (Call (CallSig H)))
    (v : Except PUnit.{2} (Res × St H)) (hA : Answered C cs₁)
    (h : Path (run' (denListXE L f stk' >>= blockK np nr stk : M (CallSig H) H Res) ⟨s⟩)
      cs₁ (.val v)) :
    ∃ s₁ f₁ fl, EvalOXE C s f stk' L (s₁, f₁, fl) ∧ endR (s₁, f₁, blockFlow np nr stk fl) = .val v := by
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

theorem block_ansXE {bt : BlockType} {body es : List BExpr} (hbody : LAnsXE C body) (hes : LAnsXE C es)
    {s : Store H} {f : Frame} {stk : List Val} {cs : List (Call (CallSig H))}
    {ee : PathEnd (Except PUnit.{2} (Res × St H))} (hA : Answered C cs)
    (h : Path (run' (denXE (.block bt body) f stk >>= thenK (denListXE es)) ⟨s⟩) cs ee)
    (he : ee ≠ .div) : ∃ r, EvalOXE C s f stk (.block bt body :: es) r ∧ endR r = ee := by
  rw [denXE_block] at h
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
      cont_ansXE (Q := BlockHeadXE C s f stk bt body) hes hA h he fun cs₁ v hA₁ h₁ => by
        obtain ⟨s₁, f₁, fl, hev, hend⟩ := blockArm_ansXE hbody cs₁ v hA₁ h₁
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
def IfHeadXE (C : CallRel H) (s : Store H) (f : Frame) (stk : List Val) (bt : BlockType)
    (c t el : List BExpr) (r₀ : Store H × Frame × Flow) : Prop :=
  (¬ r₀.2.2.IsNormal ∧ EvalOXE C s f stk c r₀) ∨
  ∃ s₁ f₁ cv stk₁ b np nr s₂ f₂ fl, EvalOXE C s f stk c (s₁, f₁, .normal (cv :: stk₁)) ∧
    truthy cv = some b ∧ arity f₁ bt = some (np, nr) ∧
    EvalOXE C s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, fl) ∧
    r₀ = (s₂, f₂, blockFlow np nr stk₁ fl)

theorem ifHead_ansXE {bt : BlockType} {c t el : List BExpr} (hc : LAnsXE C c) (ht : LAnsXE C t)
    (hel : LAnsXE C el) {s : Store H} {f : Frame} {stk : List Val} (cs₁ : List (Call (CallSig H)))
    (v : Except PUnit.{2} (Res × St H)) (hA₁ : Answered C cs₁)
    (h₁ : Path (run' (denListXE c f stk >>= fun r =>
        match r with
        | ⟨(f₁, .normal (cv :: stk₁))⟩ =>
          match truthy cv, arity f₁ bt with
          | some b, some (np, nr) =>
            (if b then denListXE t f₁ (stk₁.take np) else
              denListXE el f₁ (stk₁.take np)) >>= blockK np nr stk₁
          | _, _ => stuck
        | ⟨(_, .normal [])⟩ => stuck
        | r => pure r : M (CallSig H) H Res) ⟨s⟩) cs₁ (.val v)) :
    ∃ r₀, IfHeadXE C s f stk bt c t el r₀ ∧ endR r₀ = .val v := by
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
          have hL : LAnsXE C (if b then t else el) := by cases b <;> assumption
          have h₂' : Path (run' (denListXE (if b then t else el) f₁ (stk₁.take np) >>=
              blockK np nr stk₁ : M (CallSig H) H Res) ⟨s₁⟩) c₂ (.val v) := by
            cases b <;> exact h₂
          obtain ⟨s₂, f₂, fl, hev₂, hend₂⟩ := blockArm_ansXE hL c₂ v (answered_right hA₁) h₂'
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

theorem if_ansXE {bt : BlockType} {c t el es : List BExpr} (hc : LAnsXE C c) (ht : LAnsXE C t)
    (hel : LAnsXE C el) (hes : LAnsXE C es)
    {s : Store H} {f : Frame} {stk : List Val} {cs : List (Call (CallSig H))}
    {ee : PathEnd (Except PUnit.{2} (Res × St H))} (hA : Answered C cs)
    (h : Path (run' (denXE (.if_ bt c t el) f stk >>= thenK (denListXE es)) ⟨s⟩) cs ee)
    (he : ee ≠ .div) : ∃ r, EvalOXE C s f stk (.if_ bt c t el :: es) r ∧ endR r = ee := by
  rw [denXE_if] at h
  obtain ⟨r₀, hQ, hnorm, hnon⟩ := cont_ansXE (Q := IfHeadXE C s f stk bt c t el) hes hA h he
    (ifHead_ansXE hc ht hel)
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

/-- One loop iteration's path, inverted: the body runs to an `EvalOXE` outcome. -/
theorem loopIter_ansXE {bt : BlockType} {body : List BExpr} (hbody : LAnsXE C body)
    {p : ULift.{1} (Frame × List Val) × St H} {cs : List (Call (CallSig H))}
    {r' : PathEnd (Except PUnit.{2} ((Res ⊕ ULift.{1} (Frame × List Val)) × St H))}
    (hA : Answered C cs) (h : Path (run' (loopBodyXE bt body p.1) p.2) cs r')
    (hr : r' ≠ .div) :
    ∃ np nr s₁ f₁ fl, arity p.1.down.1 bt = some (np, nr) ∧
      EvalOXE C p.2.down p.1.down.1 (p.1.down.2.take np) body (s₁, f₁, fl) ∧
      ((fl = .trap ∧ r' = .val (.error ⟨⟩)) ∨
       (fl ≠ .trap ∧ r' = .val (.ok (loopOut np nr p.1.down.2 f₁ fl, ⟨s₁⟩)))) := by
  obtain ⟨⟨f, stk⟩, ⟨s⟩⟩ := p
  simp only [loopBodyXE] at h
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
theorem loop_ansXE {bt : BlockType} {body es : List BExpr} (hbody : LAnsXE C body) (hes : LAnsXE C es)
    {s : Store H} {f : Frame} {stk : List Val} {cs : List (Call (CallSig H))}
    {ee : PathEnd (Except PUnit.{2} (Res × St H))} (hA : Answered C cs)
    (h : Path (run' (denXE (.loop bt body) f stk >>= thenK (denListXE es)) ⟨s⟩) cs ee)
    (he : ee ≠ .div) : ∃ r, EvalOXE C s f stk (.loop bt body :: es) r ∧ endR r = ee := by
  let G := loopTree (loopBodyXE (H := H) bt body)
  let kk : Except PUnit.{2} (Res × St H) → Tree (SigEv (CallSig H)) (Except PUnit.{2} (Res × St H)) :=
    fun r => match r with
      | .ok (a, s') => run' (thenK (denListXE es) a) s'
      | .error e => pure (.error e)
  have key : ∀ (p : ULift.{1} (Frame × List Val) × St H) cs₁ (r : PathEnd (Except PUnit.{2} (Res × St H))),
      IterPath G p cs₁ r → ∀ v, r = .val v → ∀ cs₂ ee, Answered C (cs₁ ++ cs₂) →
      Path (kk v) cs₂ ee → ee ≠ .div →
      ∃ r', EvalOXE C p.2.down p.1.down.1 p.1.down.2 (.loop bt body :: es) r' ∧ endR r' = ee := by
    intro p cs₁ r hit
    induction hit with
    | @exit p cs y hp =>
      intro v hv cs₂ ee hA h₂ he
      cases hv
      obtain ⟨r', hp', hm⟩ := path_map_inv hp
      rcases loopEnd_inl hm.symm with ⟨e, rfl, rfl⟩ | ⟨b, s', rfl, rfl⟩
      · obtain ⟨np, nr, s₁, f₁, fl, har, hev, ⟨rfl, -⟩ | ⟨-, hr'⟩⟩ :=
          loopIter_ansXE hbody (answered_left hA) hp' (by simp)
        · obtain ⟨-, rfl⟩ := path_ret_inv rfl h₂
          exact ⟨_, .loopEsc har hev trivial, rfl⟩
        · cases hr'
      · obtain ⟨np, nr, s₁, f₁, fl, har, hev, ⟨-, hr'⟩ | ⟨hnt, hr'⟩⟩ :=
          loopIter_ansXE hbody (answered_left hA) hp' (by simp)
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
        loopIter_ansXE hbody (answered_left (answered_left (by rw [List.append_assoc] at hA ⊢; exact hA)))
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
  rw [denXE_loop, StoreBody.run_bind] at h
  rcases path_bind_inv h with ⟨cs₁, cs₂, v, rfl, h₁, h₂⟩ | ⟨rfl, -⟩
  · have h₁' := h₁
    change Path ((((Silmaril.Elgot.iter (loopBodyXE bt body) ⟨(f, stk)⟩ :
      M (CallSig H) H _).run ⟨s⟩).run)) cs₁ (.val v) at h₁'
    rw [Silmaril.Wasm.Abstract.BodyTrace.run_iter] at h₁'
    rcases v with e | ⟨a, s'⟩ <;> exact key _ _ _ (path_iter_iff.1 h₁') _ rfl cs₂ ee hA h₂ he
  · exact absurd rfl he

end

section
variable {C : CallRel H}

/-- The outcomes of a `try_table`'s head: the body's exit read as a block's, or a thrown
exception resolved by the clauses. -/
def TryHeadXE (C : CallRel H) (s : Store H) (f : Frame) (stk : List Val) (bt : BlockType)
    (cs : List Catch) (body : List BExpr) (r₀ : Store H × Frame × Flow) : Prop :=
  ∃ np nr s₁ f₁ fl, arity f bt = some (np, nr) ∧ EvalOXE C s f (stk.take np) body (s₁, f₁, fl) ∧
    (((∀ a, fl ≠ .throw a) ∧ r₀ = (s₁, f₁, blockFlow np nr stk fl)) ∨
     (∃ a us l, fl = .throw a ∧ Cfg.Region.Catches s₁ f₁ a cs (some (us, l)) ∧
        r₀ = (s₁, f₁, .brk l.toNat (us.reverse ++ stk.drop np))) ∨
     (∃ a, fl = .throw a ∧ Cfg.Region.Catches s₁ f₁ a cs none ∧ r₀ = (s₁, f₁, .throw a)))

theorem tryArm_ansXE {body : List BExpr} (hL : LAnsXE C body) {np nr : Nat} {stk : List Val}
    {cs : List Catch} {s : Store H} {f : Frame} (cl : List (Call (CallSig H)))
    (v : Except PUnit.{2} (Res × St H)) (hA : Answered C cl)
    (h : Path (run' (denListXE body f (stk.take np) >>= tryK np nr stk cs :
      M (CallSig H) H Res) ⟨s⟩) cl (.val v)) :
    ∃ s₁ f₁ fl r₀, EvalOXE C s f (stk.take np) body (s₁, f₁, fl) ∧ endR r₀ = .val v ∧
      (((∀ a, fl ≠ .throw a) ∧ r₀ = (s₁, f₁, blockFlow np nr stk fl)) ∨
       (∃ a us l, fl = .throw a ∧ Cfg.Region.Catches s₁ f₁ a cs (some (us, l)) ∧
          r₀ = (s₁, f₁, .brk l.toNat (us.reverse ++ stk.drop np))) ∨
       (∃ a, fl = .throw a ∧ Cfg.Region.Catches s₁ f₁ a cs none ∧ r₀ = (s₁, f₁, .throw a))) := by
  rcases path_run_bind_inv h (by simp) with ⟨c₁, c₂, a, t, rfl, h₁, h₂⟩ | ⟨h₁, hv⟩
  · obtain ⟨⟨s₁, f₁, fl⟩, hev, hend⟩ := hL s f (stk.take np) c₁ _ (answered_left hA) h₁ (by simp)
    obtain ⟨hnt, rfl, rfl⟩ := endR_ok_inv hend
    by_cases hth : ∃ a, fl = .throw a
    · obtain ⟨a, rfl⟩ := hth
      rw [run_tryK_throw] at h₂
      cases hr : resolveCatch s₁ f₁ a cs with
      | none =>
        simp only [hr] at h₂
        exact absurd (path_stuck_inv h₂) (by simp)
      | some o =>
        have hc := resolveCatch_spec hr
        cases o with
        | some p =>
          obtain ⟨us, l⟩ := p
          simp only [hr] at h₂
          obtain ⟨-, hv⟩ := path_pure_inv h₂
          cases hv
          exact ⟨s₁, f₁, _, (s₁, f₁, .brk l.toNat (us.reverse ++ stk.drop np)), hev, rfl, .inr (.inl ⟨a, us, l, rfl, hc, rfl⟩)⟩
        | none =>
          simp only [hr] at h₂
          obtain ⟨-, hv⟩ := path_pure_inv h₂
          cases hv
          exact ⟨s₁, f₁, _, (s₁, f₁, .throw a), hev, rfl, .inr (.inr ⟨a, rfl, hc, rfl⟩)⟩
    · have hnt' : ∀ a, fl ≠ .throw a := fun a ha => hth ⟨a, ha⟩
      rw [tryK_ne hnt', blockK_eq] at h₂
      obtain ⟨-, hv⟩ := path_pure_inv h₂
      cases hv
      exact ⟨s₁, f₁, fl, (s₁, f₁, blockFlow np nr stk fl), hev, endR_ok (fun h => hnt (blockFlow_trap.1 h)),
        .inl ⟨hnt', rfl⟩⟩
  · obtain ⟨⟨s₁, f₁, fl⟩, hev, hend⟩ := hL s f (stk.take np) cl _ hA h₁ (by simp)
    obtain rfl := endR_err_inv hend
    cases hv
    exact ⟨s₁, f₁, .trap, (s₁, f₁, .trap), hev, rfl, .inl ⟨fun _ h => Flow.noConfusion h, rfl⟩⟩

theorem try_ansXE {bt : BlockType} {cs : List Catch} {body es : List BExpr}
    (hbody : LAnsXE C body) (hes : LAnsXE C es)
    {s : Store H} {f : Frame} {stk : List Val} {cl : List (Call (CallSig H))}
    {ee : PathEnd (Except PUnit.{2} (Res × St H))} (hA : Answered C cl)
    (h : Path (run' (denXE (.tryTable bt cs body) f stk >>= thenK (denListXE es)) ⟨s⟩) cl ee)
    (he : ee ≠ .div) : ∃ r, EvalOXE C s f stk (.tryTable bt cs body :: es) r ∧ endR r = ee := by
  rw [denXE_try] at h
  cases har : arity f bt with
  | none =>
    simp only [har] at h
    rcases path_run_bind_inv h he with ⟨_, _, _, _, _, h₁, _⟩ | ⟨h₁, _⟩
    · exact absurd (path_stuck_inv h₁) (by simp)
    · exact absurd (path_stuck_inv h₁) (by simp)
  | some p =>
    obtain ⟨np, nr⟩ := p
    simp only [har] at h
    obtain ⟨r₀, ⟨np', nr', s₁, f₁, fl, har', hev, hcase⟩, hnorm, hnon⟩ :=
      cont_ansXE (Q := TryHeadXE C s f stk bt cs body) hes hA h he fun cs₁ v hA₁ h₁ => by
        obtain ⟨s₁, f₁, fl, r₀, hev, hend, hcase⟩ := tryArm_ansXE hbody cs₁ v hA₁ h₁
        exact ⟨r₀, ⟨np, nr, s₁, f₁, fl, har, hev, hcase⟩, hend⟩
    rw [har] at har'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj har')
    rcases hcase with ⟨hnt, rfl⟩ | ⟨a, us, l, rfl, hc, rfl⟩ | ⟨a, rfl, hc, rfl⟩
    · cases fl with
      | normal vs =>
        obtain ⟨r, hk, hr⟩ := hnorm _ rfl
        exact ⟨r, .tryOk har hev rfl hk, hr⟩
      | brk k vs =>
        cases k with
        | zero =>
          obtain ⟨r, hk, hr⟩ := hnorm _ rfl
          exact ⟨r, .tryOk har hev rfl hk, hr⟩
        | succ k => exact ⟨_, .tryBrk har hev, (hnon Flow.notNormal_brk).symm⟩
      | ret vs => exact ⟨_, .tryEsc har hev trivial hnt, (hnon Flow.notNormal_ret).symm⟩
      | trap => exact ⟨_, .tryEsc har hev trivial hnt, (hnon Flow.notNormal_trap).symm⟩
      | throw a => exact absurd rfl (hnt a)
    · exact ⟨_, .tryCatch har hev hc, (hnon Flow.notNormal_brk).symm⟩
    · exact ⟨_, .tryRethrow har hev hc, (hnon Flow.notNormal_throw).symm⟩

end

section
variable {C : CallRel H}

mutual

theorem tree_ansXE : ∀ (e : BExpr) (es : List BExpr), LAnsXE C es →
    ∀ (s : Store H) (f : Frame) (stk : List Val) (cs : List (Call (CallSig H)))
      (ee : PathEnd (Except PUnit.{2} (Res × St H))), Answered C cs →
    Path (run' (denXE e f stk >>= thenK (denListXE es)) ⟨s⟩) cs ee → ee ≠ .div →
    ∃ r, EvalOXE C s f stk (e :: es) r ∧ endR r = ee
  | .op _ args, _, hes, _, _, _, _, _, hA, h, he => op_ansXE (list_ansXE args) hes hA h he
  | .block _ body, _, hes, _, _, _, _, _, hA, h, he => block_ansXE (list_ansXE body) hes hA h he
  | .loop _ body, _, hes, _, _, _, _, _, hA, h, he => loop_ansXE (list_ansXE body) hes hA h he
  | .if_ _ c t el, _, hes, _, _, _, _, _, hA, h, he =>
    if_ansXE (list_ansXE c) (list_ansXE t) (list_ansXE el) hes hA h he
  | .tryTable _ _ body, _, hes, _, _, _, _, _, hA, h, he =>
    try_ansXE (list_ansXE body) hes hA h he

theorem list_ansXE : ∀ (es : List BExpr), LAnsXE C es
  | [] => fun s f stk cs e _ h _ => by
    obtain ⟨rfl, rfl⟩ := path_pure_inv h
    exact ⟨(s, f, .normal stk), .nil, rfl⟩
  | e :: es => fun s f stk cs ee hA h he => by
    rw [denListXE_cons] at h
    exact tree_ansXE e es (list_ansXE es) s f stk cs ee hA h he

end
end

/-! ## Exactness -/

section
variable {C : CallRel H}

theorem evalOXE_iff {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {s' : Store H} {f' : Frame} {fl : Flow} (hfl : fl ≠ .trap) :
    EvalOXE C s f stk es (s', f', fl) ↔
      ∃ cs, Answered C cs ∧ Path (run' (denListXE es f stk : M (CallSig H) H Res) ⟨s⟩) cs
        (.val (.ok (⟨(f', fl)⟩, ⟨s'⟩))) := by
  have hend : endR (s', f', fl) = .val (.ok (⟨(f', fl)⟩, ⟨s'⟩)) := endR_ok hfl
  constructor
  · intro h
    obtain ⟨cs, hA, hp⟩ := evalOXE_path h
    exact ⟨cs, hA, hend ▸ hp⟩
  · rintro ⟨cs, hA, hp⟩
    obtain ⟨⟨s₁, f₁, fl₁⟩, hev, he⟩ := list_ansXE es s f stk cs _ hA hp (by simp)
    obtain ⟨-, h1, h2⟩ := endR_ok_inv he
    simp only [ULift.up.injEq, Prod.mk.injEq] at h1 h2
    obtain ⟨rfl, rfl⟩ := h1
    subst h2
    exact hev

theorem evalOXE_trap_iff {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr} :
    (∃ s' f', EvalOXE C s f stk es (s', f', .trap)) ↔
      ∃ cs, Answered C cs ∧ Path (run' (denListXE es f stk : M (CallSig H) H Res) ⟨s⟩) cs
        (.val (.error ⟨⟩)) := by
  constructor
  · rintro ⟨s', f', h⟩
    exact evalOXE_path h
  · rintro ⟨cs, hA, hp⟩
    obtain ⟨⟨s₁, f₁, fl₁⟩, hev, he⟩ := list_ansXE es s f stk cs _ hA hp (by simp)
    obtain rfl := endR_err_inv he
    exact ⟨s₁, f₁, hev⟩

end

end Silmaril.Proofs.Wasm.Abstract.ExposeE

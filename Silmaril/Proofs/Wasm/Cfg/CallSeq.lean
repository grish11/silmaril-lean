module

public import Silmaril.Proofs.Wasm.Cfg.CtxSplit
public import Silmaril.Wasm.Execution.Core.Inversion.Thms
public import Silmaril.Wasm.Execution.Core.InversionHost.Thms

@[expose] public section

/-!
# A Core run through a call in a sequence, to a region final form

Every profile and host, Wasm and host callees. A Core run of `vals ws ++ call x :: rest` (or of
the resolved `call_ref`, or of a callee frame in progress) to a code that is a final form of a
region outcome (`Out.Ends`) first runs the callee's `call_ref` on the top `ps.length` values to a
result `r`, in the caller's frame, and then continues from `vals ws' ++ r ++ rest`. Tail calls
out of the callee's frame are followed to the final callee.
-/

namespace Silmaril.Wasm.Cfg.Proofs.Region

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Region Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- **The first non-value of a final form** is a branch, a return, a trap, a `throw_ref` or a
`return_call_ref`. -/
theorem ends_head {o : Out} {vs : List Val} {a : Admin} {es : List Admin}
    (h : o.Ends (vals vs ++ a :: es)) (ha : a.val? = none) :
    (∃ l, a = .plain (.br l)) ∨ a = .plain .return_ ∨ a = .trap ∨ a = .plain .throwRef ∨
      a.IsReturnCallRef := by
  cases o with
  | normal us =>
    simp only [Out.Ends] at h
    have hm : a ∈ vals us := by rw [← h]; simp
    simp only [vals, List.mem_map] at hm
    obtain ⟨v, -, rfl⟩ := hm
    simp [Admin.val?_toAdmin] at ha
  | br l us =>
    obtain ⟨x, rest, -, hc⟩ := h
    obtain ⟨-, rfl, -⟩ := Sim.vals_append_cons_inj ha rfl hc
    exact .inl ⟨x, rfl⟩
  | ret us =>
    obtain ⟨rest, hc⟩ := h
    obtain ⟨-, rfl, -⟩ := Sim.vals_append_cons_inj ha rfl hc
    exact .inr (.inl rfl)
  | trap =>
    simp only [Out.Ends] at h
    have hc : vals vs ++ a :: es = vals [] ++ Admin.trap :: [] := by simpa [vals] using h
    obtain ⟨-, rfl, -⟩ := Sim.vals_append_cons_inj ha rfl hc
    exact .inr (.inr (.inl rfl))
  | throw t =>
    simp only [Out.Ends] at h
    have hc : vals vs ++ a :: es = vals [.ref (.exn t)] ++ Admin.plain .throwRef :: [] := by
      simpa [vals, Val.toAdmin, throwing] using h
    obtain ⟨-, rfl, -⟩ := Sim.vals_append_cons_inj ha rfl hc
    exact .inr (.inr (.inr (.inl rfl)))
  | tail us a' r =>
    obtain ⟨hr, rest, hc⟩ := h
    have hc' : vals vs ++ a :: es = vals (us ++ [.ref (.func a')]) ++ r :: rest := by
      simpa [vals, Val.toAdmin] using hc
    obtain ⟨-, rfl, -⟩ := Sim.vals_append_cons_inj ha (Admin.val?_of_isReturnCallRef hr) hc'
    exact .inr (.inr (.inr (.inr hr)))
  | tailNull us r =>
    obtain ⟨hr, rest, hc⟩ := h
    have hc' : vals vs ++ a :: es = vals (us ++ [.ref .null]) ++ r :: rest := by
      simpa [vals, Val.toAdmin] using hc
    obtain ⟨-, rfl, -⟩ := Sim.vals_append_cons_inj ha (Admin.val?_of_isReturnCallRef hr) hc'
    exact .inr (.inr (.inr (.inr hr)))

theorem not_ends_callRef {o : Out} {ws : List Val} {a : Nat} {cr : Admin} {rest : List Admin}
    (hcr : cr.IsCallRef) : ¬ o.Ends (vals ws ++ .ref (.func a) :: cr :: rest) := by
  intro h
  have h' : o.Ends (vals (ws ++ [.ref (.func a)]) ++ cr :: rest) := by
    simpa [vals, Val.toAdmin] using h
  rcases ends_head h' (Admin.val?_of_isCallRef hcr) with ⟨l, rfl⟩ | rfl | rfl | rfl | hr
  · exact hcr
  · exact hcr
  · exact hcr
  · exact hcr
  · unfold Admin.IsCallRef at hcr; unfold Admin.IsReturnCallRef at hr
    split at hcr <;> simp_all

theorem not_ends_frame {o : Out} {ws : List Val} {n : Nat} {F : Frame} {X rest : List Admin} :
    ¬ o.Ends (vals ws ++ .frame n F X :: rest) := by
  intro h
  rcases ends_head h rfl with ⟨l, hl⟩ | hl | hl | hl | hr
  · cases hl
  · cases hl
  · cases hl
  · cases hl
  · exact hr

theorem expand_func_inj {d : DefType} {ps rs ps' rs' : Ty (.list .val)}
    (h : Expand d (.func ps rs)) (h' : Expand d (.func ps' rs')) : ps = ps' ∧ rs = rs' := by
  rw [Expand.iff] at h h'
  rw [h] at h'
  simp only [Option.some.injEq] at h'
  cases h'
  exact ⟨rfl, rfl⟩

/-- **A `call_ref` or a callee frame in a sequence, run to a final form** (every profile and
host). (A) The `call_ref` of `a` under `ws` runs its callee on the top `ps.length` values `us` to a
result `r` in the caller's frame, and the sequence continues from `vals ws' ++ r ++ rest`. (B) A
frame in progress runs alone to a result, and the sequence continues after it. -/
theorem call_seq_split {c' : Config H} (hfin : ∃ o : Out, o.Ends c'.code) :
    ∀ {c₀ : Config H}, Steps P host c₀ c' →
      (∀ (s : Store H) (f : Frame) (ws : List Val) (a : Nat) (cr : Admin) (rest : List Admin)
          (fi : FuncInst H), c₀ = ⟨s, f, vals ws ++ .ref (.func a) :: cr :: rest⟩ →
          cr.IsCallRef → s.funcs[a]? = some fi →
          ∃ (ws' us : List Val) (ps rs : Ty (.list .val)) (s₁ : Store H) (r : Result),
            ws = ws' ++ us ∧ Expand fi.type (.func ps rs) ∧ us.length = ps.length ∧
            Steps P host ⟨s, f, vals us ++ [.ref (.func a), cr]⟩ ⟨s₁, f, r.toAdmin⟩ ∧
            Steps P host ⟨s₁, f, vals ws' ++ r.toAdmin ++ rest⟩ c') ∧
      (∀ (s : Store H) (f : Frame) (ws : List Val) (n : Nat) (F : Frame) (X rest : List Admin),
          c₀ = ⟨s, f, vals ws ++ .frame n F X :: rest⟩ →
          ∃ (s₁ : Store H) (r : Result),
            Steps P host ⟨s, f, [.frame n F X]⟩ ⟨s₁, f, r.toAdmin⟩ ∧
            Steps P host ⟨s₁, f, vals ws ++ r.toAdmin ++ rest⟩ c') := by
  obtain ⟨o, ho⟩ := hfin
  intro c₀ h
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    refine ⟨fun s f ws a cr rest fi hc hcr _ => ?_, fun s f ws n F X rest hc => ?_⟩
    · subst hc; exact absurd ho (not_ends_callRef hcr)
    · subst hc; exact absurd ho not_ends_frame
  | @head c₀ c₁ hstep hrest ih =>
    refine ⟨fun s f ws a cr rest fi hc hcr hfi => ?_, fun s f ws n F X rest hc => ?_⟩
    · subst hc
      cases hcode : fi.code with
      | wasm code =>
        obtain ⟨vs₁, vs₂, ps, rs, rfl, he, hn, rfl⟩ := Step.callRef_wasm_inv_seq hcr hfi hcode hstep
        obtain ⟨s₁, r, h1, h2⟩ := ih.2 s f vs₁ _ _ _ rest rfl
        exact ⟨vs₁, vs₂, ps, rs, s₁, r, rfl, he, hn,
          .head (Step.callRefFunc hcr hfi he hn hcode) h1, h2⟩
      | host hh =>
        obtain ⟨vs₁, vs₂, ps, rs, rfl, he, hn, hres⟩ := Step.callRef_host_inv_seq hcr hfi hcode hstep
        rcases hres with ⟨s', res, hhost, rfl⟩ | ⟨hhost, rfl⟩
        · exact ⟨vs₁, vs₂, ps, rs, s', res, rfl, he, hn,
            .single (Step.callRefHost hcr hfi he hn hcode hhost), hrest⟩
        · exact (ih.1 s f (vs₁ ++ vs₂) a cr rest fi (by simp) hcr hfi)
    · subst hc
      obtain ⟨d, hd, rfl⟩ := Step.ctx_in_seq (X := .frame n F X) trivial hstep
      rcases Step.frame_inv hd with ⟨s', F', X', hin, rfl⟩ | ⟨out, hx, rfl⟩
      · obtain ⟨s₁, r, h1, h2⟩ := ih.2 s' f ws n F' X' rest (by simp)
        exact ⟨s₁, r, .head hd h1, h2⟩
      · cases hx with
        | vals hn' => exact ⟨_, .values _, .single hd, hrest⟩
        | ret hn' => exact ⟨_, .values _, .single hd, hrest⟩
        | trap => exact ⟨_, .trap, .single hd, hrest⟩
        | throw t => exact ⟨_, .throw t, .single hd, hrest⟩
        | returnCallNull hc' => exact ⟨_, .trap, .single hd, hrest⟩
        | @returnCallAddr vs' vs a' c'' rest' fn ps rs hc' hf' he' hn' =>
          obtain ⟨ws', us, ps'', rs'', s₁, r, hsplit, he'', hn'', h1, h2⟩ :=
            ih.1 s f (ws ++ vs) a' _ rest fn (by simp) (isCallRef_retToCallIn hc' F.module) hf'
          obtain ⟨rfl, -⟩ := expand_func_inj he' he''
          obtain ⟨rfl, rfl⟩ := List.append_inj' hsplit (by omega)
          exact ⟨s₁, r, .head hd h1, h2⟩

/-- **A direct call in a sequence, run to a final form** (every profile and host): it resolves
its callee `a`, whose `call_ref` runs on the top `ps.length` values `us` to a result `r` in the
caller's frame; the sequence continues from `vals ws' ++ r ++ rest`. -/
theorem call_seq_result {s : Store H} {f : Frame} {ws : List Val} {x : FuncIdx}
    {rest : List Admin} {c' : Config H} (hfin : ∃ o : Out, o.Ends c'.code)
    (h : Steps P host ⟨s, f, vals ws ++ .plain (.call x) :: rest⟩ c') :
    ∃ (a : Nat) (fi : FuncInst H), f.module.funcs[x.toNat]? = some a ∧ s.funcs[a]? = some fi ∧
      ∃ (ws' us : List Val) (ps rs : Ty (.list .val)) (s₁ : Store H) (r : Result),
        ws = ws' ++ us ∧ Expand fi.type (.func ps rs) ∧ us.length = ps.length ∧
        Steps P host ⟨s, f, vals us ++ [.ref (.func a), .callRefType fi.type]⟩ ⟨s₁, f, r.toAdmin⟩ ∧
        Steps P host ⟨s₁, f, vals ws' ++ r.toAdmin ++ rest⟩ c' := by
  rcases h.cases_head with rfl | ⟨c₁, h₁, hr⟩
  · obtain ⟨o, ho⟩ := hfin
    rcases ends_head ho rfl with ⟨l, hl⟩ | hl | hl | hl | hl <;> cases hl
  obtain ⟨a, fi, hx, hfi, rfl⟩ := Step.call_vals_inv_seq h₁
  exact ⟨a, fi, hx, hfi, (call_seq_split hfin hr).1 s f ws a _ rest fi rfl trivial hfi⟩

theorem vals_ne_cons_nonval {us ws : List Val} {a : Admin} {es : List Admin} (ha : a.val? = none) :
    vals us ≠ vals ws ++ a :: es := by
  intro h
  have hm : a ∈ vals us := by rw [h]; simp
  simp only [vals, List.mem_map] at hm
  obtain ⟨v, -, rfl⟩ := hm
  simp [Admin.val?_toAdmin] at ha

theorem ends_trap_inv {o : Out} {ws : List Val} {r : List Admin}
    (h : o.Ends (vals ws ++ .trap :: r)) : o = .trap ∧ ws = [] ∧ r = [] := by
  cases o with
  | normal us => exact absurd h (vals_ne_cons_nonval rfl).symm
  | br l us =>
    obtain ⟨x, rest, -, hc⟩ := h
    obtain ⟨-, h2, -⟩ := Sim.vals_append_cons_inj rfl rfl hc; cases h2
  | ret us =>
    obtain ⟨rest, hc⟩ := h
    obtain ⟨-, h2, -⟩ := Sim.vals_append_cons_inj rfl rfl hc; cases h2
  | trap =>
    simp only [Out.Ends] at h
    have hc : vals ws ++ Admin.trap :: r = vals [] ++ Admin.trap :: [] := by simpa [vals] using h
    obtain ⟨rfl, -, rfl⟩ := Sim.vals_append_cons_inj rfl rfl hc
    exact ⟨rfl, rfl, rfl⟩
  | throw t =>
    simp only [Out.Ends] at h
    have hc : vals ws ++ Admin.trap :: r = vals [.ref (.exn t)] ++ Admin.plain .throwRef :: [] := by
      simpa [vals, Val.toAdmin, throwing] using h
    obtain ⟨-, h2, -⟩ := Sim.vals_append_cons_inj rfl rfl hc; cases h2
  | tail us a c =>
    obtain ⟨hr, rest, hc⟩ := h
    have hc' : vals ws ++ Admin.trap :: r = vals (us ++ [.ref (.func a)]) ++ c :: rest := by
      simpa [vals, Val.toAdmin] using hc
    obtain ⟨-, rfl, -⟩ := Sim.vals_append_cons_inj rfl (Admin.val?_of_isReturnCallRef hr) hc'
    exact absurd hr (by simp [Admin.IsReturnCallRef])
  | tailNull us c =>
    obtain ⟨hr, rest, hc⟩ := h
    have hc' : vals ws ++ Admin.trap :: r = vals (us ++ [.ref .null]) ++ c :: rest := by
      simpa [vals, Val.toAdmin] using hc
    obtain ⟨-, rfl, -⟩ := Sim.vals_append_cons_inj rfl (Admin.val?_of_isReturnCallRef hr) hc'
    exact absurd hr (by simp [Admin.IsReturnCallRef])

theorem ends_throw_inv {o : Out} {ws : List Val} {t : Nat} {r : List Admin}
    (h : o.Ends (vals (ws ++ [.ref (.exn t)]) ++ .plain .throwRef :: r)) :
    o = .throw t ∧ ws = [] ∧ r = [] := by
  cases o with
  | normal us => exact absurd h (vals_ne_cons_nonval rfl).symm
  | br l us =>
    obtain ⟨x, rest, -, hc⟩ := h
    obtain ⟨-, h2, -⟩ := Sim.vals_append_cons_inj rfl rfl hc; cases h2
  | ret us =>
    obtain ⟨rest, hc⟩ := h
    obtain ⟨-, h2, -⟩ := Sim.vals_append_cons_inj rfl rfl hc; cases h2
  | trap =>
    simp only [Out.Ends] at h
    have hc : vals (ws ++ [.ref (.exn t)]) ++ Admin.plain .throwRef :: r =
        vals [] ++ Admin.trap :: [] := by simpa [vals] using h
    obtain ⟨-, h2, -⟩ := Sim.vals_append_cons_inj rfl rfl hc; cases h2
  | throw t' =>
    simp only [Out.Ends] at h
    have hc : vals (ws ++ [.ref (.exn t)]) ++ Admin.plain .throwRef :: r =
        vals [.ref (.exn t')] ++ Admin.plain .throwRef :: [] := by
      simpa [vals, Val.toAdmin, throwing] using h
    obtain ⟨h1, -, rfl⟩ := Sim.vals_append_cons_inj rfl rfl hc
    have hl := congrArg List.length h1
    simp at hl
    subst hl
    simp at h1
    obtain rfl := h1
    exact ⟨rfl, rfl, rfl⟩
  | tail us a c =>
    obtain ⟨hr, rest, hc⟩ := h
    have hc' : vals (ws ++ [.ref (.exn t)]) ++ Admin.plain .throwRef :: r =
        vals (us ++ [.ref (.func a)]) ++ c :: rest := by simpa [vals, Val.toAdmin] using hc
    obtain ⟨-, rfl, -⟩ := Sim.vals_append_cons_inj rfl (Admin.val?_of_isReturnCallRef hr) hc'
    exact absurd hr (by simp [Admin.IsReturnCallRef])
  | tailNull us c =>
    obtain ⟨hr, rest, hc⟩ := h
    have hc' : vals (ws ++ [.ref (.exn t)]) ++ Admin.plain .throwRef :: r =
        vals (us ++ [.ref .null]) ++ c :: rest := by simpa [vals, Val.toAdmin] using hc
    obtain ⟨-, rfl, -⟩ := Sim.vals_append_cons_inj rfl (Admin.val?_of_isReturnCallRef hr) hc'
    exact absurd hr (by simp [Admin.IsReturnCallRef])

/-- **A trap in a sequence only bubbles to a final form**: `[trap]`, same store and frame. -/
theorem steps_trap_ends {o : Out} {c' : Config H} (ho : o.Ends c'.code) :
    ∀ {c₀ : Config H}, Steps P host c₀ c' → ∀ (s : Store H) (f : Frame) (ws : List Val)
      (r : List Admin), c₀ = ⟨s, f, vals ws ++ .trap :: r⟩ → c' = ⟨s, f, [.trap]⟩ ∧ o = .trap := by
  intro c₀ h
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro s f ws r hc; subst hc
    obtain ⟨rfl, rfl, rfl⟩ := ends_trap_inv ho
    exact ⟨by simp [vals], rfl⟩
  | @head c₀ c₁ hstep _ ih =>
    intro s f ws r hc; subst hc
    obtain ⟨s', f', es'⟩ := c₁
    rcases Sim.Step.split_head (a := .trap) rfl hstep with
      ⟨ws₁, us, is', rfl, hst, rfl⟩ | ⟨-, rfl, rfl, ws₁, us, r₁, r₂, rfl, rfl, -, rfl⟩ | ⟨h1, -⟩
    · obtain ⟨w, hc, -⟩ := Step.trap_vals_inv hst
      simp only [Config.mk.injEq] at hc
      obtain ⟨rfl, rfl, rfl⟩ := hc
      exact ih _ _ (ws₁ ++ w) r (by simp)
    · exact ih _ _ ws₁ r₂ (by simp)
    · cases h1

/-- **An exception in a sequence only bubbles to a final form**: `throwing t`, same store and
frame. -/
theorem steps_throw_ends {o : Out} {c' : Config H} {t : Nat} (ho : o.Ends c'.code) :
    ∀ {c₀ : Config H}, Steps P host c₀ c' → ∀ (s : Store H) (f : Frame) (ws : List Val)
      (r : List Admin), c₀ = ⟨s, f, vals (ws ++ [.ref (.exn t)]) ++ .plain .throwRef :: r⟩ →
      c' = ⟨s, f, throwing t⟩ ∧ o = .throw t := by
  intro c₀ h
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro s f ws r hc; subst hc
    obtain ⟨rfl, rfl, rfl⟩ := ends_throw_inv ho
    exact ⟨by simp [vals, Val.toAdmin, throwing], rfl⟩
  | @head c₀ c₁ hstep _ ih =>
    intro s f ws r hc; subst hc
    obtain ⟨s', f', es'⟩ := c₁
    rcases Sim.Step.split_head (a := .plain .throwRef) rfl hstep with
      ⟨ws₁, us, is', hsplit, hst, rfl⟩ | ⟨h1, -⟩ |
        ⟨-, rfl, rfl, ws₁, us, x, r₁, r₂, hsplit, rfl, -, rfl⟩
    · rcases Step.throwRef_vals_inv hst with ⟨w, rfl, hc⟩ | ⟨w, w', a, rfl, -, hc⟩
      · have := congrArg List.getLast? hsplit; simp at this
      · simp only [Config.mk.injEq] at hc
        obtain ⟨rfl, rfl, rfl⟩ := hc
        have hl := congrArg List.getLast? hsplit; simp at hl; subst hl
        exact ih _ _ (ws₁ ++ w) r (by simp [vals, Val.toAdmin, throwing])
    · cases h1
    · have hl := congrArg List.getLast? hsplit; simp at hl; subst hl
      exact ih _ _ ws₁ r₂ (by simp [vals, Val.toAdmin, throwing])

theorem funcType_of_expand {d : DefType} {ps rs : Ty (.list .val)} (h : Expand d (.func ps rs)) :
    d.funcType? = some (ps.toList, rs.toList) := by
  simp [DefType.funcType?, Expand.iff.1 h]

/-- **A direct call in a sequence, from Core to the region semantics** (every profile and host):
under a complete oracle (`CallCompleteG`, its guard holding at the call's store), a Core run of
`vals ws ++ call x :: rest` to a final form of `o` is a `RunC` run of `call x :: rest`, given
that every continuation after the callee's values is one (`hk`). A trapping or throwing callee
needs no continuation. -/
theorem run_call_complete {G : Store H → Nat → List Val → Prop} {C : Abstract.CallRel H}
    (hC : CallCompleteG P host G C) {s s' : Store H} {f f' : Frame} {ws : List Val}
    {x : FuncIdx} {rest c' : List Admin} {o : Out} (hG : ∀ a us, G s a us)
    (h : Steps P host ⟨s, f, vals ws ++ .plain (.call x) :: rest⟩ ⟨s', f', c'⟩) (ho : o.Ends c')
    (hk : ∀ (s₁ : Store H) (ws' vs : List Val),
      Steps P host ⟨s₁, f, vals (ws' ++ vs) ++ rest⟩ ⟨s', f', c'⟩ →
        RunC P host C s₁ f (ws' ++ vs) rest s' f' o) :
    RunC P host C s f ws (.plain (.call x) :: rest) s' f' o := by
  obtain ⟨a, fi, hx, hfi, ws', us, ps, rs, s₁, r, rfl, he, hn, hcall, hk'⟩ :=
    call_seq_result ⟨o, ho⟩ h
  have hfunc : s.func? f x = some (a, fi) := by simp [Store.func?, hx, hfi]
  obtain ⟨-, hv, htr, hth⟩ := call_of_core (ws := ws') (code := rest) hC hfunc
    (funcType_of_expand he) hn (hG a us) hcall
  cases r with
  | values vs => exact hv vs rfl (hk s₁ ws' vs (by simpa [Result.toAdmin] using hk'))
  | trap =>
    obtain ⟨hc, rfl⟩ := steps_trap_ends ho hk' s₁ f ws' rest (by simp [Result.toAdmin])
    simp only [Config.mk.injEq] at hc
    obtain ⟨rfl, rfl, -⟩ := hc
    exact htr rfl
  | throw t =>
    obtain ⟨hc, rfl⟩ := steps_throw_ends (t := t) ho hk' s₁ f ws' rest
      (by simp [Result.toAdmin, vals, Val.toAdmin])
    simp only [Config.mk.injEq] at hc
    obtain ⟨rfl, rfl, -⟩ := hc
    exact hth t rfl

end Silmaril.Wasm.Cfg.Proofs.Region

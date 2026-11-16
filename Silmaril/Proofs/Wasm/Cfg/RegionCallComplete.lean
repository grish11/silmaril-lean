module

public import Silmaril.Proofs.Wasm.Cfg.CallSeq

@[expose] public section

/-!
# Core 3.0 runs of code with calls are region runs

For the fragment with calls (`FragC`: `call x`, `call_indirect`, `call_ref`), every Core run to a
final form of an outcome is a `RunC` run with any complete oracle (`CallCompleteG`). The proof
follows the Core run: a step whose redex is not a call is expanded (`expandB`; `call_indirect`
unfolds into `table.get; ref.cast; call_ref`, and a `call_ref` of null traps); at a call of a
function (inside labels and handlers, a context `Ctx`), the run goes through the callee's
`call_ref` and frame to a result, and the call is the region-run inclusion `call_incl` (direct) or
`callRef_incl` (by reference), lifted through the context.
-/

namespace Silmaril.Wasm.Cfg.Proofs.Region

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Region Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type} {P : Profile} {host : HostSemantics H} {C : Abstract.CallRel H}

/-- A context of the fragment with calls. -/
inductive CtxF : Ctx → Prop where
  | hole : CtxF .hole
  | label {ws : List Val} {n : Nat} {cont : List Instr} {E : Ctx} {rest : List Admin}
      (hc : ∀ i ∈ cont, FragIB true i) (hr : FragC rest) (hE : CtxF E) :
      CtxF (.label ws n cont E rest)
  | handler {ws : List Val} {n : Nat} {cs : List Catch} {E : Ctx} {rest : List Admin}
      (hr : FragC rest) (hE : CtxF E) : CtxF (.handler ws n cs E rest)

theorem fragC_fill : ∀ {E : Ctx} {X : List Admin}, CtxF E → FragC X → FragC (E.fill X)
  | .hole, _, _, h => h
  | .label ws n cont E rest, X, .label hc hr hE, h => by
    simp only [Ctx.fill]
    exact frag_append.2 ⟨frag_vals ws, fun a ha => by
      simp at ha
      rcases ha with rfl | ha
      · exact .label hc (fragC_fill hE h)
      · exact hr a ha⟩
  | .handler ws n cs E rest, X, .handler hr hE, h => by
    simp only [Ctx.fill]
    exact frag_append.2 ⟨frag_vals ws, fun a ha => by
      simp at ha
      rcases ha with rfl | ha
      · exact .handler (fragC_fill hE h)
      · exact hr a ha⟩

theorem fragC_result (r : Result) : FragC r.toAdmin := by
  cases r with
  | values vs => exact frag_vals vs
  | trap => intro a ha; simp [Result.toAdmin] at ha; subst ha; exact .trap
  | throw t =>
    intro a ha
    simp [Result.toAdmin] at ha
    rcases ha with rfl | rfl
    · exact .val (by simp [Admin.val?])
    · exact .plain .throwRef

/-- An instruction that blocks the exits of labels and handlers. -/
def Bad (y : Admin) : Prop :=
  (∃ x, y = .plain (.call x)) ∨ y.IsCallRef ∨ (∃ n F Y, y = .frame n F Y) ∨
    (∃ n cont Y, y = .label n cont Y) ∨ (∃ n cs Y, y = .handler n cs Y)

theorem bad_val {y : Admin} (h : Bad y) : y.val? = none := by
  rcases h with ⟨x, rfl⟩ | h | ⟨n, F, Y, rfl⟩ | ⟨n, c, Y, rfl⟩ | ⟨n, c, Y, rfl⟩
  · rfl
  · exact Admin.val?_of_isCallRef h
  all_goals rfl

/-- Codes whose first non-value blocks exits. -/
def Blocked (X : List Admin) : Prop := ∃ ws y rest, X = vals ws ++ y :: rest ∧ Bad y

theorem blocked_fill : ∀ (E : Ctx) {X : List Admin}, Blocked X → Blocked (E.fill X)
  | .hole, _, h => h
  | .label ws _ _ _ rest, _, _ => ⟨ws, _, rest, rfl, .inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))⟩
  | .handler ws _ _ _ rest, _, _ => ⟨ws, _, rest, rfl, .inr (.inr (.inr (.inr ⟨_, _, _, rfl⟩)))⟩

theorem bad_not {y : Admin} (h : Bad y) :
    (∀ l, y ≠ .plain (.br l)) ∧ y ≠ .plain .return_ ∧ y ≠ .trap ∧ y ≠ .plain .throwRef ∧
      ¬ y.IsReturnCallRef := by
  rcases h with ⟨x, rfl⟩ | h | ⟨n, F, Y, rfl⟩ | ⟨n, c, Y, rfl⟩ | ⟨n, c, Y, rfl⟩
  · exact ⟨fun l => by simp, by simp, by simp, by simp, by simp [Admin.IsReturnCallRef]⟩
  · refine ⟨fun l hl => by subst hl; exact h, fun hl => by subst hl; exact h,
      fun hl => by subst hl; exact h, fun hl => by subst hl; exact h, fun hr => ?_⟩
    unfold Admin.IsCallRef at h; unfold Admin.IsReturnCallRef at hr
    split at h <;> simp_all
  all_goals exact ⟨fun l => by simp, by simp, by simp, by simp, by simp [Admin.IsReturnCallRef]⟩

theorem blocked_not_vals {X : List Admin} (h : Blocked X) (vs : List Val) : X ≠ vals vs := by
  obtain ⟨ws, y, rest, rfl, hb⟩ := h
  exact (vals_ne_cons_nonval (bad_val hb)).symm

/-- Blocked codes are not inputs of the exit rules of labels. -/
theorem labelExit_blocked {n : Nat} {cont : List Instr} {X out : List Admin}
    (h : LabelExit n cont X out) (hb : Blocked X) : False := by
  obtain ⟨ws, y, rest, rfl, hy⟩ := hb
  have hv := bad_val hy
  obtain ⟨hbr, hret, htr, hth, hrc⟩ := bad_not hy
  generalize hX : vals ws ++ y :: rest = X at h
  cases h with
  | vals vs => exact vals_ne_cons_nonval hv hX.symm
  | @brZero vs' vs l rest' =>
    have h' : vals ws ++ y :: rest = vals (vs' ++ vs) ++ Admin.plain (.br l) :: rest' := by
      rw [hX]; simp
    obtain ⟨-, rfl, -⟩ := Sim.vals_append_cons_inj hv rfl h'
    exact hbr _ rfl
  | brSucc =>
    obtain ⟨-, rfl, -⟩ := Sim.vals_append_cons_inj hv rfl (by simpa using hX)
    exact hbr _ rfl
  | ret =>
    obtain ⟨-, rfl, -⟩ := Sim.vals_append_cons_inj hv rfl (by simpa using hX)
    exact hret rfl
  | returnCall hc =>
    obtain ⟨-, rfl, -⟩ := Sim.vals_append_cons_inj hv (Admin.val?_of_isReturnCallRef hc)
      (by simpa using hX)
    exact hrc hc
  | throw a =>
    have : vals ws ++ y :: rest = vals [.ref (.exn a)] ++ Admin.plain .throwRef :: [] := by
      simpa [vals, Val.toAdmin, throwing] using hX
    obtain ⟨-, rfl, -⟩ := Sim.vals_append_cons_inj hv rfl this
    exact hth rfl
  | trap =>
    have : vals ws ++ y :: rest = vals [] ++ Admin.trap :: [] := by simpa [vals] using hX
    obtain ⟨-, rfl, -⟩ := Sim.vals_append_cons_inj hv rfl this
    exact htr rfl

/-- Blocked codes are not inputs of the exit rules of handlers. -/
theorem handlerExit_blocked {s : Store H} {f : Frame} {n : Nat} {cs : List Catch}
    {X out : List Admin} (h : HandlerExit s f n cs X out) (hb : Blocked X) : False := by
  obtain ⟨ws, y, rest, rfl, hy⟩ := hb
  have hv := bad_val hy
  obtain ⟨hbr, hret, htr, hth, hrc⟩ := bad_not hy
  have hthr : ∀ a, vals ws ++ y :: rest ≠ throwing a := fun a hX => by
    have : vals ws ++ y :: rest = vals [.ref (.exn a)] ++ Admin.plain .throwRef :: [] := by
      simpa [vals, Val.toAdmin, throwing] using hX
    obtain ⟨-, rfl, -⟩ := Sim.vals_append_cons_inj hv rfl this
    exact hth rfl
  generalize hX : vals ws ++ y :: rest = X at h
  cases h with
  | vals vs => exact vals_ne_cons_nonval hv hX.symm
  | br =>
    obtain ⟨-, rfl, -⟩ := Sim.vals_append_cons_inj hv rfl (by simpa using hX)
    exact hbr _ rfl
  | ret =>
    obtain ⟨-, rfl, -⟩ := Sim.vals_append_cons_inj hv rfl (by simpa using hX)
    exact hret rfl
  | returnCall hc =>
    obtain ⟨-, rfl, -⟩ := Sim.vals_append_cons_inj hv (Admin.val?_of_isReturnCallRef hc)
      (by simpa using hX)
    exact hrc hc
  | trap =>
    have : vals ws ++ y :: rest = vals [] ++ Admin.trap :: [] := by simpa [vals] using hX
    obtain ⟨-, rfl, -⟩ := Sim.vals_append_cons_inj hv rfl this
    exact htr rfl
  | throwEmpty a => exact hthr a hX
  | catch_ => exact hthr _ hX
  | catchRef => exact hthr _ hX
  | catchAll a => exact hthr a hX
  | catchAllRef a => exact hthr a hX
  | next _ => exact hthr _ hX

/-- **A step through a context of a blocked code** is a step of the code, in place. -/
theorem step_fill : ∀ (E : Ctx) {s : Store H} {f : Frame} {X : List Admin} {c₁ : Config H},
    Blocked X → Step P host ⟨s, f, E.fill X⟩ c₁ →
      ∃ X', Step P host ⟨s, f, X⟩ ⟨c₁.store, c₁.frame, X'⟩ ∧ c₁.code = E.fill X'
  | .hole, _, _, _, ⟨_, _, _⟩, _, h => ⟨_, h, rfl⟩
  | .label ws n cont E rest, s, f, X, c₁, hb, h => by
    obtain ⟨d, hd, rfl⟩ := Step.ctx_in_seq (X := .label n cont (E.fill X)) trivial h
    rcases Step.label_inv hd with ⟨s', f', is', hin, rfl⟩ | ⟨out, hx, -⟩
    · obtain ⟨X', h1, h2⟩ := step_fill E hb hin
      exact ⟨X', h1, by simp [Ctx.fill, ← h2]⟩
    · exact (labelExit_blocked hx (blocked_fill E hb)).elim
  | .handler ws n cs E rest, s, f, X, c₁, hb, h => by
    obtain ⟨d, hd, rfl⟩ := Step.ctx_in_seq (X := .handler n cs (E.fill X)) trivial h
    rcases Step.handler_inv hd with ⟨s', f', is', hin, rfl⟩ | ⟨out, hx, -⟩
    · obtain ⟨X', h1, h2⟩ := step_fill E hb hin
      exact ⟨X', h1, by simp [Ctx.fill, ← h2]⟩
    · exact (handlerExit_blocked hx (blocked_fill E hb)).elim

/-- **Region-run inclusion lifts through a context.** -/
theorem run_fill_back : ∀ (E : Ctx) {s s₁ : Store H} {f f₁ : Frame} {X X' : List Admin},
    (∀ {o : Out} {s₂ : Store H} {f₂ : Frame},
      RunC P host C s₁ f₁ [] X' s₂ f₂ o → RunC P host C s f [] X s₂ f₂ o) →
    ∀ {o : Out} {s₂ : Store H} {f₂ : Frame},
      RunC P host C s₁ f₁ [] (E.fill X') s₂ f₂ o → RunC P host C s f [] (E.fill X) s₂ f₂ o
  | .hole, _, _, _, _, _, _, hb, _, _, _, h => hb h
  | .label ws n cont E rest, _, _, _, _, _, _, hb, _, _, _, h => by
    simp only [Ctx.fill] at h ⊢
    exact run_vals (vs := []) (by
      simpa using label_back (run_fill_back E hb) (by simpa using run_vals_inv (vs := []) h))
  | .handler ws n cs E rest, _, _, _, _, _, _, hb, _, _, _, h => by
    simp only [Ctx.fill] at h ⊢
    exact run_vals (vs := []) (by
      simpa using handler_back (run_fill_back E hb) (by simpa using run_vals_inv (vs := []) h))

theorem callAt_fill {code : List Admin} (h : CallAt code) (hF : FragC code) :
    ∃ (E : Ctx) (rest : List Admin), CtxF E ∧ FragC rest ∧
      ((∃ (ws : List Val) (x : FuncIdx), code = E.fill (vals ws ++ .plain (.call x) :: rest)) ∨
        ∃ (ws : List Val) (a : Nat) (y : TypeIdx),
          code = E.fill (vals ws ++ .ref (.func a) :: .plain (.callRef y) :: rest)) := by
  induction h with
  | @here ws x rest =>
    exact ⟨.hole, rest, .hole, fun a ha => hF a (by simp [ha]), .inl ⟨ws, x, rfl⟩⟩
  | @hereRef ws a y rest =>
    exact ⟨.hole, rest, .hole, fun b hb => hF b (by simp [hb]), .inr ⟨ws, a, y, rfl⟩⟩
  | @label ws n cont X rest _ ih =>
    have hl := hF (.label n cont X) (by simp)
    obtain ⟨hc, hi⟩ : (∀ i ∈ cont, FragIB true i) ∧ FragC X := by
      cases hl with
      | val h => simp [Admin.val?] at h
      | label hc hi => exact ⟨hc, hi⟩
    obtain ⟨E, rest', hE, hr, h'⟩ := ih hi
    refine ⟨.label ws n cont E rest, rest', .label hc (fun a ha => hF a (by simp [ha])) hE, hr, ?_⟩
    rcases h' with ⟨ws', x, rfl⟩ | ⟨ws', a, y, rfl⟩
    · exact .inl ⟨ws', x, rfl⟩
    · exact .inr ⟨ws', a, y, rfl⟩
  | @handler ws n cs X rest _ ih =>
    have hl := hF (.handler n cs X) (by simp)
    have hi : FragC X := by
      cases hl with
      | val h => simp [Admin.val?] at h
      | handler hi => exact hi
    obtain ⟨E, rest', hE, hr, h'⟩ := ih hi
    refine ⟨.handler ws n cs E rest, rest', .handler (fun a ha => hF a (by simp [ha])) hE, hr, ?_⟩
    rcases h' with ⟨ws', x, rfl⟩ | ⟨ws', a, y, rfl⟩
    · exact .inl ⟨ws', x, rfl⟩
    · exact .inr ⟨ws', a, y, rfl⟩

theorem ends_not_blocked {o : Out} {X : List Admin} (ho : o.Ends X) (hb : Blocked X) : False := by
  obtain ⟨ws, y, rest, rfl, hy⟩ := hb
  obtain ⟨hbr, hret, htr, hth, hrc⟩ := bad_not hy
  rcases ends_head ho (bad_val hy) with ⟨l, h⟩ | h | h | h | h
  · exact hbr l h
  · exact hret h
  · exact htr h
  · exact hth h
  · exact hrc h

theorem run_of_endsC {s : Store H} {f : Frame} {c : List Admin} {o : Out} (he : o.Ends c) :
    RunC P host C s f [] c s f o := by
  cases o with
  | normal vs => rw [show c = vals vs from he]; exact run_vals_normal vs
  | br l vs =>
    obtain ⟨x, rest, rfl, rfl⟩ := he
    exact run_br_at vs x rest
  | ret vs =>
    obtain ⟨rest, rfl⟩ := he
    exact run_ret_at vs rest
  | trap => rw [show c = [.trap] from he]; exact .trap
  | throw a =>
    rw [show c = throwing a from he]
    simpa using run_throwing_at (P := P) (host := host) (C := C) (s := s) (f := f) [] a []
  | tail vs a r =>
    obtain ⟨hr, rest, rfl⟩ := he
    exact run_vals (by simpa [vals, Val.toAdmin] using
      (RunC.val (C := C) (P := P) (host := host) (s := s) (f := f) (vs := vs)
        (v := .ref (.func a)) rfl (RunC.returnCallRef (code := rest) hr)))
  | tailNull vs r =>
    obtain ⟨hr, rest, rfl⟩ := he
    exact run_vals (by simpa [vals, Val.toAdmin] using
      (RunC.val (C := C) (P := P) (host := host) (s := s) (f := f) (vs := vs)
        (v := .ref .null) rfl (RunC.returnCallRefNull (code := rest) hr)))

theorem fragC_cont {E : Ctx} {ws : List Val} {out rest : List Admin} (hE : CtxF E)
    (hr : FragC rest) (ho : FragC out) : FragC (E.fill (vals ws ++ out ++ rest)) :=
  fragC_fill hE (frag_append.2 ⟨frag_append.2 ⟨frag_vals ws, ho⟩, hr⟩)

theorem blocked_pending {ws : List Val} {a : Nat} {cr : Admin} {rest : List Admin}
    (hcr : cr.IsCallRef) : Blocked (vals ws ++ .ref (.func a) :: cr :: rest) :=
  ⟨ws ++ [.ref (.func a)], cr, rest, by simp [vals, Val.toAdmin], .inr (.inl hcr)⟩

/-- **The main induction**: along a Core run to a final form of `o`, (A) fragment code runs in
`RunC` to the run's end; (B) a pending `call_ref` in a context runs its callee to a result and the
continuation runs in `RunC`; (C) a callee frame in a context likewise. -/
theorem complete_core {G : Store H → Nat → List Val → Prop} (hC : CallCompleteG P host G C)
    {c' : Config H} {o : Out} (ho : o.Ends c'.code) :
    ∀ {c₀ : Config H}, Steps P host c₀ c' → GuardedCalls P host G c₀ →
      (FragC c₀.code →
        RunC P host C c₀.store c₀.frame [] c₀.code c'.store c'.frame o) ∧
      (∀ (E : Ctx) (ws : List Val) (a : Nat) (cr : Admin) (rest : List Admin) (fi : FuncInst H),
        CtxF E → FragC rest → c₀.code = E.fill (vals ws ++ .ref (.func a) :: cr :: rest) →
        cr.IsCallRef → c₀.store.funcs[a]? = some fi →
        ∃ (ws' us : List Val) (ps rs : Ty (.list .val)) (s₁ : Store H) (r : Result),
          ws = ws' ++ us ∧ Expand fi.type (.func ps rs) ∧ us.length = ps.length ∧
          Steps P host ⟨c₀.store, c₀.frame, vals us ++ [.ref (.func a), cr]⟩
            ⟨s₁, c₀.frame, r.toAdmin⟩ ∧
          RunC P host C s₁ c₀.frame [] (E.fill (vals ws' ++ r.toAdmin ++ rest))
            c'.store c'.frame o) ∧
      (∀ (E : Ctx) (ws : List Val) (n : Nat) (F : Frame) (Y rest : List Admin),
        CtxF E → FragC rest → c₀.code = E.fill (vals ws ++ .frame n F Y :: rest) →
        ∃ (s₁ : Store H) (r : Result),
          Steps P host ⟨c₀.store, c₀.frame, [.frame n F Y]⟩ ⟨s₁, c₀.frame, r.toAdmin⟩ ∧
          RunC P host C s₁ c₀.frame [] (E.fill (vals ws ++ r.toAdmin ++ rest))
            c'.store c'.frame o) := by
  intro c₀ h
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro _
    refine ⟨fun _ => run_of_endsC ho, ?_, ?_⟩
    · intro E ws a cr rest fi _ _ hc hcr _
      rw [hc] at ho
      exact (ends_not_blocked ho (blocked_fill E (blocked_pending hcr))).elim
    · intro E ws n F Y rest _ _ hc
      rw [hc] at ho
      exact (ends_not_blocked ho (blocked_fill E
        ⟨ws, _, rest, rfl, .inr (.inr (.inl ⟨_, _, _, rfl⟩))⟩)).elim
  | @head c₀ c₁ hstep hrest ih =>
    intro hG
    have ih := ih (fun c₂ E ws us a cr rest fi ps rs h₂ =>
      hG c₂ E ws us a cr rest fi ps rs (.head hstep h₂))
    obtain ⟨s, f, code⟩ := c₀
    obtain ⟨s₁', f₁', code₁⟩ := c₁
    have hB : ∀ (E : Ctx) (ws : List Val) (a : Nat) (cr : Admin) (rest : List Admin)
        (fi : FuncInst H), CtxF E → FragC rest →
        code = E.fill (vals ws ++ .ref (.func a) :: cr :: rest) → cr.IsCallRef →
        s.funcs[a]? = some fi →
        ∃ (ws' us : List Val) (ps rs : Ty (.list .val)) (s₁ : Store H) (r : Result),
          ws = ws' ++ us ∧ Expand fi.type (.func ps rs) ∧ us.length = ps.length ∧
          Steps P host ⟨s, f, vals us ++ [.ref (.func a), cr]⟩ ⟨s₁, f, r.toAdmin⟩ ∧
          RunC P host C s₁ f [] (E.fill (vals ws' ++ r.toAdmin ++ rest))
            c'.store c'.frame o := by
      intro E ws a cr rest fi hE hr hc hcr hfi
      subst hc
      obtain ⟨X', hX', hc₁⟩ := step_fill E (blocked_pending hcr) hstep
      simp only at hc₁ hX'
      cases hcode : fi.code with
      | wasm code =>
        obtain ⟨vs₁, vs₂, ps, rs, rfl, he, hn, hcf⟩ := Step.callRef_wasm_inv_seq hcr hfi hcode hX'
        simp only [Config.mk.injEq] at hcf
        obtain ⟨rfl, rfl, rfl⟩ := hcf
        obtain ⟨s₂, r, hfr, hrun⟩ := ih.2.2 E vs₁ _ _ _ rest hE hr hc₁
        exact ⟨vs₁, vs₂, ps, rs, s₂, r, rfl, he, hn,
          .head (Step.callRefFunc hcr hfi he hn hcode) hfr, hrun⟩
      | host hh =>
        obtain ⟨vs₁, vs₂, ps, rs, rfl, he, hn, hres⟩ := Step.callRef_host_inv_seq hcr hfi hcode hX'
        rcases hres with ⟨s'', res, hhost, hcf⟩ | ⟨hhost, hcf⟩
        · simp only [Config.mk.injEq] at hcf
          obtain ⟨rfl, rfl, rfl⟩ := hcf
          have hF₁ : FragC code₁ := by rw [hc₁]; exact fragC_cont hE hr (fragC_result res)
          exact ⟨vs₁, vs₂, ps, rs, s₁', res, rfl, he, hn,
            .single (Step.callRefHost hcr hfi he hn hcode hhost), by
              simpa [hc₁] using ih.1 hF₁⟩
        · simp only [Config.mk.injEq] at hcf
          obtain ⟨rfl, rfl, rfl⟩ := hcf
          exact ih.2.1 E (vs₁ ++ vs₂) a cr rest fi hE hr (by rw [hc₁]; simp) hcr hfi
    refine ⟨fun hF => ?_, hB, ?_⟩
    · -- (A)
      by_cases hca : CallAt code
      · obtain ⟨E, rest, hE, hr, ⟨ws, x, rfl⟩ | ⟨ws, a, y, rfl⟩⟩ := callAt_fill hca hF
        · obtain ⟨X', hX', hc₁⟩ := step_fill E ⟨ws, _, rest, rfl, .inl ⟨x, rfl⟩⟩ hstep
          obtain ⟨a, fi, hx, hfi, hcf⟩ := Step.call_vals_inv_seq hX'
          simp only [Config.mk.injEq] at hcf hc₁
          obtain ⟨rfl, rfl, rfl⟩ := hcf
          obtain ⟨ws', us, ps, rs, s₂, r, rfl, he, hn, hcall, hrun⟩ :=
            ih.2.1 E ws a _ rest fi hE hr hc₁ trivial hfi
          exact run_fill_back E (fun hh => call_incl hC hx hfi he hn
            (guarded_call hG .refl rfl hx hfi he hn) hcall hh) hrun
        · obtain ⟨X', hX', -⟩ := step_fill E
            (blocked_pending (ws := ws) (a := a) (rest := rest) (cr := .plain (.callRef y)) trivial)
            hstep
          have hX'' : Step P host ⟨s, f, vals (ws ++ [.ref (.func a)]) ++ .plain (.callRef y) :: rest⟩
              ⟨s₁', f₁', X'⟩ := by simpa [vals, Val.toAdmin] using hX'
          rcases Step.callRef_top_inv_seq (r := .plain (.callRef y)) trivial hX'' with
            ⟨w, hw, -⟩ | ⟨w, a', fi, hw, hfi⟩
          · have := congrArg List.getLast? hw; simp at this
          · obtain ⟨rfl, hl⟩ := List.append_inj' hw rfl
            simp only [List.cons.injEq, Val.ref.injEq, Ref.func.injEq, and_true] at hl
            subst hl
            obtain ⟨ws', us, ps, rs, s₂, r, rfl, he, hn, hcall, hrun⟩ :=
              hB E _ a _ rest fi hE hr rfl trivial hfi
            exact run_fill_back E (fun hh => callRef_incl hC hfi he hn
              (hG _ E ws' us a _ rest fi ps rs .refl rfl trivial
                (fun d hd => by cases hd) hfi he hn) hcall hh) (by simpa using hrun)
      · obtain ⟨hF₁, hb⟩ := expandB (C := C) hstep hF hca
        exact hb (ih.1 hF₁)
    · -- (C)
      intro E ws n F Y rest hE hr hc
      simp only at hc ⊢
      subst hc
      obtain ⟨X', hX', hc₁⟩ := step_fill E ⟨ws, _, rest, rfl, .inr (.inr (.inl ⟨_, _, _, rfl⟩))⟩
        hstep
      simp only at hc₁ hX'
      obtain ⟨d, hd, hdeq⟩ := Step.ctx_in_seq (X := .frame n F Y) trivial hX'
      simp only [Config.mk.injEq] at hdeq
      obtain ⟨rfl, rfl, rfl⟩ := hdeq
      rcases Step.frame_inv hd with ⟨s', F', Y', hin, rfl⟩ | ⟨out, hx, rfl⟩
      · obtain ⟨s₂, r, hfr, hrun⟩ := ih.2.2 E ws n F' Y' rest hE hr (by rw [hc₁]; simp)
        exact ⟨s₂, r, .head hd hfr, hrun⟩
      · have hres : ∀ r : Result, out = r.toAdmin →
            ∃ (s₂ : Store H) (r : Result),
              Steps P host ⟨s, f, [.frame n F Y]⟩ ⟨s₂, f, r.toAdmin⟩ ∧
              RunC P host C s₂ f [] (E.fill (vals ws ++ r.toAdmin ++ rest)) c'.store c'.frame o := by
          intro r hr'
          subst hr'
          have hF₁ : FragC code₁ := by rw [hc₁]; exact fragC_cont hE hr (fragC_result r)
          exact ⟨s, r, .single hd, by simpa [hc₁] using ih.1 hF₁⟩
        cases hx with
        | vals hn' => exact hres (.values _) rfl
        | ret hn' => exact hres (.values _) rfl
        | trap => exact hres .trap rfl
        | throw t => exact hres (.throw t) rfl
        | returnCallNull hc' => exact hres .trap rfl
        | @returnCallAddr vs' vs a' c'' rest' fn ps rs hc' hf' he' hn' =>
          obtain ⟨ws'', us, ps'', rs'', s₂, r, hsplit, he'', hn'', hcall, hrun⟩ :=
            ih.2.1 E (ws ++ vs) a' _ rest fn hE hr (by rw [hc₁]; simp)
              (isCallRef_retToCallIn hc' F.module) hf'
          obtain ⟨rfl, -⟩ := expand_func_inj he' he''
          obtain ⟨rfl, rfl⟩ := List.append_inj' hsplit (by omega)
          exact ⟨s₂, r, .head hd hcall, hrun⟩

/-- **Core completeness for code with calls**: under a complete oracle (`CallCompleteG`,
its guard holding everywhere), every Core 3.0 run of fragment code with calls (`FragC`) to a final
form of `o` is a `RunC` run. -/
theorem completeC {G : Store H → Nat → List Val → Prop} (hC : CallCompleteG P host G C)
    {s s' : Store H} {f f' : Frame} {code c' : List Admin} {o : Out}
    (hG : GuardedCalls P host G ⟨s, f, code⟩)
    (hF : FragC code) (h : Steps P host ⟨s, f, code⟩ ⟨s', f', c'⟩) (he : o.Ends c') :
    RunC P host C s f [] code s' f' o :=
  (complete_core hC (c' := ⟨s', f', c'⟩) he h hG).1 hF

end Silmaril.Wasm.Cfg.Proofs.Region

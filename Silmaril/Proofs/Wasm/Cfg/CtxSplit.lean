module

public import Silmaril.Proofs.Wasm.Cfg.CallTransport

@[expose] public section

/-!
# Runs through a context in a sequence: the first exit

A Core run of `vals ws ++ X :: rest`, for a `FRAME`, `HANDLER` or `LABEL` `X`, that ends where that
context is gone (no such context at the top of the final code) first runs `X`'s body alone (in its
own frame for a `FRAME`), then leaves `X` by one of Core's exit rules (`FrameExit`,
`HandlerExit`, `LabelExit`), and the rest continues from `vals ws ++ out ++ rest`. Every profile
and host. For a frame whose exit is not a tail call, this is a run of `[X]` to a result
(`frame_seq_result`).
-/

namespace Silmaril.Wasm.Cfg.Proofs.Region

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Region Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- **The first exit of a frame in a sequence.** -/
theorem frame_seq_exit {ws : List Val} {n : Nat} {rest : List Admin} {c' : Config H} :
    ∀ {c₀ : Config H}, Steps P host c₀ c' → ∀ (s : Store H) (f F : Frame) (X : List Admin),
      c₀ = ⟨s, f, vals ws ++ .frame n F X :: rest⟩ →
      (∀ F' X', Admin.frame n F' X' ∉ c'.code) →
      ∃ (s₁ : Store H) (F₁ : Frame) (X₁ out : List Admin),
        Steps P host ⟨s, F, X⟩ ⟨s₁, F₁, X₁⟩ ∧ FrameExit s₁ F₁ n X₁ out ∧
        Steps P host ⟨s₁, f, vals ws ++ out ++ rest⟩ c' := by
  intro c₀ h
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro s f F X hc hfin
    subst hc
    exact absurd (by simp) (hfin F X)
  | @head c₀ c₁ hstep _ ih =>
    intro s f F X hc hfin
    subst hc
    obtain ⟨d, hd, rfl⟩ := Step.ctx_in_seq (X := .frame n F X) trivial hstep
    rcases Step.frame_inv hd with ⟨s', F', X', hin, rfl⟩ | ⟨out, hx, rfl⟩
    · obtain ⟨s₁, F₁, X₁, out, h1, h2, h3⟩ := ih s' f F' X' (by simp) hfin
      exact ⟨s₁, F₁, X₁, out, .head hin h1, h2, h3⟩
    · exact ⟨s, F, X, out, .refl, hx, by assumption⟩

/-- **The first exit of a handler in a sequence.** -/
theorem handler_seq_exit {ws : List Val} {n : Nat} {cs : List Catch} {rest : List Admin}
    {c' : Config H} :
    ∀ {c₀ : Config H}, Steps P host c₀ c' → ∀ (s : Store H) (f : Frame) (X : List Admin),
      c₀ = ⟨s, f, vals ws ++ .handler n cs X :: rest⟩ →
      (∀ X', Admin.handler n cs X' ∉ c'.code) →
      ∃ (s₁ : Store H) (f₁ : Frame) (X₁ out : List Admin),
        Steps P host ⟨s, f, X⟩ ⟨s₁, f₁, X₁⟩ ∧ HandlerExit s₁ f₁ n cs X₁ out ∧
        Steps P host ⟨s₁, f₁, vals ws ++ out ++ rest⟩ c' := by
  intro c₀ h
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro s f X hc hfin
    subst hc
    exact absurd (by simp) (hfin X)
  | @head c₀ c₁ hstep _ ih =>
    intro s f X hc hfin
    subst hc
    obtain ⟨d, hd, rfl⟩ := Step.ctx_in_seq (X := .handler n cs X) trivial hstep
    rcases Step.handler_inv hd with ⟨s', f', X', hin, rfl⟩ | ⟨out, hx, rfl⟩
    · obtain ⟨s₁, f₁, X₁, out, h1, h2, h3⟩ := ih s' f' X' (by simp) hfin
      exact ⟨s₁, f₁, X₁, out, .head hin h1, h2, h3⟩
    · exact ⟨s, f, X, out, .refl, hx, by assumption⟩

/-- **The first exit of a label in a sequence.** -/
theorem label_seq_exit {ws : List Val} {n : Nat} {cont : List Instr} {rest : List Admin}
    {c' : Config H} :
    ∀ {c₀ : Config H}, Steps P host c₀ c' → ∀ (s : Store H) (f : Frame) (X : List Admin),
      c₀ = ⟨s, f, vals ws ++ .label n cont X :: rest⟩ →
      (∀ X', Admin.label n cont X' ∉ c'.code) →
      ∃ (s₁ : Store H) (f₁ : Frame) (X₁ out : List Admin),
        Steps P host ⟨s, f, X⟩ ⟨s₁, f₁, X₁⟩ ∧ LabelExit n cont X₁ out ∧
        Steps P host ⟨s₁, f₁, vals ws ++ out ++ rest⟩ c' := by
  intro c₀ h
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro s f X hc hfin
    subst hc
    exact absurd (by simp) (hfin X)
  | @head c₀ c₁ hstep _ ih =>
    intro s f X hc hfin
    subst hc
    obtain ⟨d, hd, rfl⟩ := Step.ctx_in_seq (X := .label n cont X) trivial hstep
    rcases Step.label_inv hd with ⟨s', f', X', hin, rfl⟩ | ⟨out, hx, rfl⟩
    · obtain ⟨s₁, f₁, X₁, out, h1, h2, h3⟩ := ih s' f' X' (by simp) hfin
      exact ⟨s₁, f₁, X₁, out, .head hin h1, h2, h3⟩
    · exact ⟨s, f, X, out, .refl, hx, by assumption⟩

/-- **A frame in a sequence runs to a result, or leaves by a tail call.** For a run of
`vals ws ++ FRAME_n{F} X :: rest` to a code with no `FRAME_n` at its top: either the frame alone
runs (in the outer frame `f`) to a result `r`, and the sequence continues from
`vals ws ++ r ++ rest`; or the frame is left by a tail call (`return_call_ref-frame-addr`) to a
`call_ref` of `a` on `args`, and the sequence continues from there. -/
theorem frame_seq_result {s : Store H} {f F : Frame} {ws : List Val} {n : Nat}
    {X rest : List Admin} {c' : Config H}
    (h : Steps P host ⟨s, f, vals ws ++ .frame n F X :: rest⟩ c')
    (hfin : ∀ F' X', Admin.frame n F' X' ∉ c'.code) :
    (∃ (s₁ : Store H) (r : Result), Steps P host ⟨s, f, [.frame n F X]⟩ ⟨s₁, f, r.toAdmin⟩ ∧
        Steps P host ⟨s₁, f, vals ws ++ r.toAdmin ++ rest⟩ c') ∨
      ∃ (s₁ : Store H) (args : List Val) (a : Nat) (c : Admin), c.IsCallRef ∧
        Steps P host ⟨s, f, [.frame n F X]⟩ ⟨s₁, f, vals args ++ [.ref (.func a), c]⟩ ∧
        Steps P host ⟨s₁, f, vals ws ++ (vals args ++ [.ref (.func a), c]) ++ rest⟩ c' := by
  obtain ⟨s₁, F₁, X₁, out, h1, hx, h3⟩ := frame_seq_exit h s f F X rfl hfin
  have hin := steps_frame (f := f) n h1
  have hex := frameExit_step (P := P) (host := host) hx f
  cases hx with
  | vals hn' => exact .inl ⟨s₁, .values _, hin.tail hex, h3⟩
  | ret hn' => exact .inl ⟨s₁, .values _, hin.tail hex, h3⟩
  | trap => exact .inl ⟨s₁, .trap, hin.tail hex, h3⟩
  | throw a => exact .inl ⟨s₁, .throw a, hin.tail hex, h3⟩
  | returnCallNull hc => exact .inl ⟨s₁, .trap, hin.tail hex, h3⟩
  | returnCallAddr hc hf he hn' =>
    exact .inr ⟨s₁, _, _, _, isCallRef_retToCallIn hc F₁.module, hin.tail hex, h3⟩

end Silmaril.Wasm.Cfg.Proofs.Region

namespace Silmaril.Wasm.Cfg.Proofs.Region

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Region Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- **A frame in a sequence is still running, or has exited**: every Core run of
`vals ws ++ FRAME_n{F} X :: rest` reaches either the same sequence with the frame's body advanced
(in its own frame), or, after the frame's first exit, a run from `vals ws ++ out ++ rest`. -/
theorem frame_seq_cases {ws : List Val} {n : Nat} {rest : List Admin} {c' : Config H} :
    ∀ {c₀ : Config H}, Steps P host c₀ c' → ∀ (s : Store H) (f F : Frame) (X : List Admin),
      c₀ = ⟨s, f, vals ws ++ .frame n F X :: rest⟩ →
      (∃ F' X', c' = ⟨c'.store, f, vals ws ++ .frame n F' X' :: rest⟩ ∧
          Steps P host ⟨s, F, X⟩ ⟨c'.store, F', X'⟩) ∨
      ∃ (s₁ : Store H) (F₁ : Frame) (X₁ out : List Admin),
        Steps P host ⟨s, F, X⟩ ⟨s₁, F₁, X₁⟩ ∧ FrameExit s₁ F₁ n X₁ out ∧
        Steps P host ⟨s₁, f, vals ws ++ out ++ rest⟩ c' := by
  intro c₀ h
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro s f F X hc
    subst hc
    exact .inl ⟨F, X, rfl, .refl⟩
  | @head c₀ c₁ hstep _ ih =>
    intro s f F X hc
    subst hc
    obtain ⟨d, hd, rfl⟩ := Step.ctx_in_seq (X := .frame n F X) trivial hstep
    rcases Step.frame_inv hd with ⟨s', F', X', hin, rfl⟩ | ⟨out, hx, rfl⟩
    · rcases ih s' f F' X' (by simp) with ⟨F'', X'', he, hs⟩ | ⟨s₁, F₁, X₁, out, h1, h2, h3⟩
      · exact .inl ⟨F'', X'', he, .head hin hs⟩
      · exact .inr ⟨s₁, F₁, X₁, out, .head hin h1, h2, h3⟩
    · exact .inr ⟨s, F, X, out, .refl, hx, by assumption⟩

/-- **A direct call under values, run alone** (Wasm callee): every Core run of
`vals vs ++ [call x]` is still at the call, at the resolved `call_ref`, inside the callee's frame
(on the top `ps.length` values), or past the frame's first exit. In the last case the callee's
`call_ref` itself runs to the exit's code. -/
theorem call_vals_cases {s : Store H} {f : Frame} {vs : List Val} {x : FuncIdx} {c : Config H}
    (hw : WasmFuncs s) (h : Steps P host ⟨s, f, vals vs ++ [.plain (.call x)]⟩ c) :
    c = ⟨s, f, vals vs ++ [.plain (.call x)]⟩ ∨
    ∃ a fi, f.module.funcs[x.toNat]? = some a ∧ s.funcs[a]? = some fi ∧
      (c = ⟨s, f, vals vs ++ [.ref (.func a), .callRefType fi.type]⟩ ∨
        ∃ (ws us : List Val) (ps rs : Ty (.list .val)) (code : Func),
          vs = ws ++ us ∧ fi.code = .wasm code ∧ Expand fi.type (.func ps rs) ∧
          us.length = ps.length ∧
          ((∃ F' X', c = ⟨c.store, f, vals ws ++ [.frame rs.length F' X']⟩ ∧
              Steps P host ⟨s, Frame.forCall fi.module us code.locals,
                [.label rs.length [] (expression code.body)]⟩ ⟨c.store, F', X'⟩) ∨
            ∃ (s₁ : Store H) (F₁ : Frame) (X₁ out : List Admin),
              FrameExit s₁ F₁ rs.length X₁ out ∧
              Steps P host ⟨s, f, vals us ++ [.ref (.func a), .callRefType fi.type]⟩
                ⟨s₁, f, out⟩ ∧
              Steps P host ⟨s₁, f, vals ws ++ out⟩ c)) := by
  rcases h.cases_head with rfl | ⟨c₁, h₁, hr⟩
  · exact .inl rfl
  obtain ⟨a, fi, hx, hfi, rfl⟩ := Step.call_vals_inv h₁
  refine .inr ⟨a, fi, hx, hfi, ?_⟩
  rcases hr.cases_head with rfl | ⟨c₂, h₂, hr₂⟩
  · exact .inl rfl
  obtain ⟨code, hcode⟩ := hw fi (List.mem_of_getElem? hfi)
  obtain ⟨ws, us, ps, rs, rfl, he, hn, rfl⟩ := Step.callRef_wasm_inv (r := .callRefType fi.type) trivial hfi hcode h₂
  refine .inr ⟨ws, us, ps, rs, code, rfl, hcode, he, hn, ?_⟩
  rcases frame_seq_cases (ws := ws) (n := rs.length) (rest := []) hr₂ s f
      (Frame.forCall fi.module us code.locals) [.label rs.length [] (expression code.body)] rfl with
    ⟨F', X', he', hs⟩ | ⟨s₁, F₁, X₁, out, h1, hx', h3⟩
  · exact .inl ⟨F', X', by simpa using he', hs⟩
  · refine .inr ⟨s₁, F₁, X₁, out, hx', ?_, by simpa using h3⟩
    have hent : Step P host ⟨s, f, vals us ++ [.ref (.func a), .callRefType fi.type]⟩
        ⟨s, f, [.frame rs.length (Frame.forCall fi.module us code.locals)
          [.label rs.length [] (expression code.body)]]⟩ :=
      Step.callRefFunc trivial hfi he hn hcode
    exact .head hent ((steps_frame rs.length h1).tail (frameExit_step hx' f))

end Silmaril.Wasm.Cfg.Proofs.Region

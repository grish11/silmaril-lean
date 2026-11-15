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

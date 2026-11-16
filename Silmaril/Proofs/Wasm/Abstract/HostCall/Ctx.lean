module

public import Silmaril.Wasm.Abstract.HostCall.Defs
public import Silmaril.Wasm.Execution.Core.Inversion.Thms
public import Silmaril.Wasm.SingleThreaded.Agreement
public import Silmaril.Wasm.SingleThreaded.NoRedex
public import Silmaril.Wasm.SingleThreaded.Determinism.Stuck
public import Silmaril.Proofs.Wasm.Abstract.HostCall.Split

/-!
# Runs in a label or a call frame (proofs)

A label or a frame is left only once its body is stuck: every exit form
(`LabelExit`, `FrameExit`) has no step of its own (`labelExit_stuck`). So a run of
`vals ws ++ [label n cont b] ++ rest` to a stuck end first runs the body `b` alone
to a stuck `c_b`, and then continues from the label around `c_b`
(`stepsN_label_seq_split`); likewise for the frame and label of a call,
`vals ws ++ [frame n F [label n [] b]] ++ rest` (`stepsN_frame_seq_split`), the
body running in its own frame. Counted, so the body's run is no longer than the
whole run.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostCall

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.SingleThreaded

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

/-- A head that only reduces through an enclosing label, handler or frame does not
step, whatever the host. -/
theorem blocked_stuck {s : Store H} {f : Frame} {vs : List Val} {e : Admin} {rest : List Admin}
    {c : Config H} (he : Det.Blocked e) : ¬ Step P host ⟨s, f, vals vs ++ e :: rest⟩ c := by
  intro h
  have hv : e.val? = none := by
    rcases he with ⟨l, rfl⟩ | rfl | hc
    · rfl
    · rfl
    · exact SingleThreaded.val?_returnCallRef hc
  have hd : decompose? s (vals vs ++ e :: rest) = none := by
    refine decompose?_vals_cons_none hv fun _ _ => ?_
    rcases he with ⟨l, rfl⟩ | rfl | hc
    · exact decompHead_plain rfl
    · exact decompHead_plain rfl
    · exact decompHead_returnCallRef hc
  have hn : Step P Det.noHost ⟨s, f, vals vs ++ e :: rest⟩ c := by
    rcases Step.split_host h with h | ⟨E, a, hh, args, hdc, -⟩
    · exact h
    · rw [hd] at hdc; cases hdc
  exact Det.not_step_blocked (W := vs) (rest := rest) hn (by simp [Det.fnv_cons_of_none hv]) he

/-- **Every label exit form is stuck.** -/
theorem labelExit_stuck {s : Store H} {f : Frame} {n : Nat} {cont : List Instr} {b out : List Admin}
    (h : LabelExit n cont b out) (c : Config H) : ¬ Step P host ⟨s, f, b⟩ c := by
  cases h with
  | vals vs => exact Sim.Step.not_vals
  | @brZero vs' vs l rest _ _ =>
    have e : vals vs' ++ vals vs ++ [.plain (.br l)] ++ rest =
        vals (vs' ++ vs) ++ .plain (.br l) :: rest := by simp
    rw [e]; exact blocked_stuck (.inl ⟨l, rfl⟩)
  | @brSucc vs l rest _ =>
    have e : vals vs ++ [.plain (.br l)] ++ rest = vals vs ++ .plain (.br l) :: rest := by simp
    rw [e]; exact blocked_stuck (.inl ⟨l, rfl⟩)
  | @ret vs rest =>
    have e : vals vs ++ [.plain .return_] ++ rest = vals vs ++ .plain .return_ :: rest := by simp
    rw [e]; exact blocked_stuck (.inr (.inl rfl))
  | @returnCall vs c' rest hc =>
    have e : vals vs ++ [c'] ++ rest = vals vs ++ c' :: rest := by simp
    rw [e]; exact blocked_stuck (.inr (.inr hc))
  | throw a => exact throw_stuck
  | trap => exact trap_stuck

theorem not_mem_vals {a : Admin} (ha : a.val? = none) {ws : List Val} : a ∉ vals ws := by
  intro hm
  obtain ⟨v, -, rfl⟩ := List.mem_map.1 hm
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin, Admin.val?] at ha

/-- A frame around a single label does not exit. -/
theorem frameExit_label {s : Store H} {fi : Frame} {n k : Nat} {cont : List Instr}
    {b code out : List Admin} (h : FrameExit s fi n code out) (hc : code = [.label k cont b]) :
    False := by
  have hlab : Admin.label k cont b ∈ code := by rw [hc]; simp
  have hlen : code.length = 1 := by rw [hc]; simp
  cases h with
  | vals hn => exact not_mem_vals rfl hlab
  | ret hn =>
    have hm : Admin.plain .return_ ∈ [Admin.label k cont b] := by rw [← hc]; simp
    simp at hm
  | trap => simp at hlab
  | throw a => simp [throwing] at hlab
  | returnCallNull hc =>
    simp at hlen; omega
  | returnCallAddr hc hf he hn =>
    simp at hlen; omega

/-! ## Splitting a run in a label or a call frame -/

/-- The conclusion of `stepsN_label_seq_split`. -/
def LabelSeqSplit (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H) (N : Nat)
    (s : Store H) (f : Frame) (ws : List Val) (n : Nat) (cont : List Instr) (b rest : List Admin)
    (c : Config H) : Prop :=
  ∃ (cb : Config H) (N₁ : Nat), N₁ ≤ N ∧ StepsN P host N₁ ⟨s, f, b⟩ cb ∧
    (∀ c', ¬ Step P host cb c') ∧
    StepsN P host (N - N₁) ⟨cb.store, cb.frame, vals ws ++ [.label n cont cb.code] ++ rest⟩ c

/-- **A run in a label**: the body runs alone to a stuck end, then the label around it
goes on. -/
theorem stepsN_label_seq_split {N : Nat} {s : Store H} {f : Frame} {ws : List Val} {n : Nat}
    {cont : List Instr} {b rest : List Admin} {c : Config H}
    (hrun : StepsN P host N ⟨s, f, vals ws ++ [.label n cont b] ++ rest⟩ c)
    (hend : ∀ c', ¬ Step P host c c') :
    LabelSeqSplit P host N s f ws n cont b rest c := by
  suffices key : ∀ N y, StepsN P host N y c → ∀ s f b,
      y = ⟨s, f, vals ws ++ [.label n cont b] ++ rest⟩ → LabelSeqSplit P host N s f ws n cont b rest c
    from key _ _ hrun s f b rfl
  clear hrun
  intro N y hy
  induction hy with
  | refl =>
    intro s f b hy
    subst hy
    by_cases hb : ∃ c', Step P host ⟨s, f, b⟩ c'
    · obtain ⟨⟨s', f', b'⟩, h⟩ := hb
      exact (hend _ (Silmaril.Wasm.Logic.Core.Step.ctx ws rest (Step.ctxtLabel h))).elim
    · exact ⟨⟨s, f, b⟩, 0, le_refl _, .refl _, fun c' h => hb ⟨c', h⟩, .refl _⟩
  | @head N y z _ hstep hrest ih =>
    intro s f b hy
    subst hy
    by_cases hb : ∃ c', Step P host ⟨s, f, b⟩ c'
    · obtain ⟨c₀, h₀, rfl⟩ := Step.ctx_in_seq (X := .label n cont b) trivial
        (by simpa using hstep)
      rcases Step.label_inv h₀ with ⟨s', f', b', hin, rfl⟩ | ⟨out, hex, -⟩
      · obtain ⟨cb, N₁, hN₁, h₁, hs₁, hk⟩ := ih hend s' f' b' (by simp)
        refine ⟨cb, N₁ + 1, by omega, .head hin h₁, hs₁, ?_⟩
        rwa [show N + 1 - (N₁ + 1) = N - N₁ by omega]
      · obtain ⟨c', hc'⟩ := hb
        exact (labelExit_stuck (P := P) (host := host) (s := s) (f := f) hex c' hc').elim
    · exact ⟨⟨s, f, b⟩, 0, by omega, .refl _, fun c' h => hb ⟨c', h⟩, .head hstep hrest⟩

/-- The conclusion of `stepsN_frame_seq_split`. -/
def FrameSeqSplit (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H) (N : Nat)
    (s : Store H) (f F : Frame) (ws : List Val) (n : Nat) (b rest : List Admin) (c : Config H) :
    Prop :=
  ∃ (cb : Config H) (N₁ : Nat), N₁ ≤ N ∧ StepsN P host N₁ ⟨s, F, b⟩ cb ∧
    (∀ c', ¬ Step P host cb c') ∧
    StepsN P host (N - N₁)
      ⟨cb.store, f, vals ws ++ [.frame n cb.frame [.label n [] cb.code]] ++ rest⟩ c

/-- **A run in a call frame**: the callee body runs alone, in its frame, to a stuck
end; then the frame and label around it go on. -/
theorem stepsN_frame_seq_split {N : Nat} {s : Store H} {f F : Frame} {ws : List Val} {n : Nat}
    {b rest : List Admin} {c : Config H}
    (hrun : StepsN P host N ⟨s, f, vals ws ++ [.frame n F [.label n [] b]] ++ rest⟩ c)
    (hend : ∀ c', ¬ Step P host c c') :
    FrameSeqSplit P host N s f F ws n b rest c := by
  suffices key : ∀ N y, StepsN P host N y c → ∀ s F b,
      y = ⟨s, f, vals ws ++ [.frame n F [.label n [] b]] ++ rest⟩ →
      FrameSeqSplit P host N s f F ws n b rest c
    from key _ _ hrun s F b rfl
  clear hrun
  intro N y hy
  induction hy with
  | refl =>
    intro s F b hy
    subst hy
    by_cases hb : ∃ c', Step P host ⟨s, F, b⟩ c'
    · obtain ⟨⟨s', F', b'⟩, h⟩ := hb
      exact (hend _ (Silmaril.Wasm.Logic.Core.Step.ctx ws rest
        (Step.ctxtFrame (f := f) (Step.ctxtLabel h)))).elim
    · exact ⟨⟨s, F, b⟩, 0, le_refl _, .refl _, fun c' h => hb ⟨c', h⟩, .refl _⟩
  | @head N y z _ hstep hrest ih =>
    intro s F b hy
    subst hy
    by_cases hb : ∃ c', Step P host ⟨s, F, b⟩ c'
    · obtain ⟨c₀, h₀, rfl⟩ := Step.ctx_in_seq (X := .frame n F [.label n [] b]) trivial
        (by simpa using hstep)
      rcases Step.frame_inv h₀ with ⟨s', F', is', hin, rfl⟩ | ⟨out, hex, -⟩
      · rcases Step.label_inv hin with ⟨s'', F'', b', hin', he⟩ | ⟨out, hex, -⟩
        · simp only [Config.mk.injEq] at he
          obtain ⟨rfl, rfl, rfl⟩ := he
          obtain ⟨cb, N₁, hN₁, h₁, hs₁, hk⟩ := ih hend s' F' b' (by simp)
          refine ⟨cb, N₁ + 1, by omega, .head hin' h₁, hs₁, ?_⟩
          rwa [show N + 1 - (N₁ + 1) = N - N₁ by omega]
        · obtain ⟨c', hc'⟩ := hb
          exact (labelExit_stuck (P := P) (host := host) (s := s) (f := F) hex c' hc').elim
      · exact (frameExit_label hex rfl).elim
    · exact ⟨⟨s, F, b⟩, 0, by omega, .refl _, fun c' h => hb ⟨c', h⟩, .head hstep hrest⟩

end Silmaril.Proofs.Wasm.Abstract.HostCall

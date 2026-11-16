module

public import Silmaril.Wasm.Abstract.BodyDet.Thms
public import Silmaril.Wasm.Abstract.PubModule.Thms
public import Silmaril.Wasm.Abstract.PubModuleXP.Thms
public import Silmaril.Wasm.Abstract.HostCall.Thms
public import Silmaril.Wasm.Execution.Core.Soundness
public import Silmaril.Wasm.Execution.Core.Inversion.Thms
public import Silmaril.Wasm.Execution.Core.Sim.TypedContext
public import Silmaril.Wasm.SingleThreaded.NoRedex
public import Silmaril.Wasm.SingleThreaded.Determinism.Vals

/-!
# Determinism of the Core host triple at the deterministic profile (proofs)

* `agree_of`: two behaviours agree when they make the same call after every common prefix,
  neither log is a strict prefix of the other, and equal logs have equal ends. `agree_map`:
  agreement survives a map on the ends.
* Runs at `profile o` (`Stop`: no host-free step). `evRun_through`: a labelled run from `K` with
  log `cs` to `x` is passed through by every labelled run from `K` with log `cs ++ d` to a
  stopped configuration, which continues from `x` with `d`. Host-free steps go through
  `evRunN_through`; at a host event both runs are at the same callout, where the only silent
  step is a stutter and the answer fixes the next configuration. Hence one stopped configuration
  per log (`evRun_stop_unique`), and a configuration that diverges host-free never reaches a
  stopped one with the same log, when it is typed (`not_div_stop`, by `diverges_through_steps`).
* Finished Core behaviours (`FinB`: a run to an end configuration `EndCfg`, or a run followed by
  host-free divergence) agree (`finB_agree`) and never share their log with a reached callout
  (`finB_callout`).
* `tripleDet_sat`: a triple whose finished behaviours are `FinB` from a typed start and whose
  call prefixes are reached callouts has a deterministic saturation; `pubTriple_det` transfers
  this to the public restriction.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.CoreDet

open Silmaril.Wasm Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
  Silmaril.Wasm.Abstract.BodyDet

/-! ## Agreement -/

section Agree

universe u

variable {E : Sig.{u}} {S B : Type u}

theorem agree_of {c₁ c₂ : List (Call E)} {e₁ e₂ : End S B}
    (hc : ∀ p x₁ r₁ x₂ r₂, c₁ = p ++ x₁ :: r₁ → c₂ = p ++ x₂ :: r₂ → x₁.1 = x₂.1)
    (h₁ : ∀ x r, c₂ = c₁ ++ x :: r → False) (h₂ : ∀ x r, c₁ = c₂ ++ x :: r → False)
    (he : c₁ = c₂ → e₁ = e₂) : AFun.Agree c₁ e₁ c₂ e₂ := by
  induction c₁ generalizing c₂ with
  | nil =>
    cases c₂ with
    | nil => exact he rfl
    | cons x r => exact (h₁ x r rfl).elim
  | cons x₁ r₁ ih =>
    cases c₂ with
    | nil => exact (h₂ x₁ r₁ rfl).elim
    | cons x₂ r₂ =>
      obtain ⟨m₁, n₁⟩ := x₁
      obtain ⟨m₂, n₂⟩ := x₂
      have hm : m₁ = m₂ := hc [] _ r₁ _ r₂ rfl rfl
      subst hm
      refine ⟨rfl, fun hn => ?_⟩
      cases hn
      exact ih (fun p y₁ s₁ y₂ s₂ h h' => hc (⟨m₁, n₁⟩ :: p) y₁ s₁ y₂ s₂ (by rw [h]; rfl)
          (by rw [h']; rfl))
        (fun x r h => h₁ x r (by rw [h]; rfl)) (fun x r h => h₂ x r (by rw [h]; rfl))
        (fun h => he (by rw [h]))

theorem agree_map {S' B' : Type u} (f : End S B → End S' B') {c₁ c₂ : List (Call E)}
    {e₁ e₂ : End S B} (h : AFun.Agree c₁ e₁ c₂ e₂) : AFun.Agree c₁ (f e₁) c₂ (f e₂) := by
  induction c₁ generalizing c₂ with
  | nil =>
    cases c₂ with
    | nil => exact congrArg f h
    | cons => exact h.elim
  | cons x r ih =>
    obtain ⟨m, n⟩ := x
    cases c₂ with
    | nil => exact h.elim
    | cons y r' =>
      obtain ⟨m', n'⟩ := y
      exact ⟨h.1, fun hn => ih (h.2 hn)⟩

end Agree

variable {H : Type} {host : HostSemantics H}

/-! ## Callouts and end configurations -/

/-- No host-free step. -/
def Stop (P : Numerics.Profile) (c : Config H) : Prop :=
  ∀ c', ¬ Step P SingleThreaded.Det.noHost c c'

/-- The configuration at which a finished end is reached. -/
def EndCfg : End (Store H) (List Val ⊕ Nat) → Config H → Prop
  | .ret (.inl ws) s₂, y => y = ⟨s₂, {}, vals ws⟩
  | .ret (.inr t) s₂, y => y = ⟨s₂, {}, throwing t⟩
  | .trap, y => ∃ s₂, y = ⟨s₂, {}, [.trap]⟩
  | .div, _ => False

section Cfg

variable {P : Numerics.Profile}

theorem stop_of_atCallout {c : Config H} {m : (wasmHostSig H).Op} (h : AtCallout c m) :
    Stop P c := by
  obtain ⟨E, b, hd, -⟩ := h
  exact fun _ => noFree_of_decompose hd

theorem atCallout_unique {c : Config H} {m m' : (wasmHostSig H).Op} (h : AtCallout c m)
    (h' : AtCallout c m') : m = m' := by
  obtain ⟨E, b, hd, hs⟩ := h
  obtain ⟨E', b', hd', hs'⟩ := h'
  rw [hd] at hd'
  simp only [Option.some.injEq, Prod.mk.injEq] at hd'
  obtain ⟨-, -, h₁, h₂⟩ := hd'
  exact Prod.ext h₁ (Prod.ext (hs.symm.trans hs') h₂)

theorem atCallout_of_hEvStep {c c' : Config H} {e : Call (wasmHostSig H)}
    (h : HEvStep P host c (some e) c') : AtCallout c e.1 := by
  obtain ⟨E, b, hd, hs, -, -⟩ := h
  exact ⟨E, b, hd, hs.symm⟩

theorem hEvStep_some_unique {c c₁ c₂ : Config H} {e : Call (wasmHostSig H)}
    (h₁ : HEvStep P host c (some e) c₁) (h₂ : HEvStep P host c (some e) c₂) : c₁ = c₂ := by
  obtain ⟨E₁, a₁, hd₁, -, -, rfl⟩ := h₁
  obtain ⟨E₂, a₂, hd₂, -, -, rfl⟩ := h₂
  rw [hd₁] at hd₂
  simp only [Option.some.injEq, Prod.mk.injEq] at hd₂
  rw [hd₂.1]

theorem decompose?_trap (s : Store H) : SingleThreaded.decompose? s [.trap] = none :=
  SingleThreaded.decompose?_vals_cons_none (vs := []) (r := []) rfl
    fun _ _ => SingleThreaded.decompHead_trap

theorem decompose?_throwing (s : Store H) (a : Nat) :
    SingleThreaded.decompose? s (throwing a) = none :=
  SingleThreaded.decompose?_vals_cons_none (vs := [.ref (.exn a)]) (r := []) rfl
    fun _ _ => SingleThreaded.decompHead_plain rfl

theorem endCfg_stop {e : End (Store H) (List Val ⊕ Nat)} {y : Config H} (h : EndCfg e y) :
    Stop P y := by
  rcases e with ⟨ws | t, s₂⟩ | _ | _
  · subst h; exact fun _ => Step.not_vals
  · subst h; exact fun _ => Step.throwing_stuck
  · obtain ⟨_, rfl⟩ := h; exact fun _ => Step.trap_stuck
  · exact h.elim

theorem endCfg_not_callout {e : End (Store H) (List Val ⊕ Nat)} {y : Config H}
    {m : (wasmHostSig H).Op} (h : EndCfg e y) (hm : AtCallout y m) : False := by
  obtain ⟨E, b, hd, -⟩ := hm
  rcases e with ⟨ws | t, s₂⟩ | _ | _
  · subst h; rw [SingleThreaded.decompose?_vals_nil] at hd; cases hd
  · subst h; rw [decompose?_throwing] at hd; cases hd
  · obtain ⟨_, rfl⟩ := h; rw [decompose?_trap] at hd; cases hd
  · exact h.elim

theorem vals_ne_throwing {ws : List Val} {t : Nat} : vals ws ≠ throwing t :=
  SingleThreaded.Det.vals_ne_append_cons (k := [.ref (.exn t)]) (t := []) rfl

theorem vals_ne_trap {ws : List Val} : vals ws ≠ [.trap] :=
  SingleThreaded.Det.vals_ne_append_cons (k := []) (t := []) rfl

theorem endCfg_unique {e e' : End (Store H) (List Val ⊕ Nat)} {y : Config H} (h : EndCfg e y)
    (h' : EndCfg e' y) : e = e' := by
  rcases e with ⟨ws | t, s₂⟩ | _ | _ <;> rcases e' with ⟨ws' | t', s₂'⟩ | _ | _
  · have h₁ : y = ⟨s₂, {}, vals ws⟩ := h
    have h₂ : y = ⟨s₂', {}, vals ws'⟩ := h'
    rw [h₁] at h₂
    injection h₂ with h₃ _ h₄
    rw [SingleThreaded.vals_injective h₄, h₃]
  · have h₁ : y = ⟨s₂, {}, vals ws⟩ := h
    have h₂ : y = ⟨s₂', {}, throwing t'⟩ := h'
    rw [h₁] at h₂
    exact (vals_ne_throwing (congrArg Config.code h₂)).elim
  · have h₁ : y = ⟨s₂, {}, vals ws⟩ := h
    obtain ⟨_, h₂⟩ := h'
    rw [h₁] at h₂
    exact (vals_ne_trap (congrArg Config.code h₂)).elim
  · exact h'.elim
  · have h₁ : y = ⟨s₂, {}, throwing t⟩ := h
    have h₂ : y = ⟨s₂', {}, vals ws'⟩ := h'
    rw [h₂] at h₁
    exact (vals_ne_throwing (congrArg Config.code h₁)).elim
  · have h₁ : y = ⟨s₂, {}, throwing t⟩ := h
    have h₂ : y = ⟨s₂', {}, throwing t'⟩ := h'
    rw [h₁] at h₂
    injection h₂ with h₃ _ h₄
    simp only [throwing, List.cons.injEq, Admin.ref.injEq, Ref.exn.injEq] at h₄
    rw [h₄.1, h₃]
  · have h₁ : y = ⟨s₂, {}, throwing t⟩ := h
    obtain ⟨_, h₂⟩ := h'
    rw [h₁] at h₂
    have h₃ := congrArg Config.code h₂
    simp at h₃
  · exact h'.elim
  · obtain ⟨_, h₁⟩ := h
    have h₂ : y = ⟨s₂', {}, vals ws'⟩ := h'
    rw [h₂] at h₁
    exact (vals_ne_trap (congrArg Config.code h₁)).elim
  · obtain ⟨_, h₁⟩ := h
    have h₂ : y = ⟨s₂', {}, throwing t'⟩ := h'
    rw [h₂] at h₁
    have h₃ := congrArg Config.code h₁
    simp at h₃
  · rfl
  · exact h'.elim
  all_goals exact h.elim

end Cfg

/-! ## Runs at the deterministic profile -/

section Runs

variable {P : Numerics.Profile}

theorem evRun_split {c c' : Config H} {l : List (Call (wasmHostSig H))}
    (h : EvRun P host c l c') :
    ∀ {cs cs' : List (Call (wasmHostSig H))} {e : Call (wasmHostSig H)}, l = cs ++ e :: cs' →
      ∃ c₁ c₂, EvRun P host c cs c₁ ∧ HEvStep P host c₁ (some e) c₂ ∧
        EvRun P host c₂ cs' c' := by
  induction h with
  | refl => intro cs cs' e hl; simp at hl
  | silent h₁ _ ih =>
    intro cs cs' e hl
    obtain ⟨c₁, c₂, h₁', h₂, h₃⟩ := ih hl
    exact ⟨c₁, c₂, .silent h₁ h₁', h₂, h₃⟩
  | event h₁ hr ih =>
    intro cs cs' e hl
    cases cs with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      exact ⟨_, _, .refl _, h₁, hr⟩
    | cons x cs =>
      simp only [List.cons_append, List.cons.injEq] at hl
      obtain ⟨rfl, hl⟩ := hl
      obtain ⟨c₁, c₂, h₁', h₂, h₃⟩ := ih hl
      exact ⟨c₁, c₂, .event h₁ h₁', h₂, h₃⟩

/-- A run with log `cs ++ x :: r` passes a callout of `x` after the log `cs`. -/
theorem evRun_callout {K y : Config H} {cs r : List (Call (wasmHostSig H))}
    {x : Call (wasmHostSig H)} (h : EvRun P host K (cs ++ x :: r) y) :
    ∃ z, EvRun P host K cs z ∧ AtCallout z x.1 := by
  obtain ⟨z, _, hz, he, -⟩ := evRun_split h rfl
  exact ⟨z, hz, atCallout_of_hEvStep he⟩

theorem evRun_nil_stop {c y : Config H} (hc : Stop P c) (h : EvRun P host c [] y) : y = c := by
  generalize hl : ([] : List (Call (wasmHostSig H))) = l at h
  induction h with
  | refl => rfl
  | silent h₁ _ ih =>
    rcases h₁ with h₁ | ⟨rfl, -⟩
    · exact (hc _ h₁).elim
    · exact ih hc hl
  | event _ _ _ => cases hl

theorem evRun_cons_stop {K K₁ y : Config H} {e : Call (wasmHostSig H)}
    {l : List (Call (wasmHostSig H))} (hK : Stop P K) (he : HEvStep P host K (some e) K₁)
    (h : EvRun P host K (e :: l) y) : EvRun P host K₁ l y := by
  generalize hl : e :: l = l' at h
  induction h with
  | refl => cases hl
  | silent h₁ _ ih =>
    rcases h₁ with h₁ | ⟨rfl, -⟩
    · exact (hK _ h₁).elim
    · exact ih hK he hl
  | event h₁ hr _ =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hl
    rw [hEvStep_some_unique he h₁]
    exact hr

theorem free_of_evRun_nil {o : SingleThreaded.GrowOracle} {x y : Config H}
    (h : EvRun (SingleThreaded.profile o) host x [] y) :
    Relation.ReflTransGen (SingleThreaded.Det.DStep o) x y := by
  generalize hl : ([] : List (Call (wasmHostSig H))) = l at h
  induction h with
  | refl => exact .refl
  | silent h₁ _ ih =>
    rcases h₁ with h₁ | ⟨rfl, -⟩
    · exact .head h₁ (ih hl)
    · exact ih hl
  | event _ _ _ => cases hl

variable {o : SingleThreaded.GrowOracle}

/-- **A run is passed through** by every run with a longer log to a stopped configuration. -/
theorem evRun_through {K x : Config H} {cs : List (Call (wasmHostSig H))}
    (hx : EvRun (SingleThreaded.profile o) host K cs x) :
    ∀ {d : List (Call (wasmHostSig H))} {y : Config H},
      EvRun (SingleThreaded.profile o) host K (cs ++ d) y → Stop (SingleThreaded.profile o) y →
        EvRun (SingleThreaded.profile o) host x d y := by
  induction hx with
  | refl => intro d y h _; simpa using h
  | silent h₁ _ ih =>
    intro d y h hy
    rcases h₁ with h₁ | ⟨rfl, -⟩
    · obtain ⟨n, hn⟩ := evRunN_of_evRun h
      obtain ⟨m, -, hm⟩ := evRunN_through hn hy h₁
      exact ih (evRunN_evRun hm) hy
    · exact ih h hy
  | event h₁ _ ih =>
    intro d y h hy
    rw [List.cons_append] at h
    have hK : Stop (SingleThreaded.profile o) _ := stop_of_atCallout (atCallout_of_hEvStep h₁)
    exact ih (evRun_cons_stop hK h₁ h) hy

/-- **One stopped configuration per log.** -/
theorem evRun_stop_unique {K y₁ y₂ : Config H} {cs : List (Call (wasmHostSig H))}
    (h₁ : EvRun (SingleThreaded.profile o) host K cs y₁) (hy₁ : Stop (SingleThreaded.profile o) y₁)
    (h₂ : EvRun (SingleThreaded.profile o) host K cs y₂)
    (hy₂ : Stop (SingleThreaded.profile o) y₂) : y₁ = y₂ :=
  (evRun_nil_stop hy₁ (evRun_through h₁ (d := []) (by rwa [List.append_nil]) hy₂)).symm

/-- **A typed configuration that diverges host-free reaches no stopped configuration with the
same log.** -/
theorem not_div_stop {K x y : Config H} {cs : List (Call (wasmHostSig H))}
    (hx : EvRun (SingleThreaded.profile o) host K cs x) (ht : Sim.ContextTyped x)
    (hd : Diverges (SingleThreaded.profile o) SingleThreaded.Det.noHost x)
    (hy : EvRun (SingleThreaded.profile o) host K cs y) (hys : Stop (SingleThreaded.profile o) y) :
    False := by
  have hf := free_of_evRun_nil (evRun_through hx (d := []) (by rwa [List.append_nil]) hys)
  obtain ⟨b, hb, -⟩ := (diverges_through_steps hf ht hd).unfold
  exact hys _ hb

end Runs

/-! ## Finished Core behaviours -/

/-- A finished Core behaviour of the runs from `K`: a run to an end configuration, or a run
followed by host-free divergence. -/
def FinB (P : Numerics.Profile) (host : HostSemantics H) (K : Config H)
    (x : CallBeh (wasmHostSig H) (Store H) (List Val ⊕ Nat)) : Prop :=
  (∃ y, EvRun P host K x.1 y ∧ EndCfg x.2 y) ∨
    (x.2 = .div ∧ ∃ y, EvRun P host K x.1 y ∧ Diverges P SingleThreaded.Det.noHost y)

section Fin

variable {o : SingleThreaded.GrowOracle} {K : Config H}

theorem finB_run {x : CallBeh (wasmHostSig H) (Store H) (List Val ⊕ Nat)}
    (h : FinB (SingleThreaded.profile o) host K x) :
    ∃ y, EvRun (SingleThreaded.profile o) host K x.1 y := by
  rcases h with ⟨y, hy, -⟩ | ⟨-, y, hy, -⟩ <;> exact ⟨y, hy⟩

theorem typed_of_evRun (hT : HostTyped host) (hK : Sim.ContextTyped K) {cs y}
    (h : EvRun (SingleThreaded.profile o) host K cs y) : Sim.ContextTyped y :=
  ContextTyped.steps_typed hT hK (evRun_steps h)

/-- A finished behaviour never shares its log with a reached callout. -/
theorem finB_callout (hT : HostTyped host) (hK : Sim.ContextTyped K) {c : List (Call (wasmHostSig H))}
    {e : End (Store H) (List Val ⊕ Nat)} {z : Config H} {m : (wasmHostSig H).Op}
    (h : FinB (SingleThreaded.profile o) host K (c, e))
    (hz : EvRun (SingleThreaded.profile o) host K c z) (hm : AtCallout z m) : False := by
  rcases h with ⟨y, hy, he⟩ | ⟨-, y, hy, hd⟩
  · have := evRun_stop_unique hy (endCfg_stop he) hz (stop_of_atCallout hm)
    subst this
    exact endCfg_not_callout he hm
  · exact not_div_stop hy (typed_of_evRun hT hK hy) hd hz (stop_of_atCallout hm)

/-- A finished behaviour's log is not a strict prefix of a run's log. -/
theorem finB_prefix (hT : HostTyped host) (hK : Sim.ContextTyped K)
    {c r : List (Call (wasmHostSig H))} {e : End (Store H) (List Val ⊕ Nat)}
    {x : Call (wasmHostSig H)} {y : Config H} (h : FinB (SingleThreaded.profile o) host K (c, e))
    (hy : EvRun (SingleThreaded.profile o) host K (c ++ x :: r) y) : False := by
  obtain ⟨z, hz, hm⟩ := evRun_callout hy
  exact finB_callout hT hK h hz hm

/-- Two runs make the same call after a common log. -/
theorem evRun_next {p r₁ r₂ : List (Call (wasmHostSig H))} {x₁ x₂ : Call (wasmHostSig H)}
    {y₁ y₂ : Config H} (h₁ : EvRun (SingleThreaded.profile o) host K (p ++ x₁ :: r₁) y₁)
    (h₂ : EvRun (SingleThreaded.profile o) host K (p ++ x₂ :: r₂) y₂) : x₁.1 = x₂.1 := by
  obtain ⟨z₁, hz₁, hm₁⟩ := evRun_callout h₁
  obtain ⟨z₂, hz₂, hm₂⟩ := evRun_callout h₂
  have := evRun_stop_unique hz₁ (stop_of_atCallout hm₁) hz₂ (stop_of_atCallout hm₂)
  subst this
  exact atCallout_unique hm₁ hm₂

/-- Finished behaviours with the same log have the same end. -/
theorem finB_end (hT : HostTyped host) (hK : Sim.ContextTyped K) {c : List (Call (wasmHostSig H))}
    {e₁ e₂ : End (Store H) (List Val ⊕ Nat)} (h₁ : FinB (SingleThreaded.profile o) host K (c, e₁))
    (h₂ : FinB (SingleThreaded.profile o) host K (c, e₂)) : e₁ = e₂ := by
  rcases h₁ with ⟨y₁, hy₁, he₁⟩ | ⟨hd₁, y₁, hy₁, hv₁⟩ <;>
    rcases h₂ with ⟨y₂, hy₂, he₂⟩ | ⟨hd₂, y₂, hy₂, hv₂⟩
  · have := evRun_stop_unique hy₁ (endCfg_stop he₁) hy₂ (endCfg_stop he₂)
    subst this
    exact endCfg_unique he₁ he₂
  · exact (not_div_stop hy₂ (typed_of_evRun hT hK hy₂) hv₂ hy₁ (endCfg_stop he₁)).elim
  · exact (not_div_stop hy₁ (typed_of_evRun hT hK hy₁) hv₁ hy₂ (endCfg_stop he₂)).elim
  · exact hd₁.trans hd₂.symm

/-- **Finished Core behaviours agree** until the host answers differ. -/
theorem finB_agree (hT : HostTyped host) (hK : Sim.ContextTyped K)
    {x y : CallBeh (wasmHostSig H) (Store H) (List Val ⊕ Nat)}
    (hx : FinB (SingleThreaded.profile o) host K x) (hy : FinB (SingleThreaded.profile o) host K y) :
    AFun.Agree x.1 x.2 y.1 y.2 := by
  obtain ⟨cx, ex⟩ := x
  obtain ⟨cy, ey⟩ := y
  obtain ⟨zx, hzx⟩ := finB_run hx
  obtain ⟨zy, hzy⟩ := finB_run hy
  refine agree_of (fun p x₁ r₁ x₂ r₂ h₁ h₂ => ?_) (fun x r h => ?_) (fun x r h => ?_) ?_
  · subst h₁ h₂; exact evRun_next hzx hzy
  · subst h; exact finB_prefix hT hK hx hzy
  · subst h; exact finB_prefix hT hK hy hzx
  · intro h; subst h; exact finB_end hT hK hx hy

end Fin

/-! ## Triples -/

section Triple

variable {o : SingleThreaded.GrowOracle}

/-- **A triple of finished Core behaviours from typed starts, with reached callouts as call
prefixes, has a deterministic saturation.** -/
theorem tripleDet_sat (hT : HostTyped host)
    {T : ObsTriple (wasmHostSig H) (Store H) (Nat × List Val) (List Val ⊕ Nat)}
    (K : Store H → Nat × List Val → Config H)
    (h₁ : ∀ s q x, x ∈ T.1 s q →
      Sim.ContextTyped (K s q) ∧ FinB (SingleThreaded.profile o) host (K s q) x)
    (h₂ : ∀ s q x, x ∈ StratObs.satP T s q →
      ∃ c, EvRun (SingleThreaded.profile o) host (K s q) x.1 c ∧ AtCallout c x.2) :
    TripleDet (StratObs.sat T) where
  fin s q x y hx hy := finB_agree hT (h₁ s q x hx).1 (h₁ s q x hx).2 (h₁ s q y hy).2
  pend s q c m m' hm hm' := by
    obtain ⟨z, hz, hzm⟩ := h₂ s q _ hm
    obtain ⟨z', hz', hzm'⟩ := h₂ s q _ hm'
    have := evRun_stop_unique hz (stop_of_atCallout hzm) hz' (stop_of_atCallout hzm')
    subst this
    exact atCallout_unique hzm hzm'
  excl s q c e m he hm := by
    obtain ⟨z, hz, hzm⟩ := h₂ s q _ hm
    exact finB_callout hT (h₁ s q _ he).1 (h₁ s q _ he).2 hz hzm
  inf _ _ ω hω k := .inr (.inr (.inr ⟨ω, hω, k, rfl, rfl⟩))

theorem typed_invoke {s : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hok : InvokeOk s a vs) : Sim.ContextTyped (invoke s a vs) := by
  obtain ⟨_, _, _, -, -, hcok⟩ := invoke_ok hs hok
  exact .of_configOk hcok

theorem finB_coreXP {s : Store H} {q : Nat × List Val}
    {x : CallBeh (wasmHostSig H) (Store H) (List Val ⊕ Nat)}
    (h : CoreObsLXP (SingleThreaded.profile o) host s q.1 q.2 (.done x.1 x.2) ∨
      (x.2 = .div ∧ CoreObsLXP (SingleThreaded.profile o) host s q.1 q.2 (.div x.1))) :
    FinB (SingleThreaded.profile o) host (invoke s q.1 q.2) x := by
  obtain ⟨c, e⟩ := x
  rcases h with h | ⟨rfl, h⟩
  · left
    match e, h with
    | .ret (.inl _) _, h => exact ⟨_, h, rfl⟩
    | .ret (.inr _) _, h => exact ⟨_, h, rfl⟩
    | .trap, ⟨s₂, h⟩ => exact ⟨_, h, s₂, rfl⟩
    | .div, h => exact h.elim
  · exact .inr ⟨rfl, h⟩

theorem coreObsLXP_of_done {s : Store H} {a : Nat} {vs : List Val}
    {c : List (Call (wasmHostSig H))} {e : End (Store H) (List Val ⊕ Nat)}
    (h : CoreObsL (SingleThreaded.profile o) host s a vs (.done c e)) :
    CoreObsLXP (SingleThreaded.profile o) host s a vs (.done c e) :=
  match e, h with
  | .ret (.inl _) _, h => h
  | .ret (.inr _) _, h => (h : False).elim
  | .trap, h => h
  | .div, h => (h : False).elim

variable {Ok : Store H → Nat × List Val → Prop}

theorem coreTriple_det (hT : HostTyped host)
    (hOk : ∀ s q, Ok s q → StoreOk s ∧ InvokeOk s q.1 q.2) :
    TripleDet (StratObs.sat (coreTriple (SingleThreaded.profile o) host Ok)) :=
  tripleDet_sat hT (fun s q => invoke s q.1 q.2)
    (fun s q _ ⟨hq, h⟩ => ⟨typed_invoke (hOk s q hq).1 (hOk s q hq).2,
      finB_coreXP (h.imp coreObsLXP_of_done id)⟩)
    (fun _ _ _ h => (coreTriple_satP_callout h).2)

theorem coreTripleXP_det (hT : HostTyped host)
    (hOk : ∀ s q, Ok s q → StoreOk s ∧ InvokeOk s q.1 q.2) :
    TripleDet (StratObs.sat (coreTripleXP (SingleThreaded.profile o) host Ok)) :=
  tripleDet_sat hT (fun s q => invoke s q.1 q.2)
    (fun s q _ ⟨hq, h⟩ => ⟨typed_invoke (hOk s q hq).1 (hOk s q hq).2, finB_coreXP h⟩)
    (fun _ _ _ h => (coreTripleXP_satP_callout h).2)

end Triple

/-! ## The public restriction -/

section Pub

variable {T : ObsTriple (wasmHostSig H) (Store H) (Nat × List Val) (List Val ⊕ Nat)}

theorem satP_pubTriple (s : Store H) (a : Nat) (u : PUnit) (vs : List Val) :
    StratObs.satP (pubTriple T s a) u vs = StratObs.satP T s (a, vs) := by
  ext x
  constructor
  · rintro (h | h | ⟨d, e, ⟨e', h, -⟩, hp⟩ | h)
    exacts [.inl h, .inr (.inl h), .inr (.inr (.inl ⟨d, e', h, hp⟩)), .inr (.inr (.inr h))]
  · rintro (h | h | ⟨d, e, h, hp⟩ | h)
    exacts [.inl h, .inr (.inl h), .inr (.inr (.inl ⟨d, pubEnd e, ⟨e, h, rfl⟩, hp⟩)),
      .inr (.inr (.inr h))]

/-- **The public restriction of a triple with a deterministic saturation has one.** -/
theorem pubTriple_det (hd : TripleDet (StratObs.sat T)) (s : Store H) (a : Nat) :
    TripleDet (StratObs.sat (pubTriple T s a)) where
  fin u vs x y hx hy := by
    obtain ⟨e₁, hx, h₁⟩ := hx
    obtain ⟨e₂, hy, h₂⟩ := hy
    rw [← h₁, ← h₂]
    exact agree_map pubEnd (hd.fin s (a, vs) _ _ hx hy)
  pend u vs c m m' hm hm' := by
    change _ ∈ StratObs.satP (pubTriple T s a) u vs at hm hm'
    rw [satP_pubTriple] at hm hm'
    exact hd.pend s (a, vs) c m m' hm hm'
  excl u vs c e m he hm := by
    obtain ⟨e', he, -⟩ := he
    change _ ∈ StratObs.satP (pubTriple T s a) u vs at hm
    rw [satP_pubTriple] at hm
    exact hd.excl s (a, vs) c e' m he hm
  inf u vs ω hω k := by
    change _ ∈ StratObs.satP (pubTriple T s a) u vs
    rw [satP_pubTriple]
    exact hd.inf s (a, vs) ω hω k

end Pub

end Silmaril.Proofs.Wasm.Abstract.CoreDet

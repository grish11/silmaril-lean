module

public import Silmaril.Proofs.Wasm.Cfg.ProfileFree.Step
public import Silmaril.Wasm.Abstract.HostCall.Defs
public import Silmaril.Wasm.Abstract.HostSessionXP.Defs
public import Silmaril.Wasm.Abstract.HostSquareXP.Defs
public import Silmaril.Wasm.Abstract.NodeBridge.Defs
public import Silmaril.Wasm.SingleThreaded.Thread

@[expose] public section

/-!
# Profile-free Core code: runs and observations (proofs)

Along every Core run of a profile-free configuration (`ConfigFree`) against a host keeping the
functions profile-free (`HostFree`), every configuration is profile-free and every step is a step
at every other profile. The witnesses are kept: the same labelled runs, the same infinite traces
and the same segmented productive runs (no choice, no compactness).

* `hEvStep_profile`, `evRun_profile`, `rtg_profile`, `diverges_profile`, `coreInf_profile`;
* the Core observations of an invocation on a store with profile-free functions:
  `coreObsLXP_profile_iff`, `coreBehSXP_profile_iff`, `coreCallout_profile_iff`, and the
  componentwise equality of the open Core triples `coreTripleSO_profile`.
-/

namespace Silmaril.Wasm.Cfg.Proofs.ProfileFree

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm.Cfg.ProfileFree
open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract (wasmHostSig HEvStep EvRun CoreInf CoreObsLXP CoreBehSXP)
open Silmaril.Wasm.Abstract.NodeBridge (CoreCallout coreTripleSO)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SingleThreaded (Ctx decompose?)

variable {H : Type} {P P' : Profile} {host : HostSemantics H}

/-! ## Configurations -/

theorem fill_free (E : Ctx) {xs ys : List Admin} (hx : ∀ a ∈ E.fill xs, AFree a)
    (hy : ∀ a ∈ ys, AFree a) : ∀ a ∈ E.fill ys, AFree a := by
  induction E with
  | top pre rest =>
    simp only [Ctx.fill, List.forall_mem_append] at hx ⊢
    exact ⟨⟨hx.1.1, hy⟩, hx.2⟩
  | label _ _ _ _ _ ih =>
    simp only [Ctx.fill, List.forall_mem_append, List.forall_mem_singleton] at hx ⊢
    obtain ⟨hc, hb⟩ := afree_label_inv hx.1.2
    exact ⟨⟨hx.1.1, .label _ hc (ih hb)⟩, hx.2⟩
  | handler _ _ _ _ _ ih =>
    simp only [Ctx.fill, List.forall_mem_append, List.forall_mem_singleton] at hx ⊢
    exact ⟨⟨hx.1.1, .handler _ _ (ih (afree_handler_inv hx.1.2))⟩, hx.2⟩
  | frame _ _ _ _ _ ih =>
    simp only [Ctx.fill, List.forall_mem_append, List.forall_mem_singleton] at hx ⊢
    exact ⟨⟨hx.1.1, .frame _ _ (ih (afree_frame_inv hx.1.2))⟩, hx.2⟩

theorem hostFree_none : HostFree (fun _ _ _ _ => False : HostSemantics H) :=
  fun _ _ _ _ _ h => h.elim

theorem hostFree_of_storePreserving (h : Abstract.NodeBridge.StorePreserving host) : HostFree host :=
  fun _ _ _ _ _ hh hF => (h _ _ _ _ _ hh) ▸ hF

theorem configFree_invoke {s : Store H} (hF : FuncsFree s.funcs) (a : Nat) (vs : List Val) :
    ConfigFree (invoke s a vs) := by
  refine ⟨?_, hF⟩
  simp only [invoke, List.forall_mem_append, List.forall_mem_cons]
  exact ⟨afree_vals vs, .ref _, .callRefType _, fun _ h => nomatch h⟩

theorem ConfigFree.step (hH : HostFree host) {c c' : Config H} (hc : ConfigFree c)
    (h : Step P host c c') : ConfigFree c' :=
  (step_free h hH hc.2 hc.1).symm

/-! ## Labelled steps and runs -/

/-- **A labelled step of a profile-free configuration is one at every profile**, to a
profile-free configuration. -/
theorem hEvStep_profile (hH : HostFree host) {c c' : Config H} (hc : ConfigFree c)
    {l : Option (Call (wasmHostSig H))} (h : HEvStep P host c l c') :
    HEvStep P' host c l c' ∧ ConfigFree c' := by
  cases l with
  | none =>
    rcases h with h | ⟨rfl, hdiv⟩
    · exact ⟨.inl (step_profile h hc.1), ConfigFree.step hostFree_none hc h⟩
    · exact ⟨.inr ⟨rfl, hdiv⟩, hc⟩
  | some e =>
    obtain ⟨E, a, hd, hs, hh, rfl⟩ := h
    refine ⟨⟨E, a, hd, hs, hh, rfl⟩, ?_, hH _ _ _ _ _ hh hc.2⟩
    obtain ⟨_, _, _, _, -, -, -, -, -, hcode⟩ := SingleThreaded.decompose?_sound hd
    exact fill_free E (hcode ▸ hc.1) (afree_result _)

theorem rtg_profile (hH : HostFree host) {c c' : Config H} (hc : ConfigFree c)
    (h : Relation.ReflTransGen (fun a b => HEvStep P host a none b) c c') :
    Relation.ReflTransGen (fun a b => HEvStep P' host a none b) c c' ∧ ConfigFree c' := by
  induction h with
  | refl => exact ⟨.refl, hc⟩
  | tail _ hs ih =>
    obtain ⟨h1, h2⟩ := ih
    obtain ⟨h3, h4⟩ := hEvStep_profile (P' := P') hH h2 hs
    exact ⟨h1.tail h3, h4⟩

/-- **A labelled run of a profile-free configuration is one at every profile**, ending in a
profile-free configuration. -/
theorem evRun_profile (hH : HostFree host) {c c' : Config H} (hc : ConfigFree c)
    {cs : List (Call (wasmHostSig H))} (h : EvRun P host c cs c') :
    EvRun P' host c cs c' ∧ ConfigFree c' := by
  induction h with
  | refl => exact ⟨.refl _, hc⟩
  | silent hs _ ih =>
    obtain ⟨h1, h2⟩ := hEvStep_profile (P' := P') hH hc hs
    obtain ⟨h3, h4⟩ := ih h2
    exact ⟨.silent h1 h3, h4⟩
  | event hs _ ih =>
    obtain ⟨h1, h2⟩ := hEvStep_profile (P' := P') hH hc hs
    obtain ⟨h3, h4⟩ := ih h2
    exact ⟨.event h1 h3, h4⟩

theorem evRun_profile_iff (hH : HostFree host) {c c' : Config H} (hc : ConfigFree c)
    {cs : List (Call (wasmHostSig H))} : EvRun P host c cs c' ↔ EvRun P' host c cs c' :=
  ⟨fun h => (evRun_profile hH hc h).1, fun h => (evRun_profile hH hc h).1⟩

/-- **Divergence of a profile-free configuration is divergence at every profile**, along the same
infinite trace. -/
theorem diverges_profile (hH : HostFree host) {c : Config H} (hc : ConfigFree c)
    (h : Diverges P host c) : Diverges P' host c := by
  obtain ⟨tr, h0, hs⟩ := h
  have hfree : ∀ n, ConfigFree (tr n) := by
    intro n
    induction n with
    | zero => exact h0 ▸ hc
    | succ n ih => exact ConfigFree.step hH ih (hs n)
  exact ⟨tr, h0, fun n => step_profile (hs n) (hfree n).1⟩

theorem diverges_profile_iff (hH : HostFree host) {c : Config H} (hc : ConfigFree c) :
    Diverges P host c ↔ Diverges P' host c :=
  ⟨diverges_profile hH hc, diverges_profile hH hc⟩

/-- **A productive run of a profile-free configuration is one at every profile**, with the same
segmentation. -/
theorem coreInf_profile (hH : HostFree host) {c : Config H} (hc : ConfigFree c)
    {ω : Nat → Call (wasmHostSig H)} (h : CoreInf P host c ω) : CoreInf P' host c ω := by
  obtain ⟨g, hg0, hg⟩ := h
  have hfree : ∀ n, ConfigFree (g n) := by
    intro n
    induction n with
    | zero => exact hg0 ▸ hc
    | succ n ih =>
      obtain ⟨c₁, hr, he⟩ := hg n
      exact (hEvStep_profile (P' := P) hH (rtg_profile (P' := P) hH ih hr).2 he).2
  refine ⟨g, hg0, fun n => ?_⟩
  obtain ⟨c₁, hr, he⟩ := hg n
  obtain ⟨hr', hc₁⟩ := rtg_profile (P' := P') hH (hfree n) hr
  exact ⟨c₁, hr', (hEvStep_profile hH hc₁ he).1⟩

theorem coreInf_profile_iff (hH : HostFree host) {c : Config H} (hc : ConfigFree c)
    {ω : Nat → Call (wasmHostSig H)} : CoreInf P host c ω ↔ CoreInf P' host c ω :=
  ⟨coreInf_profile hH hc, coreInf_profile hH hc⟩

/-! ## Observations -/

variable {s : Store H}

/-- **The Core observations with exceptions of a store with profile-free functions are
profile-independent.** -/
theorem coreObsLXP_profile_iff (hH : HostFree host) (hF : FuncsFree s.funcs) (a : Nat)
    (vs : List Val) (o : Abstract.FullObs H) :
    CoreObsLXP P host s a vs o ↔ CoreObsLXP P' host s a vs o := by
  have hc := configFree_invoke hF a vs
  rcases o with ⟨cs, (⟨(ws | t), s₂⟩ | _ | _)⟩ | ⟨cs, ⟨hh, s', us⟩⟩ | ⟨cs, ⟨hh, s', us⟩⟩ | cs | ω
  · exact evRun_profile_iff hH hc
  · exact evRun_profile_iff hH hc
  · exact exists_congr fun _ => evRun_profile_iff hH hc
  · exact Iff.rfl
  · exact exists_congr fun c => exists_congr fun _ => exists_congr fun _ =>
      and_congr_left fun _ => evRun_profile_iff hH hc
  · exact exists_congr fun c => exists_congr fun _ => exists_congr fun _ =>
      and_congr_left fun _ => evRun_profile_iff hH hc
  · refine exists_congr fun c' => ⟨fun ⟨h₁, h₂⟩ => ?_, fun ⟨h₁, h₂⟩ => ?_⟩
    · obtain ⟨h₁', hc'⟩ := evRun_profile (P' := P') hH hc h₁
      exact ⟨h₁', diverges_profile hostFree_none hc' h₂⟩
    · obtain ⟨h₁', hc'⟩ := evRun_profile (P' := P) hH hc h₁
      exact ⟨h₁', diverges_profile hostFree_none hc' h₂⟩
  · exact coreInf_profile_iff hH hc

theorem coreBehSXP_profile_iff (hH : HostFree host) (hF : FuncsFree s.funcs)
    (q : Nat × List Val) (y : CallBeh (wasmHostSig H) (Store H) ((List Val ⊕ Nat) ⊕ PUnit)) :
    CoreBehSXP P host s q y ↔ CoreBehSXP P' host s q y := by
  obtain ⟨cs, e⟩ := y
  rcases e with ⟨(r | u), s₂⟩ | _ | _
  · exact coreObsLXP_profile_iff hH hF _ _ _
  · exact evRun_profile_iff hH (configFree_invoke hF _ _)
  · exact Iff.rfl
  · exact coreObsLXP_profile_iff hH hF q.1 q.2 (.div cs)

theorem coreCallout_profile_iff (hH : HostFree host) (hF : FuncsFree s.funcs)
    (q : Nat × List Val) (x : List (Call (wasmHostSig H)) × (wasmHostSig H).Op) :
    CoreCallout P host s q x ↔ CoreCallout P' host s q x :=
  exists_congr fun _ => exists_congr fun _ => exists_congr fun _ =>
    and_congr_left fun _ => evRun_profile_iff hH (configFree_invoke hF _ _)

/-- **The open Core triple at a store with profile-free functions is profile-independent**,
componentwise. -/
theorem coreTripleSO_profile (hH : HostFree host) (hF : FuncsFree s.funcs) (q : Nat × List Val) :
    (coreTripleSO P host).1 s q = (coreTripleSO P' host).1 s q ∧
      (coreTripleSO P host).2.1 s q = (coreTripleSO P' host).2.1 s q ∧
      (coreTripleSO P host).2.2 s q = (coreTripleSO P' host).2.2 s q := by
  refine ⟨Set.ext fun y => ?_, Set.ext fun x => coreCallout_profile_iff hH hF q x,
    Set.ext fun ω => ?_⟩
  · exact and_congr_right fun _ => coreBehSXP_profile_iff hH hF q y
  · exact and_congr_right fun _ => coreObsLXP_profile_iff hH hF _ _ _

end Silmaril.Wasm.Cfg.Proofs.ProfileFree

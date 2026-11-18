module

public import Silmaril.Wasm.Cfg.ProfileFree.Thms
public import Silmaril.Wasm.Cfg.DanglingSession.Thms
public import Silmaril.Wasm.Abstract.BackInv.Thms
public import Silmaril.Wasm.Abstract.NodeBridge.Thms
public import Silmaril.Proofs.Wasm.Cfg.CfgInst
public import Silmaril.Wasm.Cfg.CfgLegalComp.Thms
public import Silmaril.Wasm.Cfg.SessionCheck.Thms

@[expose] public section

/-!
# The backward simulations and sessions at every numeric profile (proofs)

On a store whose functions are profile-free (`ProfileFree.FuncsFree`, e.g. in the checker's
instruction profile), the open Core triple, hence the instance triple `instTripleS I P`, does not
depend on `P` (`ProfileFree.coreTripleSO_profile` at the store-preserving host `instHost I`).
Every finished round keeps the functions profile-free (its end store is the store of a
profile-free configuration), so the instance session does not depend on `P` either
(`instSession_profile`). The deterministic-profile results transfer:
`instTripleS_agree_cfgInstTripleU_P`, `agree_P`, `threadS_eq_P`, `instSession_eq_P`,
`instSession_eq_of_supported_P`, `infRounds_iff_P`; and for every `BackInv`,
`coreBehSXP_mem_P`, `coreCallout_mem_P`, `coreInf_mem_P`.
-/

namespace Silmaril.Wasm.Cfg.Proofs.DanglingProfile

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game
open Silmaril.Wasm.Cfg.ProfileFree Silmaril.Wasm.Cfg.CfgInst Silmaril.Wasm.Cfg.DanglingExn
open Silmaril.Wasm.Cfg.DanglingSession
open Silmaril.Wasm.Abstract (wasmHostSig CoreBehSXP CoreInf)
open Silmaril.Wasm.Abstract.NodeBridge (instHost qOf viewTriple viewEnd coreTripleSO CoreCallout)
open Silmaril.Wasm.Abstract.InstSession (instTripleS instSession)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile neverFail)
open Silmaril.Games.Abstract.StratThread (Reach InfRounds)

variable {I : ScalarInstance} {P P' : Numerics.Profile}

theorem hostFree_instHost : HostFree (instHost I) :=
  hostFree_of_storePreserving Abstract.NodeBridge.storePreserving_instHost

/-- **The instance triple at a store with profile-free functions is profile-independent.** -/
theorem instTripleS_profile {s : Store Nat} (hF : FuncsFree s.funcs) (a : I.F.Op) :
    AgreeAt (instTripleS I P) (instTripleS I P') s a := by
  obtain ⟨h₁, h₂, h₃⟩ := coreTripleSO_profile (P := P) (P' := P') hostFree_instHost hF (qOf I a)
  rw [Abstract.NodeBridge.instTripleS_eq_viewTriple, Abstract.NodeBridge.instTripleS_eq_viewTriple]
  refine ⟨?_, ?_, ?_⟩
  · show {x | ∃ y ∈ (coreTripleSO P (instHost I)).1 s (qOf I a), _} =
      {x | ∃ y ∈ (coreTripleSO P' (instHost I)).1 s (qOf I a), _}
    rw [h₁]
  · show {x | ∃ y ∈ (coreTripleSO P (instHost I)).2.1 s (qOf I a), _} =
      {x | ∃ y ∈ (coreTripleSO P' (instHost I)).2.1 s (qOf I a), _}
    rw [h₂]
  · show {ω | ∃ ω' ∈ (coreTripleSO P (instHost I)).2.2 s (qOf I a), _} =
      {ω | ∃ ω' ∈ (coreTripleSO P' (instHost I)).2.2 s (qOf I a), _}
    rw [h₃]

/-- **A finished round keeps the functions profile-free**: its end store is the store of the
final configuration of a labelled run from a profile-free invocation. -/
theorem funcsFree_of_round {s s₁ : Store Nat} (hF : FuncsFree s.funcs) {a : I.F.Op}
    {c : List (Call I.E)} {b : Abstract.InstSession.Res I.exports ⊕ PUnit}
    (hm : (c, .ret b s₁) ∈ (instTripleS I P).1 s a) : FuncsFree s₁.funcs := by
  rw [Abstract.NodeBridge.instTripleS_eq_viewTriple] at hm
  obtain ⟨⟨cs, e⟩, ⟨-, hy⟩, -, hv⟩ := hm
  have hc := configFree_invoke hF (qOf I a).1 (qOf I a).2
  rcases e with ⟨(r | u), s₂⟩ | _ | _
  · have hs : s₂ = s₁ := by
      simp only [viewEnd, Option.map_eq_some_iff] at hv
      obtain ⟨_, -, h⟩ := hv
      cases h; rfl
    subst hs
    rcases r with ws | t
    · exact (evRun_free hostFree_instHost hc hy).2
    · exact (evRun_free hostFree_instHost hc hy).2
  · have hs : s₂ = s₁ := by
      simp only [viewEnd, Option.map_eq_some_iff] at hv
      obtain ⟨_, -, h⟩ := hv
      cases h; rfl
    subst hs
    exact (evRun_free hostFree_instHost hc hy).2
  · simp [viewEnd] at hv
  · simp [viewEnd] at hv

theorem funcsFree_of_reach {s₀ s : Store Nat} (hF : FuncsFree s₀.funcs)
    (hr : Reach (instTripleS I P) s₀ s) : FuncsFree s.funcs := by
  induction hr with
  | refl => exact hF
  | step hm _ ih => exact ih (funcsFree_of_round hF hm)

/-- **The instance session from a store with profile-free functions is profile-independent.** -/
theorem instSession_profile {s₀ : Store Nat} (hF : FuncsFree s₀.funcs) :
    instSession I P s₀ = instSession I P' s₀ :=
  Proofs.CfgInst.threadS_eq_of_agree fun _ hr a => instTripleS_profile (funcsFree_of_reach hF hr) a

theorem agreeAt_trans {E : Sig.{0}} {S A B : Type} {t₁ t₂ t₃ : ObsTriple E S A B} {s : S} {a : A}
    (h₁ : AgreeAt t₁ t₂ s a) (h₂ : AgreeAt t₂ t₃ s a) : AgreeAt t₁ t₃ s a :=
  ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, h₁.2.2.trans h₂.2.2⟩

/-- **Per question, at every profile**, on a well-formed store in the checker's profile. -/
theorem instTripleS_agree_cfgInstTripleU_P {s : Store Nat} (hw : I.WellFormed s)
    (hsup : Interp.CheckComplete.StoreSupported s.funcs) (a : I.F.Op) :
    AgreeAt (instTripleS I P) (cfgInstTripleU I) s a :=
  agreeAt_trans (instTripleS_profile (P' := profile neverFail) (funcsFree_of_storeSupported hsup) a)
    (DanglingBack.instTripleS_agree_cfgInstTripleU hw hsup a)

/-- **Per question on the relaxed domain, at every profile**, with profile-free functions. -/
theorem agree_P {s : Store Nat} (hd : InstDomD I s) (hF : FuncsFree s.funcs) (a : I.F.Op) :
    AgreeAt (instTripleS I P) (cfgInstTripleU I) s a :=
  agreeAt_trans (instTripleS_profile (P' := profile neverFail) hF a) (agree hd a)

/-- **The instance session is the CFG session, at every profile**, from the relaxed domain with
profile-free functions. -/
theorem threadS_eq_P {s₀ : Store Nat} (hd : InstDomD I s₀) (hF : FuncsFree s₀.funcs) :
    StratSession.threadS (instTripleS I P) s₀ = StratSession.threadS (cfgInstTripleU I) s₀ :=
  (instSession_profile (P' := profile neverFail) hF).trans (threadS_eq hd)

theorem instSession_eq_P {s₀ : Store Nat} (hd : InstDomD I s₀) (hF : FuncsFree s₀.funcs) :
    instSession I P s₀ = cfgInstSessionU I s₀ :=
  threadS_eq_P hd hF

theorem instSession_eq_of_supported_P {s₀ : Store Nat} (hw : I.WellFormed s₀)
    (hsup : Interp.CheckComplete.StoreSupported s₀.funcs) :
    instSession I P s₀ = cfgInstSessionU I s₀ :=
  instSession_eq_P (instDomD_of_supported hw hsup) (funcsFree_of_storeSupported hsup)

/-- **Coherent infinite sequences of rounds agree, at every profile.** -/
theorem infRounds_iff_P {s₀ : Store Nat} (hd : InstDomD I s₀) (hF : FuncsFree s₀.funcs)
    {a : ℕ → I.F.Op} {r : ℕ → List (Call I.E) × (Abstract.InstSession.Res I.exports ⊕ PUnit)}
    {s : ℕ → Store Nat} :
    InfRounds (instTripleS I P) s₀ a r s ↔ InfRounds (cfgInstTripleU I) s₀ a r s := by
  constructor
  · intro h
    refine ⟨h.zero, fun k => ?_⟩
    have hr := reach_of_infRounds h k
    rw [← (agree_P (domD_of_reach hd hr) (funcsFree_of_reach hF hr) (a k)).1]
    exact h.step k
  · intro h
    have hr : ∀ k, Reach (instTripleS I P) s₀ (s k) := by
      intro k
      induction k with
      | zero => exact h.zero ▸ .refl _
      | succ k ih =>
        refine ih.tail (c := (r k).1) (b := (r k).2) (a := a k) ?_
        rw [(agree_P (domD_of_reach hd ih) (funcsFree_of_reach hF ih) (a k)).1]
        exact h.step k
    refine ⟨h.zero, fun k => ?_⟩
    rw [(agree_P (domD_of_reach hd (hr k)) (funcsFree_of_reach hF (hr k)) (a k)).1]
    exact h.step k

/-! ## Store determinism and infinite plays on profile-free stores -/

section Rounds

variable {E : Sig.{0}} {S A B : Type} {t t' : ObsTriple E S A B}

/-- Finite round sequences of two triples agreeing at every store the first reaches. -/
theorem rounds_iff_of_agree {s₀ s : S} {rs : List (A × List (Call E) × B)}
    (h : ∀ s, Reach t s₀ s → ∀ a, t.1 s a = t'.1 s a) :
    StratThread.Rounds t s₀ rs s ↔ StratThread.Rounds t' s₀ rs s := by
  induction rs generalizing s₀ with
  | nil => exact ⟨fun h => by cases h; exact .nil _, fun h => by cases h; exact .nil _⟩
  | cons r rs ih =>
    constructor
    · intro hr
      cases hr with
      | cons hm hr =>
        exact .cons (h _ (.refl _) _ ▸ hm) ((ih fun s hs => h s (.step hm hs)).1 hr)
    · intro hr
      cases hr with
      | cons hm hr =>
        have hm' := (h _ (.refl _) _).symm ▸ hm
        exact .cons hm' ((ih fun s hs => h s (.step hm' hs)).2 hr)

theorem reach_of_rounds {s₀ s : S} {rs : List (A × List (Call E) × B)}
    (h : StratThread.Rounds t s₀ rs s) : Reach t s₀ s := by
  induction h with
  | nil => exact .refl _
  | cons hm _ ih => exact .step hm ih

/-- Coherent infinite round sequences of two triples agreeing at every store the first
reaches. -/
theorem infRounds_iff_of_agree {s₀ : S} {a : ℕ → A} {r : ℕ → List (Call E) × B} {s : ℕ → S}
    (h : ∀ s, Reach t s₀ s → ∀ a, t.1 s a = t'.1 s a) :
    InfRounds t s₀ a r s ↔ InfRounds t' s₀ a r s := by
  constructor
  · intro hi
    exact ⟨hi.zero, fun k => h _ (reach_of_infRounds hi k) _ ▸ hi.step k⟩
  · intro hi
    have hr : ∀ k, Reach t s₀ (s k) := by
      intro k
      induction k with
      | zero => exact hi.zero ▸ .refl _
      | succ k ih =>
        exact ih.tail (c := (r k).1) (b := (r k).2) (a := a k) ((h _ ih _).symm ▸ hi.step k)
    exact ⟨hi.zero, fun k => (h _ (hr k) _).symm ▸ hi.step k⟩

end Rounds

/-- **Store determinism at a store with profile-free functions, every profile**: the final store
of a finished round is determined by the store, the question, the log and the answer. -/
theorem storeDet_at {s s₁ s₂ : Store Nat} (hF : FuncsFree s.funcs) {a : I.F.Op}
    {c : List (Call I.E)} {b : Abstract.InstSession.Res I.exports ⊕ PUnit}
    (h₁ : (c, .ret b s₁) ∈ (instTripleS I P).1 s a) (h₂ : (c, .ret b s₂) ∈ (instTripleS I P).1 s a) :
    s₁ = s₂ := by
  rw [(instTripleS_profile (P' := profile neverFail) hF a).1] at h₁ h₂
  exact Abstract.InstSession.storeDet_instTripleS neverFail s a c b s₁ s₂ h₁ h₂

/-- **The infinite plays of the session, every profile**, from a store with profile-free
functions: a productive stream after completed rounds, or the play of a coherent infinite
sequence of rounds. -/
theorem mem_inf_instSession_P {s₀ : Store Nat} (hF : FuncsFree s₀.funcs)
    {J : Set (List (Move I.E (Abstract.InstSession.ssig I.exports)))} :
    J ∈ (instSession I P s₀).inf ↔
      (∃ rs s a ω, StratThread.Rounds (instTripleS I P) s₀ rs s ∧
        ω ∈ (instTripleS I P).2.2 s a ∧
          J = StratThread.streamPlay (StratSession.sroundsMoves rs) a ω) ∨
      ∃ a r s, InfRounds (instTripleS I P) s₀ a r s ∧ J = StratSession.sroundsPlay a r := by
  have hag : ∀ s, Reach (instTripleS I (profile neverFail)) s₀ s → ∀ a,
      (instTripleS I (profile neverFail)).1 s a = (instTripleS I P).1 s a :=
    fun s hr a => (instTripleS_profile (funcsFree_of_reach hF hr) a).1
  rw [instSession_profile (P' := profile neverFail) hF,
    Abstract.InstSession.mem_inf_instSession neverFail]
  refine or_congr ?_ ?_
  · refine exists_congr fun rs => exists_congr fun s => exists_congr fun a =>
      exists_congr fun ω => ?_
    constructor
    · rintro ⟨hr, hω, rfl⟩
      exact ⟨(rounds_iff_of_agree hag).1 hr,
        (instTripleS_profile (funcsFree_of_reach hF (reach_of_rounds hr)) a).2.2 ▸ hω, rfl⟩
    · rintro ⟨hr, hω, rfl⟩
      have hr' := (rounds_iff_of_agree hag).2 hr
      exact ⟨hr',
        (instTripleS_profile (funcsFree_of_reach hF (reach_of_rounds hr')) a).2.2.symm ▸ hω, rfl⟩
  · exact exists_congr fun a => exists_congr fun r => exists_congr fun s =>
      and_congr_left fun _ => infRounds_iff_of_agree hag

/-! ## The backward simulations, every invariant, every profile -/

section Back

variable {H : Type} (J : Interp.BackInv H) {host : HostSemantics H} {tags : List TagInst}
  {s : Store H} {a : Nat} {vs : List Val}

theorem coreBehSXP_mem_P (hHF : HostFree host) (hF : FuncsFree s.funcs) (hT : J.HostOk host)
    (hH : Interp.HostSliceT host) (hE : Interp.HostSliceE tags host) (hct : J.CT (invoke s a vs))
    (hS : Interp.StoreChkE (Interp.ehExt tags) s.funcs) (hts : Interp.TagsOk tags s)
    (hok : InvokeOk s a vs) {y : CallBeh (wasmHostSig H) (Store H) ((List Val ⊕ Nat) ⊕ PUnit)}
    (hy : CoreBehSXP P host s (a, vs) y) : y ∈ Abstract.wasmEvFunDXPS s (a, vs) :=
  J.coreBehSXP_mem (o := neverFail) hT hH hE hct hS hts hok
    ((coreBehSXP_profile_iff hHF hF _ _).1 hy)

theorem coreCallout_mem_P (hHF : HostFree host) (hF : FuncsFree s.funcs) (hT : J.HostOk host)
    (hH : Interp.HostSliceT host) (hE : Interp.HostSliceE tags host) (hct : J.CT (invoke s a vs))
    (hS : Interp.StoreChkE (Interp.ehExt tags) s.funcs) (hts : Interp.TagsOk tags s)
    (hok : InvokeOk s a vs) {x : List (Call (wasmHostSig H)) × (wasmHostSig H).Op}
    (hx : CoreCallout P host s (a, vs) x) : x ∈ Abstract.wasmEvPendXPS s (a, vs) :=
  J.coreCallout_mem (o := neverFail) hT hH hE hct hS hts hok
    ((coreCallout_profile_iff hHF hF _ _).1 hx)

theorem coreInf_mem_P (hHF : HostFree host) (hF : FuncsFree s.funcs) (hT : J.HostOk host)
    (hH : Interp.HostSliceT host) (hE : Interp.HostSliceE tags host) (hct : J.CT (invoke s a vs))
    (hS : Interp.StoreChkE (Interp.ehExt tags) s.funcs) (hts : Interp.TagsOk tags s)
    (hok : InvokeOk s a vs) {ω : Nat → Call (wasmHostSig H)}
    (h : CoreInf P host (invoke s a vs) ω) : ω ∈ Abstract.wasmEvInfNXP s (a, vs) :=
  J.coreInf_mem (o := neverFail) hT hH hE hct hS hts hok
    ((coreInf_profile_iff hHF (configFree_invoke hF a vs)).1 h)

end Back

/-! ## The legal and throw-free triples and sessions -/

theorem legalT_agree {t t' : ObsTriple (wasmHostSig Nat) (Store Nat) (Nat × List Val)
    ((List Val ⊕ Nat) ⊕ PUnit)} {s : Store Nat} {q : Nat × List Val}
    (h : t.1 s q = t'.1 s q ∧ t.2.1 s q = t'.2.1 s q ∧ t.2.2 s q = t'.2.2 s q) :
    (legalT t).1 s q = (legalT t').1 s q ∧ (legalT t).2.1 s q = (legalT t').2.1 s q ∧
      (legalT t).2.2 s q = (legalT t').2.2 s q := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · show {x | x ∈ t.1 s q ∧ _} = {x | x ∈ t'.1 s q ∧ _}
    rw [h₁]
  · show {x | x ∈ t.2.1 s q ∧ _} = {x | x ∈ t'.2.1 s q ∧ _}
    rw [h₂]
  · show {ω | ω ∈ t.2.2 s q ∧ _} = {ω | ω ∈ t'.2.2 s q ∧ _}
    rw [h₃]

/-- **The legal instance triple at a store with profile-free functions is
profile-independent.** -/
theorem instTripleL_profile {s : Store Nat} (hF : FuncsFree s.funcs) (a : I.F.Op) :
    AgreeAt (instTripleL I P) (instTripleL I P') s a := by
  obtain ⟨h₁, h₂, h₃⟩ := legalT_agree
    (coreTripleSO_profile (P := P) (P' := P') hostFree_instHost hF (qOf I a))
  refine ⟨?_, ?_, ?_⟩
  · show {x | ∃ y ∈ (legalT (coreTripleSO P (instHost I))).1 s (qOf I a), _} =
      {x | ∃ y ∈ (legalT (coreTripleSO P' (instHost I))).1 s (qOf I a), _}
    rw [h₁]
  · show {x | ∃ y ∈ (legalT (coreTripleSO P (instHost I))).2.1 s (qOf I a), _} =
      {x | ∃ y ∈ (legalT (coreTripleSO P' (instHost I))).2.1 s (qOf I a), _}
    rw [h₂]
  · show {ω | ∃ ω' ∈ (legalT (coreTripleSO P (instHost I))).2.2 s (qOf I a), _} =
      {ω | ∃ ω' ∈ (legalT (coreTripleSO P' (instHost I))).2.2 s (qOf I a), _}
    rw [h₃]

theorem noThrowT_agree {S A B : Type} {t t' : ObsTriple I.E S A B} {s : S} {a : A}
    (h : AgreeAt t t' s a) : AgreeAt (noThrowT I t) (noThrowT I t') s a := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · show {x | x ∈ t.1 s a ∧ _} = {x | x ∈ t'.1 s a ∧ _}
    rw [h₁]
  · show {x | x ∈ t.2.1 s a ∧ _} = {x | x ∈ t'.2.1 s a ∧ _}
    rw [h₂]
  · show {ω | ω ∈ t.2.2 s a ∧ _} = {ω | ω ∈ t'.2.2 s a ∧ _}
    rw [h₃]

theorem funcsFree_of_reachL {s₀ s : Store Nat} (hF : FuncsFree s₀.funcs)
    (hr : Reach (instTripleL I P) s₀ s) : FuncsFree s.funcs := by
  induction hr with
  | refl => exact hF
  | step hm _ ih => exact ih (funcsFree_of_round hF ((instTripleL_sub _ _).1 hm))

theorem funcsFree_of_reachNT {s₀ s : Store Nat} (hF : FuncsFree s₀.funcs)
    (hr : Reach (noThrowT I (instTripleS I P)) s₀ s) : FuncsFree s.funcs := by
  induction hr with
  | refl => exact hF
  | step hm _ ih => exact ih (funcsFree_of_round hF hm.1)

/-- **The legal instance session from a store with profile-free functions is
profile-independent.** -/
theorem threadS_instTripleL_profile {s₀ : Store Nat} (hF : FuncsFree s₀.funcs) :
    StratSession.threadS (instTripleL I P) s₀ = StratSession.threadS (instTripleL I P') s₀ :=
  Proofs.CfgInst.threadS_eq_of_agree fun _ hr a =>
    instTripleL_profile (funcsFree_of_reachL hF hr) a

theorem threadS_noThrowT_profile {s₀ : Store Nat} (hF : FuncsFree s₀.funcs) :
    StratSession.threadS (noThrowT I (instTripleS I P)) s₀ =
      StratSession.threadS (noThrowT I (instTripleS I P')) s₀ :=
  Proofs.CfgInst.threadS_eq_of_agree fun _ hr a =>
    noThrowT_agree (instTripleS_profile (funcsFree_of_reachNT hF hr) a)

theorem instTripleL_agree_P {s : Store Nat} (hd : InstDom I s) (hF : FuncsFree s.funcs)
    (a : I.F.Op) : AgreeAt (instTripleL I P) (cfgInstTripleL I) s a :=
  agreeAt_trans (instTripleL_profile (P' := profile neverFail) hF a) (instTripleL_agree hd a)

theorem noThrowT_instTripleS_agree_P {s : Store Nat} (hd : InstDom I s) (hF : FuncsFree s.funcs)
    (a : I.F.Op) : AgreeAt (noThrowT I (instTripleS I P)) (cfgInstTriple I) s a :=
  agreeAt_trans (noThrowT_agree (instTripleS_profile (P' := profile neverFail) hF a))
    (noThrowT_instTripleS_agree hd a)

theorem threadS_instTripleL_eq_P {s₀ : Store Nat} (hd : InstDom I s₀) (hF : FuncsFree s₀.funcs) :
    StratSession.threadS (instTripleL I P) s₀ = StratSession.threadS (cfgInstTripleL I) s₀ :=
  (threadS_instTripleL_profile (P' := profile neverFail) hF).trans (threadS_instTripleL_eq hd)

theorem threadS_noThrowT_eq_P {s₀ : Store Nat} (hd : InstDom I s₀) (hF : FuncsFree s₀.funcs) :
    StratSession.threadS (noThrowT I (instTripleS I P)) s₀ =
      StratSession.threadS (cfgInstTriple I) s₀ :=
  (threadS_noThrowT_profile (P' := profile neverFail) hF).trans (threadS_noThrowT_eq hd)

/-! ## Component semantics -/

section Comp

open Silmaril.Wasm.Component (Comp)
open Silmaril.Wasm.Component.Reference (NumInstance)
open Silmaril.Wasm.Abstract.InstSession (core3SemD threadSemSD)
open Silmaril.Wasm.Cfg.SessionCheck (CompIn)

theorem core3SemD_sem_profile {m : NumInstance} (hF : FuncsFree m.inst.store.funcs) :
    (core3SemD P).sem m = (core3SemD P').sem m :=
  congrArg (Abstract.InstSession.semOfSD m) (instSession_profile hF)

theorem legalSemD_sem_profile {m : NumInstance} (hF : FuncsFree m.inst.store.funcs) :
    (legalSemD P).sem m = (legalSemD P').sem m :=
  congrArg (Abstract.InstSession.semOfSD m) (threadS_instTripleL_profile hF)

theorem denUD_core3SemD_profile (c : Comp NumInstance)
    (hc : CompIn (fun m : NumInstance => FuncsFree m.inst.store.funcs) c) :
    c.denUD (core3SemD P) = c.denUD (core3SemD P') :=
  SessionCheck.denUD_congrIn (fun _ hm => core3SemD_sem_profile hm) c hc

theorem denUD_legalSemD_profile (c : Comp NumInstance)
    (hc : CompIn (fun m : NumInstance => FuncsFree m.inst.store.funcs) c) :
    c.denUD (legalSemD P) = c.denUD (legalSemD P') :=
  SessionCheck.denUD_congrIn (fun _ hm => legalSemD_sem_profile hm) c hc

theorem denUD_cfgSemD_eq_core3_P (c : Comp NumInstance)
    (hc : CompIn (fun m : NumInstance => InstDom m.inst m.inst.store) c)
    (hF : CompIn (fun m : NumInstance => FuncsFree m.inst.store.funcs) c) :
    c.denUD CfgLegal.cfgSemD = c.denUD (core3SemD P) :=
  (CfgLegalComp.denUD_cfgSemD_eq_core3 (o := neverFail) c hc).trans
    (denUD_core3SemD_profile c hF)

theorem denD_cfgSemD_eq_core3_P (c : Comp NumInstance)
    (hc : CompIn (fun m : NumInstance => InstDom m.inst m.inst.store) c)
    (hF : CompIn (fun m : NumInstance => FuncsFree m.inst.store.funcs) c) :
    c.denD CfgLegal.cfgSemD = c.denD (core3SemD P) := by
  unfold Comp.denD
  rw [denUD_cfgSemD_eq_core3_P c hc hF]

end Comp

end Silmaril.Wasm.Cfg.Proofs.DanglingProfile

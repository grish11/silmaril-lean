module

public import Silmaril.Wasm.Cfg.ProfileFree.Thms
public import Silmaril.Wasm.Cfg.DanglingSession.Thms
public import Silmaril.Wasm.Abstract.BackInv.Thms
public import Silmaril.Wasm.Cfg.CfgLegalComp.Thms
public import Silmaril.Wasm.Cfg.SessionCheck.Thms
import Silmaril.Proofs.Wasm.Cfg.DanglingProfile

@[expose] public section

/-!
# The backward simulations and sessions at every numeric profile: theorems

The backward simulations (`Abstract.HostClosingXP`, `HostClosingInfXPBack`, generic over
`Interp.BackInv`) and the instance, legal, throw-free and component results of `CfgInst`,
`CfgLegal`, `CfgLegalComp`, `DanglingBack` and `DanglingSession` are stated at the deterministic
profile `SingleThreaded.profile o`. Here they hold **at every numeric profile `P`** (`nd`,
`relaxed`, `nan`, `grow` arbitrary) on stores whose functions are profile-free
(`ProfileFree.FuncsFree`; the checker's instruction profile `StoreSupported` is, by
`ProfileFree.funcsFree_of_storeSupported`).

**Why determinism was inessential.** Every use of `profile o` in these proofs is a use of Core
steps of supported code: the `BackInv.through` field (a divergent run passes through every
host-free step, `Det.DStep`), the interpreter's exactness (`HostEval`, `evalLXPh`), and the
instance-level equalities built from them. On profile-free code a Core step at `P` is a step at
every `P'` (`ProfileFree.step_profile`), the code stays profile-free along runs whose host answers
keep the functions profile-free (`step_free`; `instHost I` keeps the store), and the open Core
triple is the same at every profile (`ProfileFree.coreTripleSO_profile`), with the same run,
trace and segmented-stream witnesses. So the deterministic-profile results transfer by rewriting;
no new finite-branching or compactness argument is used.

* Instance triples: `instTripleS_profile`, `instTripleL_profile` (`AgreeAt` on all four
  observations at a store with profile-free functions);
* sessions: every finished round keeps the functions profile-free (`funcsFree_of_round`), so
  `instSession_profile`, `threadS_instTripleL_profile`, `threadS_noThrowT_profile` (finite
  plays, pending plays, divergence after a log, productive streams, coherent infinite sequences
  of rounds);
* store determinism and infinite plays: `storeDet_at` (at stores with profile-free functions;
  the session results above use no store determinism), `mem_inf_instSession_P`
  (`InstSession.mem_inf_instSession`, which relies on `StoreDet`, at every profile);
* dangling host exceptions, every profile: `instTripleS_agree_cfgInstTripleU_P`, `agree_P`,
  `threadS_eq_P`, `instSession_eq_P`, `instSession_eq_of_supported_P`, `infRounds_iff_P`;
* legal and throw-free, every profile: `instTripleL_agree_P`, `noThrowT_instTripleS_agree_P`,
  `threadS_instTripleL_eq_P`, `threadS_noThrowT_eq_P`;
* component semantics, every profile: `core3SemD_sem_profile`, `legalSemD_sem_profile`,
  `denUD_core3SemD_profile`, `denUD_legalSemD_profile`, `denUD_cfgSemD_eq_core3_P`,
  `denD_cfgSemD_eq_core3_P`;
* every backward-simulation invariant `J : BackInv`, every profile, with a host keeping the
  functions profile-free: `coreBehSXP_mem_P`, `coreCallout_mem_P`, `coreInf_mem_P`.

**The restriction.** The hypothesis is syntactic: `FuncsFree` (or `StoreSupported`) at the start
store. `InstDomD` and `InstDom` alone accept profile-sensitive instructions in dead code after an
instruction that never falls through (the checker skips it), so they do not give `FuncsFree`; the
results are not claimed there.
-/

namespace Silmaril.Wasm.Cfg.DanglingProfile

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game
open Silmaril.Wasm.Cfg.ProfileFree Silmaril.Wasm.Cfg.CfgInst Silmaril.Wasm.Cfg.DanglingExn
open Silmaril.Wasm.Cfg.DanglingSession
open Silmaril.Wasm.Abstract (wasmHostSig CoreBehSXP CoreInf)
open Silmaril.Wasm.Abstract.NodeBridge (CoreCallout)
open Silmaril.Wasm.Abstract.InstSession (instTripleS instSession core3SemD)
open Silmaril.Games.Abstract.StratThread (Reach InfRounds)
open Silmaril.Wasm.Component (Comp)
open Silmaril.Wasm.Component.Reference (NumInstance)
open Silmaril.Wasm.Cfg.SessionCheck (CompIn)

variable {I : ScalarInstance} {P P' : Numerics.Profile}

/-! ## Profile independence of the instance triples and sessions -/

/-- **The instance triple at a store with profile-free functions is profile-independent**, on
all four observations. -/
theorem instTripleS_profile {s : Store Nat} (hF : FuncsFree s.funcs) (a : I.F.Op) :
    AgreeAt (instTripleS I P) (instTripleS I P') s a :=
  Proofs.DanglingProfile.instTripleS_profile hF a

/-- **A finished round keeps the functions profile-free** (every profile). -/
theorem funcsFree_of_round {s s₁ : Store Nat} (hF : FuncsFree s.funcs) {a : I.F.Op}
    {c : List (Call I.E)} {b : Abstract.InstSession.Res I.exports ⊕ PUnit}
    (hm : (c, .ret b s₁) ∈ (instTripleS I P).1 s a) : FuncsFree s₁.funcs :=
  Proofs.DanglingProfile.funcsFree_of_round hF hm

theorem funcsFree_of_reach {s₀ s : Store Nat} (hF : FuncsFree s₀.funcs)
    (hr : Reach (instTripleS I P) s₀ s) : FuncsFree s.funcs :=
  Proofs.DanglingProfile.funcsFree_of_reach hF hr

/-- **The instance session from a store with profile-free functions is profile-independent.** -/
theorem instSession_profile {s₀ : Store Nat} (hF : FuncsFree s₀.funcs) :
    instSession I P s₀ = instSession I P' s₀ :=
  Proofs.DanglingProfile.instSession_profile hF

theorem instTripleL_profile {s : Store Nat} (hF : FuncsFree s.funcs) (a : I.F.Op) :
    AgreeAt (instTripleL I P) (instTripleL I P') s a :=
  Proofs.DanglingProfile.instTripleL_profile hF a

theorem threadS_instTripleL_profile {s₀ : Store Nat} (hF : FuncsFree s₀.funcs) :
    StratSession.threadS (instTripleL I P) s₀ = StratSession.threadS (instTripleL I P') s₀ :=
  Proofs.DanglingProfile.threadS_instTripleL_profile hF

theorem threadS_noThrowT_profile {s₀ : Store Nat} (hF : FuncsFree s₀.funcs) :
    StratSession.threadS (noThrowT I (instTripleS I P)) s₀ =
      StratSession.threadS (noThrowT I (instTripleS I P')) s₀ :=
  Proofs.DanglingProfile.threadS_noThrowT_profile hF

/-! ## Dangling host exceptions, every profile -/

/-- **Per question, at every profile**: on a well-formed store in the checker's instruction
profile, the instance triple (host `instHost I`, dangling throws included) is the CFG instance
triple at the unrestricted host, on all four observations. -/
theorem instTripleS_agree_cfgInstTripleU_P {s : Store Nat} (hw : I.WellFormed s)
    (hsup : Interp.CheckComplete.StoreSupported s.funcs) (a : I.F.Op) :
    AgreeAt (instTripleS I P) (cfgInstTripleU I) s a :=
  Proofs.DanglingProfile.instTripleS_agree_cfgInstTripleU_P hw hsup a

/-- **Per question on the relaxed domain, at every profile**, with profile-free functions. -/
theorem agree_P {s : Store Nat} (hd : InstDomD I s) (hF : FuncsFree s.funcs) (a : I.F.Op) :
    AgreeAt (instTripleS I P) (cfgInstTripleU I) s a :=
  Proofs.DanglingProfile.agree_P hd hF a

/-- **The instance session is the CFG session at the unrestricted host, at every profile**, from
the relaxed domain with profile-free functions. -/
theorem threadS_eq_P {s₀ : Store Nat} (hd : InstDomD I s₀) (hF : FuncsFree s₀.funcs) :
    StratSession.threadS (instTripleS I P) s₀ = StratSession.threadS (cfgInstTripleU I) s₀ :=
  Proofs.DanglingProfile.threadS_eq_P hd hF

theorem instSession_eq_P {s₀ : Store Nat} (hd : InstDomD I s₀) (hF : FuncsFree s₀.funcs) :
    instSession I P s₀ = cfgInstSessionU I s₀ :=
  Proofs.DanglingProfile.instSession_eq_P hd hF

/-- **At a well-formed store in the checker's instruction profile, at every profile**, the
instance session is the CFG session at the unrestricted host. -/
theorem instSession_eq_of_supported_P {s₀ : Store Nat} (hw : I.WellFormed s₀)
    (hsup : Interp.CheckComplete.StoreSupported s₀.funcs) :
    instSession I P s₀ = cfgInstSessionU I s₀ :=
  Proofs.DanglingProfile.instSession_eq_of_supported_P hw hsup

/-- **Coherent infinite sequences of rounds agree, at every profile.** -/
theorem infRounds_iff_P {s₀ : Store Nat} (hd : InstDomD I s₀) (hF : FuncsFree s₀.funcs)
    {a : ℕ → I.F.Op} {r : ℕ → List (Call I.E) × (Abstract.InstSession.Res I.exports ⊕ PUnit)}
    {s : ℕ → Store Nat} :
    InfRounds (instTripleS I P) s₀ a r s ↔ InfRounds (cfgInstTripleU I) s₀ a r s :=
  Proofs.DanglingProfile.infRounds_iff_P hd hF

/-! ## Store determinism and infinite plays, every profile -/

/-- **Store determinism at a store with profile-free functions, every profile.** (Global
`StoreDet (instTripleS I P)` is not claimed: it quantifies over every store, including stores
whose functions read the profile.) -/
theorem storeDet_at {s s₁ s₂ : Store Nat} (hF : FuncsFree s.funcs) {a : I.F.Op}
    {c : List (Call I.E)} {b : Abstract.InstSession.Res I.exports ⊕ PUnit}
    (h₁ : (c, .ret b s₁) ∈ (instTripleS I P).1 s a) (h₂ : (c, .ret b s₂) ∈ (instTripleS I P).1 s a) :
    s₁ = s₂ :=
  Proofs.DanglingProfile.storeDet_at hF h₁ h₂

/-- **The infinite plays of the session, every profile**, from a store with profile-free
functions: a productive stream after completed rounds, or the play of a coherent infinite
sequence of rounds (`InstSession.mem_inf_instSession` at every profile). -/
theorem mem_inf_instSession_P {s₀ : Store Nat} (hF : FuncsFree s₀.funcs)
    {J : Set (List (Move I.E (Abstract.InstSession.ssig I.exports)))} :
    J ∈ (instSession I P s₀).inf ↔
      (∃ rs s a ω, StratThread.Rounds (instTripleS I P) s₀ rs s ∧
        ω ∈ (instTripleS I P).2.2 s a ∧
          J = StratThread.streamPlay (StratSession.sroundsMoves rs) a ω) ∨
      ∃ a r s, InfRounds (instTripleS I P) s₀ a r s ∧ J = StratSession.sroundsPlay a r :=
  Proofs.DanglingProfile.mem_inf_instSession_P hF

/-! ## Legal and throw-free host answers, every profile -/

theorem instTripleL_agree_P {s : Store Nat} (hd : InstDom I s) (hF : FuncsFree s.funcs)
    (a : I.F.Op) : AgreeAt (instTripleL I P) (cfgInstTripleL I) s a :=
  Proofs.DanglingProfile.instTripleL_agree_P hd hF a

theorem noThrowT_instTripleS_agree_P {s : Store Nat} (hd : InstDom I s) (hF : FuncsFree s.funcs)
    (a : I.F.Op) : AgreeAt (noThrowT I (instTripleS I P)) (cfgInstTriple I) s a :=
  Proofs.DanglingProfile.noThrowT_instTripleS_agree_P hd hF a

theorem threadS_instTripleL_eq_P {s₀ : Store Nat} (hd : InstDom I s₀) (hF : FuncsFree s₀.funcs) :
    StratSession.threadS (instTripleL I P) s₀ = StratSession.threadS (cfgInstTripleL I) s₀ :=
  Proofs.DanglingProfile.threadS_instTripleL_eq_P hd hF

theorem threadS_noThrowT_eq_P {s₀ : Store Nat} (hd : InstDom I s₀) (hF : FuncsFree s₀.funcs) :
    StratSession.threadS (noThrowT I (instTripleS I P)) s₀ =
      StratSession.threadS (cfgInstTriple I) s₀ :=
  Proofs.DanglingProfile.threadS_noThrowT_eq_P hd hF

/-! ## Component semantics, every profile -/

theorem core3SemD_sem_profile {m : NumInstance} (hF : FuncsFree m.inst.store.funcs) :
    (core3SemD P).sem m = (core3SemD P').sem m :=
  Proofs.DanglingProfile.core3SemD_sem_profile hF

theorem legalSemD_sem_profile {m : NumInstance} (hF : FuncsFree m.inst.store.funcs) :
    (legalSemD P).sem m = (legalSemD P').sem m :=
  Proofs.DanglingProfile.legalSemD_sem_profile hF

theorem denUD_core3SemD_profile (c : Comp NumInstance)
    (hc : CompIn (fun m : NumInstance => FuncsFree m.inst.store.funcs) c) :
    c.denUD (core3SemD P) = c.denUD (core3SemD P') :=
  Proofs.DanglingProfile.denUD_core3SemD_profile c hc

theorem denUD_legalSemD_profile (c : Comp NumInstance)
    (hc : CompIn (fun m : NumInstance => FuncsFree m.inst.store.funcs) c) :
    c.denUD (legalSemD P) = c.denUD (legalSemD P') :=
  Proofs.DanglingProfile.denUD_legalSemD_profile c hc

/-- **The CFG-built denotation is the Core 3.0 denotation at every profile**, on components whose
core instances are in the domain with profile-free functions. -/
theorem denUD_cfgSemD_eq_core3_P (c : Comp NumInstance)
    (hc : CompIn (fun m : NumInstance => InstDom m.inst m.inst.store) c)
    (hF : CompIn (fun m : NumInstance => FuncsFree m.inst.store.funcs) c) :
    c.denUD CfgLegal.cfgSemD = c.denUD (core3SemD P) :=
  Proofs.DanglingProfile.denUD_cfgSemD_eq_core3_P c hc hF

theorem denD_cfgSemD_eq_core3_P (c : Comp NumInstance)
    (hc : CompIn (fun m : NumInstance => InstDom m.inst m.inst.store) c)
    (hF : CompIn (fun m : NumInstance => FuncsFree m.inst.store.funcs) c) :
    c.denD CfgLegal.cfgSemD = c.denD (core3SemD P) :=
  Proofs.DanglingProfile.denD_cfgSemD_eq_core3_P c hc hF

/-! ## The backward simulations, every invariant, every profile -/

section Back

variable {H : Type} (J : Interp.BackInv H) {host : HostSemantics H} {tags : List TagInst}
  {s : Store H} {a : Nat} {vs : List Val}

/-- **Finished Core behaviours are session behaviours**, for every invariant and every profile,
on a store with profile-free functions and a host keeping them profile-free. -/
theorem coreBehSXP_mem_P (hHF : HostFree host) (hF : FuncsFree s.funcs) (hT : J.HostOk host)
    (hH : Interp.HostSliceT host) (hE : Interp.HostSliceE tags host) (hct : J.CT (invoke s a vs))
    (hS : Interp.StoreChkE (Interp.ehExt tags) s.funcs) (hts : Interp.TagsOk tags s)
    (hok : InvokeOk s a vs) {y : CallBeh (wasmHostSig H) (Store H) ((List Val ⊕ Nat) ⊕ PUnit)}
    (hy : CoreBehSXP P host s (a, vs) y) : y ∈ Abstract.wasmEvFunDXPS s (a, vs) :=
  Proofs.DanglingProfile.coreBehSXP_mem_P J hHF hF hT hH hE hct hS hts hok hy

/-- **Core callouts are pending session calls**, every invariant, every profile. -/
theorem coreCallout_mem_P (hHF : HostFree host) (hF : FuncsFree s.funcs) (hT : J.HostOk host)
    (hH : Interp.HostSliceT host) (hE : Interp.HostSliceE tags host) (hct : J.CT (invoke s a vs))
    (hS : Interp.StoreChkE (Interp.ehExt tags) s.funcs) (hts : Interp.TagsOk tags s)
    (hok : InvokeOk s a vs) {x : List (Call (wasmHostSig H)) × (wasmHostSig H).Op}
    (hx : CoreCallout P host s (a, vs) x) : x ∈ Abstract.wasmEvPendXPS s (a, vs) :=
  Proofs.DanglingProfile.coreCallout_mem_P J hHF hF hT hH hE hct hS hts hok hx

/-- **Productive Core runs are productive streams**, every invariant, every profile. -/
theorem coreInf_mem_P (hHF : HostFree host) (hF : FuncsFree s.funcs) (hT : J.HostOk host)
    (hH : Interp.HostSliceT host) (hE : Interp.HostSliceE tags host) (hct : J.CT (invoke s a vs))
    (hS : Interp.StoreChkE (Interp.ehExt tags) s.funcs) (hts : Interp.TagsOk tags s)
    (hok : InvokeOk s a vs) {ω : Nat → Call (wasmHostSig H)}
    (h : CoreInf P host (invoke s a vs) ω) : ω ∈ Abstract.wasmEvInfNXP s (a, vs) :=
  Proofs.DanglingProfile.coreInf_mem_P J hHF hF hT hH hE hct hS hts hok h

end Back

end Silmaril.Wasm.Cfg.DanglingProfile

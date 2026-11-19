module

public import Silmaril.Wasm.Cfg.ProfileFree.Defs
public import Silmaril.Wasm.Interp.CheckComplete.Defs
public import Silmaril.Wasm.Abstract.HostCall.Defs
public import Silmaril.Wasm.Abstract.HostSessionXP.Defs
public import Silmaril.Wasm.Abstract.HostSquareXP.Defs
public import Silmaril.Wasm.Abstract.NodeBridge.Defs
import Silmaril.Proofs.Wasm.Cfg.ProfileFree.Lift

@[expose] public section

/-!
# Profile-free Core code: theorems

Definitions in `Silmaril.Wasm.Cfg.ProfileFree.Defs`. The numeric profile `P` (`nd`, `relaxed`,
`nan`, `grow`) occurs in Core only in the premises of the float unary and binary operations,
the conversions, the vector operations and `memory.grow`/`table.grow` (`PSens`). Code without
them (`IFree`, `AFree`; type tests, references, aggregates, every call form, tail calls,
`throw`/`throw_ref`/`try_table`, labels, handlers and frames are all allowed) runs identically at
every profile.

* `step_profile`: a Core step of profile-free code at `P` is a step at every `P'` (any host);
* `step_free`: a Core step keeps profile-free code and functions, every profile, when host
  answers keep the functions profile-free (`HostFree`; store-preserving hosts do);
* `funcsFree_of_storeSupported`: the checker's instruction profile
  (`Interp.CheckComplete.StoreSupported`) is profile-free;
* runs, with the same witnesses: `hEvStep_profile`, `evRun_profile_iff`, `diverges_profile_iff`,
  `coreInf_profile_iff`;
* observations of an invocation on a store with profile-free functions:
  `coreObsLXP_profile_iff` (all `FullObs`), `coreBehSXP_profile_iff`, `coreCallout_profile_iff`,
  and the open Core triple `coreTripleSO_profile` (finished behaviours with their stores and logs,
  pending calls, productive streams).
-/

namespace Silmaril.Wasm.Cfg.ProfileFree

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract (wasmHostSig HEvStep EvRun CoreInf CoreObsLXP CoreBehSXP)
open Silmaril.Wasm.Abstract.NodeBridge (CoreCallout coreTripleSO)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P P' : Profile} {host : HostSemantics H}

/-! ## One step -/

/-- **Profile transfer of one step**: on profile-free code, a Core step at profile `P` is a step
at every profile `P'` (same host). -/
theorem step_profile {c c' : Config H} (h : Step P host c c') (hs : ∀ a ∈ c.code, AFree a) :
    Step P' host c c' :=
  Proofs.ProfileFree.step_profile h hs

/-- **One step keeps profile-free code and functions** (every profile), when host answers keep
the functions profile-free. -/
theorem step_free {c c' : Config H} (h : Step P host c c') (hH : HostFree host)
    (hF : FuncsFree c.store.funcs) (hs : ∀ a ∈ c.code, AFree a) :
    FuncsFree c'.store.funcs ∧ ∀ a ∈ c'.code, AFree a :=
  Proofs.ProfileFree.step_free h hH hF hs

/-- **Functions in the checker's instruction profile are profile-free.** -/
theorem funcsFree_of_storeSupported {F : List (FuncInst H)}
    (hsup : Interp.CheckComplete.StoreSupported F) : FuncsFree F :=
  Proofs.ProfileFree.funcsFree_of_storeSupported hsup

theorem hostFree_of_storePreserving (h : Abstract.NodeBridge.StorePreserving host) :
    HostFree host :=
  Proofs.ProfileFree.hostFree_of_storePreserving h

theorem configFree_invoke {s : Store H} (hF : FuncsFree s.funcs) (a : Nat) (vs : List Val) :
    ConfigFree (invoke s a vs) :=
  Proofs.ProfileFree.configFree_invoke hF a vs

/-! ## Runs -/

/-- **A labelled step of a profile-free configuration is one at every profile**, to a
profile-free configuration. -/
theorem hEvStep_profile (hH : HostFree host) {c c' : Config H} (hc : ConfigFree c)
    {l : Option (Call (wasmHostSig H))} (h : HEvStep P host c l c') :
    HEvStep P' host c l c' ∧ ConfigFree c' :=
  Proofs.ProfileFree.hEvStep_profile hH hc h

/-- **Labelled runs of profile-free configurations are profile-independent.** -/
theorem evRun_profile_iff (hH : HostFree host) {c c' : Config H} (hc : ConfigFree c)
    {cs : List (Call (wasmHostSig H))} : EvRun P host c cs c' ↔ EvRun P' host c cs c' :=
  Proofs.ProfileFree.evRun_profile_iff hH hc

/-- A labelled run of a profile-free configuration ends in a profile-free configuration. -/
theorem evRun_free (hH : HostFree host) {c c' : Config H} (hc : ConfigFree c)
    {cs : List (Call (wasmHostSig H))} (h : EvRun P host c cs c') : ConfigFree c' :=
  (Proofs.ProfileFree.evRun_profile (P' := P) hH hc h).2

/-- **Divergence of profile-free configurations is profile-independent** (the same trace). -/
theorem diverges_profile_iff (hH : HostFree host) {c : Config H} (hc : ConfigFree c) :
    Diverges P host c ↔ Diverges P' host c :=
  Proofs.ProfileFree.diverges_profile_iff hH hc

/-- **Productive runs of profile-free configurations are profile-independent** (the same
segmented run). -/
theorem coreInf_profile_iff (hH : HostFree host) {c : Config H} (hc : ConfigFree c)
    {ω : Nat → Call (wasmHostSig H)} : CoreInf P host c ω ↔ CoreInf P' host c ω :=
  Proofs.ProfileFree.coreInf_profile_iff hH hc

/-! ## Observations -/

variable {s : Store H}

/-- **Every Core observation with exceptions of an invocation on a store with profile-free
functions is profile-independent.** -/
theorem coreObsLXP_profile_iff (hH : HostFree host) (hF : FuncsFree s.funcs) (a : Nat)
    (vs : List Val) (o : Abstract.FullObs H) :
    CoreObsLXP P host s a vs o ↔ CoreObsLXP P' host s a vs o :=
  Proofs.ProfileFree.coreObsLXP_profile_iff hH hF a vs o

theorem coreBehSXP_profile_iff (hH : HostFree host) (hF : FuncsFree s.funcs)
    (q : Nat × List Val) (y : CallBeh (wasmHostSig H) (Store H) ((List Val ⊕ Nat) ⊕ PUnit)) :
    CoreBehSXP P host s q y ↔ CoreBehSXP P' host s q y :=
  Proofs.ProfileFree.coreBehSXP_profile_iff hH hF q y

theorem coreCallout_profile_iff (hH : HostFree host) (hF : FuncsFree s.funcs)
    (q : Nat × List Val) (x : List (Call (wasmHostSig H)) × (wasmHostSig H).Op) :
    CoreCallout P host s q x ↔ CoreCallout P' host s q x :=
  Proofs.ProfileFree.coreCallout_profile_iff hH hF q x

/-- **The open Core triple at a store with profile-free functions is profile-independent**:
finished behaviours (values, exceptions, traps with their stores, divergence after a log),
pending calls and productive streams. -/
theorem coreTripleSO_profile (hH : HostFree host) (hF : FuncsFree s.funcs) (q : Nat × List Val) :
    (coreTripleSO P host).1 s q = (coreTripleSO P' host).1 s q ∧
      (coreTripleSO P host).2.1 s q = (coreTripleSO P' host).2.1 s q ∧
      (coreTripleSO P host).2.2 s q = (coreTripleSO P' host).2.2 s q :=
  Proofs.ProfileFree.coreTripleSO_profile hH hF q

end Silmaril.Wasm.Cfg.ProfileFree

module

public import Silmaril.Wasm.Cfg.CfgInst.Defs
public import Silmaril.Wasm.Cfg.CfgClosure.Thms
public import Silmaril.Wasm.Abstract.NodeBridge.Thms
public import Silmaril.Wasm.Abstract.HostSessionXP.Thms
public import Silmaril.Wasm.Abstract.InstSession.Thms
public import Silmaril.Wasm.Interp.CheckComplete.Thms
import Silmaril.Proofs.Wasm.Cfg.CfgInst

@[expose] public section

/-!
# Instance sessions built from the self-contained CFG closure: theorems

Proofs in `Silmaril.Proofs.Wasm.Cfg.CfgInst`. Deterministic profile `profile o` throughout the
instance theorems; the CFG side (`cfgInstTriple`) does not depend on a profile.

**The explicit domain.** At a store `s`: `InstDom I s`, that is `I.WellFormed s` and
`StoreChkE (ehExt s.tags) s.funcs` (checker acceptance is a **hypothesis**, not derived from
validation), and **no thrown import answers**: the instance triple is restricted by `noThrowT`.
Exceptions raised inside Wasm code (caught, or escaping an export as an uncaught exception) are
kept.

**(a) Hosts.** `instHostNT I` is store-preserving, typed (`HostTyped`), in the native host slice
(`NativeHostSlice`) and keeps the checker's invariants for every tag list (`HostSliceE`), with no
hypothesis on `I`: the typing of its answers comes from `ImportTyped` at the callout store, which
is part of its definition. The universal host `instHost I` is **not** in the native slice as soon
as `I.E` has an operation (`not_nativeHostSlice_instHost`): it answers it by `Answer.throw`.

**(b) The square, per question** (any host with `hT`/`hH`/`hE`, on `InvOkXP tags s q`):
`coreTripleSO_agree_cfg`: the open Core triple `coreTripleSO (profile o) host` and the openly
restricted CFG session triple `openRestrict (coreHostRel host) cfgSessionTripleC` have the same
finished behaviours (values, exceptions, traps at their store, divergence), pending calls (every
reached callout) and productive streams at `(s, q)`.

**(c) Host transfer** (every profile, at a start store whose host functions are typed imports,
`ImportsTyped I s`; this persists along runs since host-free steps keep the functions and both
hosts keep the store): labelled runs, reached callouts, Core behaviours and productive runs at
`instHostNT I` are exactly those at `instHost I` whose events answer no exception
(`evRun_NT_iff`, `coreCallout_NT_iff`, `coreBehSXP_NT_iff`, `coreInf_NT_iff`); hence
`noThrowT_view_agree` on the viewed triples.

**(d) Main per-question theorem** (`noThrowT_instTripleS_agree`): on `InstDom I s`, the
throw-free instance triple `noThrowT I (instTripleS I (profile o))` and `cfgInstTriple I` agree at
`(s, a)` on all three components. The typed invocation `InvokeOk s (I.addr a.1) a.2.1` comes from
`export_type` and the typed scalar arguments (`invOkXP_of_dom`).

**(e) Sessions** (`threadS_noThrowT_eq`): from a store of the domain, the throw-free instance
session `threadS (noThrowT I (instTripleS I (profile o))) s₀` **is** `threadS (cfgInstTriple I) s₀`.
The domain holds at every store the throw-free session reaches (`instDom_of_reach`): a throw-free
round is a Core run at `instHostNT I`, which keeps the functions and tags of the store and, being
typed, keeps it well typed; so well-formedness and checker acceptance persist. Only the start
store is a hypothesis.

**(f) Without imports** (`instSession_eq_cfg`): no log can throw, so the instance session itself
is the CFG instance session on the domain; `core3SemD_eq_cfgInstSessions`:
`core3SemD (profile o) = threadSemSD (cfgInstSessions o)`, and `denUD_core3SemD_eq_cfgInstSessions`
for component denotations. `core3SemD` is unchanged: this is an equality, not a redefinition.
Instances without imports in the domain may raise, catch and leak exceptions (`ehExt`); unlike
`Cfg.Session`, no oracle is involved.

## What is not claimed

* **Instances with imports in `core3SemD`.** Their node session `instSession` also has the logs in
  which an import answers `Answer.throw t`. Those observations are excluded from the CFG reading:
  the native↔Core bridge needs hosts in the native slice. `cfgInstSessions` therefore falls back to
  the Core 3.0 session for instances with imports; for them the CFG equality is the throw-free
  session equality (e).
* **Checker acceptance** `StoreChkE (ehExt s.tags) s.funcs` is the hypothesis of `InstDom`. The
  `_of_supported` corollaries replace it by the explicit instruction-profile condition
  `StoreSupported s.funcs` (`Interp.CheckComplete.storeChkE_of_storeOk`, with `StoreOk` from
  well-formedness); `StoreSupported` persists along the throw-free session, whose rounds keep the
  store's functions (`funcs_of_reach`).
-/

namespace Silmaril.Wasm.Cfg.CfgInst

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract (wasmHostSig coreHostRel HostTyped EvRun CoreInf CoreBehSXP InvOkXP)
open Silmaril.Wasm.Abstract.NodeBridge (instHost StorePreserving viewTriple CoreCallout
  coreTripleSO qOf)
open Silmaril.Wasm.Abstract.InstSession (instTripleS instSession core3SemD threadSemSD)
open Silmaril.Wasm.Interp (NativeHostSlice HostSliceE)
open Silmaril.Wasm.Interp.CheckComplete (StoreSupported storeChkE_of_storeOk)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)
open Silmaril.Wasm.Component (Comp)
open Silmaril.Wasm.Component.Reference (NumInstance)
open Silmaril.Games.Abstract.StratThread (Reach)

variable {I : ScalarInstance}

/-! ## (a) Hosts -/

theorem storePreserving_instHostNT : StorePreserving (instHostNT I) :=
  Proofs.CfgInst.storePreserving_instHostNT

/-- The non-throwing universal host answers with typed results. -/
theorem hostTyped_instHostNT : HostTyped (instHostNT I) :=
  Proofs.CfgInst.hostTyped_instHostNT

/-- The non-throwing universal host is in the native host slice. -/
theorem nativeHostSlice_instHostNT : NativeHostSlice (instHostNT I) :=
  Proofs.CfgInst.nativeHostSlice_instHostNT

/-- The non-throwing universal host keeps the exception checker's invariants. -/
theorem hostSliceE_instHostNT (tags : List TagInst) : HostSliceE tags (instHostNT I) :=
  Proofs.CfgInst.hostSliceE_instHostNT tags

/-- **The obstruction**: when the import signature has an operation `e`, the universal host
answers it by an exception, so it is not in the native host slice. -/
theorem not_nativeHostSlice_instHost (e : I.E.Op) : ¬ NativeHostSlice (instHost I) :=
  Proofs.CfgInst.not_nativeHostSlice_instHost e

/-- A well-formed store's host functions are typed imports. -/
theorem importsTyped_of_wf {s : Store Nat} (hw : I.WellFormed s) : ImportsTyped I s :=
  Proofs.CfgInst.importsTyped_of_wf hw

/-! ## (b) The square, per question -/

section Square

variable {H : Type} {o : GrowOracle} {host : HostSemantics H} {tags : List TagInst}

/-- **The open Core triple is the openly host-restricted self-contained CFG session triple**, at
each question of `InvOkXP tags`. -/
theorem coreTripleSO_agree_cfg (hT : HostTyped host) (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {s : Store H} {q : Nat × List Val} (hok : InvOkXP tags s q) :
    AgreeAt (coreTripleSO (profile o) host)
      (openRestrict (coreHostRel host) CfgClosure.cfgSessionTripleC) s q :=
  Proofs.CfgInst.coreTripleSO_agree_cfg hT hH hE hok

end Square

/-! ## (c) Host transfer -/

section Transfer

variable {P : Numerics.Profile}

/-- **Runs at the non-throwing host are the throw-free runs at the universal host.** -/
theorem evRun_NT_iff {c c' : Config Nat} {cs : List (Call (wasmHostSig Nat))}
    (hI : ImportsTyped I c.store) :
    EvRun P (instHostNT I) c cs c' ↔ EvRun P (instHost I) c cs c' ∧ ∀ e ∈ cs, NoThrow e.2.2 :=
  Proofs.CfgInst.evRun_NT_iff hI

/-- **Productive runs at the non-throwing host are the throw-free productive runs.** -/
theorem coreInf_NT_iff {c : Config Nat} {ω : Nat → Call (wasmHostSig Nat)}
    (hI : ImportsTyped I c.store) :
    CoreInf P (instHostNT I) c ω ↔ CoreInf P (instHost I) c ω ∧ ∀ k, NoThrow (ω k).2.2 :=
  Proofs.CfgInst.coreInf_NT_iff hI

/-- **Reached callouts at the non-throwing host are those after throw-free logs.** -/
theorem coreCallout_NT_iff {s : Store Nat} {q : Nat × List Val}
    {x : List (Call (wasmHostSig Nat)) × (wasmHostSig Nat).Op} (hI : ImportsTyped I s) :
    CoreCallout P (instHostNT I) s q x ↔
      CoreCallout P (instHost I) s q x ∧ ∀ e ∈ x.1, NoThrow e.2.2 :=
  Proofs.CfgInst.coreCallout_NT_iff hI

/-- **Core behaviours at the non-throwing host are the throw-free ones.** -/
theorem coreBehSXP_NT_iff {s : Store Nat} {q : Nat × List Val}
    {y : CallBeh (wasmHostSig Nat) (Store Nat) ((List Val ⊕ Nat) ⊕ PUnit)}
    (hI : ImportsTyped I s) :
    CoreBehSXP P (instHostNT I) s q y ↔
      CoreBehSXP P (instHost I) s q y ∧ ∀ e ∈ y.1, NoThrow e.2.2 :=
  Proofs.CfgInst.coreBehSXP_NT_iff hI

/-- **The throw-free view of the universal host is the view of the non-throwing host.** -/
theorem noThrowT_view_agree {s : Store Nat} (hI : ImportsTyped I s) (a : I.F.Op) :
    AgreeAt (noThrowT I (viewTriple I (coreTripleSO P (instHost I))))
      (viewTriple I (coreTripleSO P (instHostNT I))) s a :=
  Proofs.CfgInst.noThrowT_view_agree hI a

end Transfer

/-! ## (d) The instance, per question -/

variable {o : GrowOracle}

/-- On the domain, every export question is a typed invocation with the checker's and tags'
invariants. -/
theorem invOkXP_of_dom {s : Store Nat} (hd : InstDom I s) (a : I.F.Op) :
    InvOkXP s.tags s (qOf I a) :=
  Proofs.CfgInst.invOkXP_of_dom hd a

/-- **The throw-free instance triple is the CFG instance triple**, at each export question of a
store of the domain: finished behaviours (values, exceptions, traps at their store, divergence),
pending import calls and productive import streams. -/
theorem noThrowT_instTripleS_agree {s : Store Nat} (hd : InstDom I s) (a : I.F.Op) :
    AgreeAt (noThrowT I (instTripleS I (profile o))) (cfgInstTriple I) s a :=
  Proofs.CfgInst.noThrowT_instTripleS_agree hd a

/-! ## (e) Sessions -/

/-- **The domain holds at every store the throw-free instance session reaches.** -/
theorem instDom_of_reach {P : Numerics.Profile} {s₀ s : Store Nat} (hd : InstDom I s₀)
    (hr : Reach (noThrowT I (instTripleS I P)) s₀ s) : InstDom I s :=
  Proofs.CfgInst.instDom_of_reach hd hr

/-- **The throw-free instance session is the session of the CFG instance triple**, from a store
of the domain. -/
theorem threadS_noThrowT_eq {s₀ : Store Nat} (hd : InstDom I s₀) :
    StratSession.threadS (noThrowT I (instTripleS I (profile o))) s₀ =
      StratSession.threadS (cfgInstTriple I) s₀ :=
  Proofs.CfgInst.threadS_noThrowT_eq hd

/-- **The throw-free session keeps the store's functions**, from a store of the domain. -/
theorem funcs_of_reach {P : Numerics.Profile} {s₀ s : Store Nat} (hd : InstDom I s₀)
    (hr : Reach (noThrowT I (instTripleS I P)) s₀ s) : s.funcs = s₀.funcs :=
  Proofs.CfgInst.funcs_of_reach hd hr

/-! ## The domain from the instruction profile -/

/-- **The domain from the instruction profile**: a well-formed store whose functions are in the
supported instruction profile passes the exception checker. -/
theorem instDom_of_supported {s : Store Nat} (hw : I.WellFormed s)
    (hsup : StoreSupported s.funcs) : InstDom I s :=
  ⟨hw, storeChkE_of_storeOk hw.storeOk hsup⟩

/-- **The instruction profile persists** along the throw-free session. -/
theorem supported_of_reach {P : Numerics.Profile} {s₀ s : Store Nat} (hw : I.WellFormed s₀)
    (hsup : StoreSupported s₀.funcs) (hr : Reach (noThrowT I (instTripleS I P)) s₀ s) :
    StoreSupported s.funcs := by
  rw [funcs_of_reach (instDom_of_supported hw hsup) hr]; exact hsup

/-- `noThrowT_instTripleS_agree` on well-formed stores in the instruction profile. -/
theorem noThrowT_instTripleS_agree_of_supported {s : Store Nat} (hw : I.WellFormed s)
    (hsup : StoreSupported s.funcs) (a : I.F.Op) :
    AgreeAt (noThrowT I (instTripleS I (profile o))) (cfgInstTriple I) s a :=
  noThrowT_instTripleS_agree (instDom_of_supported hw hsup) a

/-- `threadS_noThrowT_eq` on well-formed stores in the instruction profile. -/
theorem threadS_noThrowT_eq_of_supported {s₀ : Store Nat} (hw : I.WellFormed s₀)
    (hsup : StoreSupported s₀.funcs) :
    StratSession.threadS (noThrowT I (instTripleS I (profile o))) s₀ =
      StratSession.threadS (cfgInstTriple I) s₀ :=
  threadS_noThrowT_eq (instDom_of_supported hw hsup)

/-! ## (f) Without imports: the instance session and the component semantics -/

/-- Without imports the throw-free restriction is the identity. -/
theorem noThrowT_eq_of_nil (h : I.imports = []) {S A B : Type} (t : ObsTriple I.E S A B) :
    noThrowT I t = t :=
  Proofs.CfgInst.noThrowT_eq_of_nil h t

/-- **Without imports, the instance session is the CFG instance session**, from a store of the
domain. -/
theorem instSession_eq_cfg (h : I.imports = []) {s : Store Nat} (hd : InstDom I s) :
    instSession I (profile o) s = StratSession.threadS (cfgInstTriple I) s :=
  Proofs.CfgInst.instSession_eq_cfg h hd

/-- `instSession_eq_cfg` on well-formed stores in the instruction profile. -/
theorem instSession_eq_cfg_of_supported (h : I.imports = []) {s : Store Nat}
    (hw : I.WellFormed s) (hsup : StoreSupported s.funcs) :
    instSession I (profile o) s = StratSession.threadS (cfgInstTriple I) s :=
  instSession_eq_cfg h (instDom_of_supported hw hsup)

/-- **An instance without imports, well formed at its instantiation store and in the instruction
profile there, is interpreted by its CFG instance session** in `cfgInstSessions`. -/
theorem cfgInstSessions_of_supported {m : NumInstance} (h : m.inst.imports = [])
    (hw : m.inst.WellFormed m.inst.store) (hsup : StoreSupported m.inst.store.funcs) :
    cfgInstSessions o m = StratSession.threadS (cfgInstTriple m.inst) m.inst.store :=
  ite_eq_left ⟨h, instDom_of_supported hw hsup⟩

/-- **`core3SemD` through CFG instance sessions**: every numeric instance without imports and in
the domain at its instantiation store is interpreted by the session of its CFG instance triple;
the others keep their Core 3.0 instance sessions. -/
theorem core3SemD_eq_cfgInstSessions :
    core3SemD (profile o) = threadSemSD (cfgInstSessions o) :=
  Proofs.CfgInst.core3SemD_eq_cfgInstSessions

/-- **Component denotations through CFG instance sessions.** -/
theorem denUD_core3SemD_eq_cfgInstSessions (c : Comp NumInstance) :
    c.denUD (core3SemD (profile o)) = c.denUD (threadSemSD (cfgInstSessions o)) := by
  rw [core3SemD_eq_cfgInstSessions]

end Silmaril.Wasm.Cfg.CfgInst

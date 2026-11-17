module

public import Silmaril.Wasm.Cfg.CfgInst.Defs
public import Silmaril.Wasm.Cfg.CfgClosure.Thms
public import Silmaril.Wasm.Cfg.SessionCheck.Thms
public import Silmaril.Wasm.Abstract.NodeBridge.Thms
public import Silmaril.Wasm.Abstract.HostSessionXP.Thms
public import Silmaril.Wasm.Abstract.InstSession.Thms
public import Silmaril.Wasm.Interp.CheckComplete.Thms
import Silmaril.Proofs.Wasm.Cfg.CfgInst

@[expose] public section

/-!
# Instance sessions built from the self-contained CFG closure: theorems

Proofs in `Silmaril.Proofs.Wasm.Cfg.CfgInst`. Deterministic profile `profile o` throughout the
instance theorems; the CFG side (`cfgInstTripleL`, `cfgInstTriple`) does not depend on a profile.

**The explicit domain.** At a store `s`: `InstDom I s`, that is `I.WellFormed s` and
`StoreChkE (ehExt s.tags) s.funcs` (checker acceptance is a **hypothesis**, not derived from
validation; the `_of_supported` corollaries derive it from `StoreSupported s.funcs`), and
**legal host exceptions**: an import answering `Answer.throw a` names an exception of the store
at that call, `a < s.exns.length` (`LegalRes`, i.e. `Answer.ThrowsBelow s.exns.length`, the
legality of `IsInstance.adequacy`). The instance triple is restricted to it by `instTripleL`.
Exceptions raised inside Wasm code (caught, or escaping an export) and legal host exceptions
(caught by a `try_table` or escaping) are all kept.

**(a) Hosts.** The restricted universal hosts `instHostQ I Q` are store-preserving, in the typed
host slice (`HostSliceT`, via `HostSliceT.of_funcs_eq`) and keep the checker's invariants
(`HostSliceE`), for every `Q`. The legal host `instHostL I` is typed (`hostTyped_instHostL`):
its thrown addresses exist at the callout store. The non-throwing host `instHostNT I` is its
special case, also in the native slice. Neither needs a hypothesis on `I`: the typing of answers
comes from `ImportTyped` at the callout store, part of the definition. The unrestricted typed host
`instHostU I` is **not** typed (`not_hostTyped_instHostU`), and the universal host is not in the
native slice (`not_nativeHostSlice_instHost`).

**(b) The square, per question** (any host with `hT`/`hH`/`hE`, on `InvOkXP tags s q`):
`coreTripleSO_agree_cfg`.

**(c) Host transfer** (every profile, at a store whose host functions are typed imports):
`legalT_coreTripleSO_agree`: restricting the open Core triple of `instHost I` to legal host
events (`legalT`) gives the open Core triple of `instHostL I`; `noThrowT_view_agree` likewise for
throw-free logs.

**(d) Main per-question theorem** (`instTripleL_agree`): on `InstDom I s`, the instance triple with
legal host exceptions `instTripleL I (profile o)` and `cfgInstTripleL I` agree at `(s, a)`:
finished behaviours (values, exceptions, traps keeping their store, divergence), pending import
calls and productive import streams. `instTripleL` is contained in `instTripleS`
(`instTripleL_sub`), contains its throw-free part (`noThrowT_sub_instTripleL`), and is all of it
without imports (`instTripleL_eq_of_nil`). The throw-free statement `noThrowT_instTripleS_agree`
(against `cfgInstTriple`) is kept.

**(e) Sessions** (`threadS_instTripleL_eq`): from a store of the domain, the legal instance session
`threadS (instTripleL I (profile o)) s₀` **is** `threadS (cfgInstTripleL I) s₀`. The domain holds
at every store the legal session reaches (`instDom_of_reachL`): a legal round is a Core run at
`instHostL I`, which keeps the functions and tags (Wasm `throw` only appends exception instances,
the host keeps the store), and, being typed, keeps the configuration typed (Core preservation
`Abstract.Step.preservation_typed`, through caught host exceptions and the exception references
they leave), so `StoreOk` at the round's end store holds. Only the start store is a hypothesis.

**(f) Session families, without fallback.** `cfgInstSessionsL m` is the session of
`cfgInstTripleL m.inst` at `m.inst.store`, for **every** numeric instance.
* `legalSemD_sem_eq`, `denUD_legalSemD_eq_cfgInstSessionsL`: the legal Core 3.0 semantics
  `legalSemD (profile o)` interprets every instance in the domain at its instantiation store
  (`InstDom m.inst m.inst.store`) as `cfgInstSessionsL`, and so a component all of whose core
  instances are in the domain (`SessionCheck.CompIn`) has the same denotation under both.
* `core3SemD_sem_eq_cfgInstSessionsL`, `denUD_core3SemD_eq_cfgInstSessionsL`: the same for
  `core3SemD (profile o)` itself on the instances **without imports** in the domain.

## What is not claimed: dangling host exceptions

`core3SemD` interprets an instance with imports by `instSession`, which also has the logs in
which an import answers `Answer.throw a` with `a ≥ s.exns.length` at the call store `s`. Those are
outside `instTripleL`, and no CFG reading of them is claimed. Native and Core agree on the
operations involved (Core `CatchMatches` and the native `Cfg.Region.Catches` both read
`s.exns[a]?`; a dangling address fails tagged clauses, and `catch_all(_ref)` catches it), but the
proved bridge does not cover them: its backward simulation (`HostClosingXP.back_all`) carries
`Sim.ContextTyped` (a `ConfigOk` of the plugged configuration) across every Core step by
`ContextTyped.steps_typed hT`, which needs `HostTyped host`, and `ConfigOk` types `ref.exn a` only
by `RefOk.exn (h : s.exns[a]? = some e)`. After a dangling host throw the Core configuration
`throwing a` is not typed. Precisely, the instance-level hypothesis that fails is
`HostTyped (instHostU I)` (`not_hostTyped_instHostU`: the answer `.throw s.exns.length` needs
`∃ e, s.exns[s.exns.length]? = some e`). Padding the store with exceptions does not repair this:
a later Wasm `throw` allocates at `s.exns.length`, so a dangling address can come to name a fresh
exception, and padding would change which one. Closing the gap needs a bridge whose invariant
types exception references without existence; it is not attempted here, and `core3SemD` is not
claimed equal to a CFG semantics for instances with imports.
-/

namespace Silmaril.Wasm.Cfg.CfgInst

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract (wasmHostSig coreHostRel HostTyped EvRun CoreInf CoreBehSXP InvOkXP)
open Silmaril.Wasm.Abstract.NodeBridge (instHost StorePreserving viewTriple CoreCallout
  coreTripleSO qOf)
open Silmaril.Wasm.Abstract.InstSession (instTripleS instSession core3SemD threadSemSD semOfSD)
open Silmaril.Wasm.Interp (NativeHostSlice HostSliceT HostSliceE)
open Silmaril.Wasm.Interp.CheckComplete (StoreSupported storeChkE_of_storeOk)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)
open Silmaril.Wasm.Component (Comp)
open Silmaril.Wasm.Component.Reference (NumInstance)
open Silmaril.Wasm.Cfg.SessionCheck (CompIn denUD_congrIn)
open Silmaril.Games.Abstract.StratThread (Reach)

variable {I : ScalarInstance}

/-! ## (a) Hosts -/

theorem storePreserving_instHostL : StorePreserving (instHostL I) :=
  Proofs.CfgInst.storePreserving_instHostL

theorem storePreserving_instHostNT : StorePreserving (instHostNT I) :=
  Proofs.CfgInst.storePreserving_instHostNT

/-- **The legal universal host answers with typed results**: its exceptions exist. -/
theorem hostTyped_instHostL : HostTyped (instHostL I) :=
  Proofs.CfgInst.hostTyped_instHostL

/-- The non-throwing universal host answers with typed results. -/
theorem hostTyped_instHostNT : HostTyped (instHostNT I) :=
  Proofs.CfgInst.hostTyped_instHostNT

/-- **Every restricted universal host is in the typed host slice**, whatever it throws. -/
theorem hostSliceT_instHostQ {Q : Store Nat → Result → Prop} : HostSliceT (instHostQ I Q) :=
  Proofs.CfgInst.hostSliceT_instHostQ

/-- The legal universal host is in the typed host slice. -/
theorem hostSliceT_instHostL : HostSliceT (instHostL I) :=
  Proofs.CfgInst.hostSliceT_instHostL

/-- The non-throwing universal host is in the native host slice. -/
theorem nativeHostSlice_instHostNT : NativeHostSlice (instHostNT I) :=
  Proofs.CfgInst.nativeHostSlice_instHostNT

/-- The legal universal host keeps the exception checker's invariants. -/
theorem hostSliceE_instHostL (tags : List TagInst) : HostSliceE tags (instHostL I) :=
  Proofs.CfgInst.hostSliceE_instHostL tags

/-- The non-throwing universal host keeps the exception checker's invariants. -/
theorem hostSliceE_instHostNT (tags : List TagInst) : HostSliceE tags (instHostNT I) :=
  Proofs.CfgInst.hostSliceE_instHostNT tags

/-- On import answers, legality at `s` is `Answer.ThrowsBelow s.exns.length`. -/
theorem legalRes_toResult_iff {s : Store Nat} {ft : FnType} (v : Answer ft) :
    LegalRes s v.toResult ↔ v.ThrowsBelow s.exns.length :=
  Proofs.CfgInst.legalRes_toResult_iff v

/-- **The obstruction for dangling exceptions**: at a typed callout `e` of a store with `StoreOk`,
the unrestricted typed host answers `throw s.exns.length`, so it is not typed. -/
theorem not_hostTyped_instHostU {s : Store Nat} (hs : StoreOk s) (e : I.E.Op)
    {fi : FuncInst Nat} (hfi : fi ∈ s.funcs) (hcode : fi.code = .host e.1.1)
    (hIT : ImportTyped I s e.1.1) : ¬ HostTyped (instHostU I) :=
  Proofs.CfgInst.not_hostTyped_instHostU hs e hfi hcode hIT

/-- **The old obstruction**: when the import signature has an operation `e`, the universal host
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
theorem coreTripleSO_agree_cfg (hT : HostTyped host) (hH : HostSliceT host)
    (hE : HostSliceE tags host) {s : Store H} {q : Nat × List Val} (hok : InvOkXP tags s q) :
    AgreeAt (coreTripleSO (profile o) host)
      (openRestrict (coreHostRel host) CfgClosure.cfgSessionTripleC) s q :=
  Proofs.CfgInst.coreTripleSO_agree_cfg hT hH hE hok

end Square

/-! ## (c) Host transfer -/

section Transfer

variable {P : Numerics.Profile}

/-- **The legal restriction of the universal host's open Core triple is the legal host's open
Core triple**, at a store whose host functions are typed imports. -/
theorem legalT_coreTripleSO_agree {s : Store Nat} (hI : ImportsTyped I s) (q : Nat × List Val) :
    AgreeAt (legalT (coreTripleSO P (instHost I))) (coreTripleSO P (instHostL I)) s q :=
  Proofs.CfgInst.legalT_coreTripleSO_agree hI q

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

/-- **The instance triple with legal host exceptions is the legal CFG instance triple**, at each
export question of a store of the domain: finished behaviours (values, exceptions, traps at
their store, divergence), pending import calls and productive import streams. -/
theorem instTripleL_agree {s : Store Nat} (hd : InstDom I s) (a : I.F.Op) :
    AgreeAt (instTripleL I (profile o)) (cfgInstTripleL I) s a :=
  Proofs.CfgInst.instTripleL_agree hd a

/-- **The throw-free instance triple is the throw-free CFG instance triple**, on the domain. -/
theorem noThrowT_instTripleS_agree {s : Store Nat} (hd : InstDom I s) (a : I.F.Op) :
    AgreeAt (noThrowT I (instTripleS I (profile o))) (cfgInstTriple I) s a :=
  Proofs.CfgInst.noThrowT_instTripleS_agree hd a

/-- The legal instance triple is a restriction of the instance triple. -/
theorem instTripleL_sub {P : Numerics.Profile} (s : Store Nat) (a : I.F.Op) :
    (instTripleL I P).1 s a ⊆ (instTripleS I P).1 s a ∧
      (instTripleL I P).2.1 s a ⊆ (instTripleS I P).2.1 s a ∧
      (instTripleL I P).2.2 s a ⊆ (instTripleS I P).2.2 s a :=
  Proofs.CfgInst.instTripleL_sub s a

/-- The throw-free instance triple is contained in the legal one. -/
theorem noThrowT_sub_instTripleL {P : Numerics.Profile} (s : Store Nat) (a : I.F.Op) :
    (noThrowT I (instTripleS I P)).1 s a ⊆ (instTripleL I P).1 s a ∧
      (noThrowT I (instTripleS I P)).2.1 s a ⊆ (instTripleL I P).2.1 s a ∧
      (noThrowT I (instTripleS I P)).2.2 s a ⊆ (instTripleL I P).2.2 s a :=
  Proofs.CfgInst.noThrowT_sub_instTripleL s a

/-- Without imports the legal instance triple is the instance triple. -/
theorem instTripleL_eq_of_nil (h : I.imports = []) (P : Numerics.Profile) :
    instTripleL I P = instTripleS I P :=
  Proofs.CfgInst.instTripleL_eq_of_nil h P

/-! ## (e) Sessions -/

/-- **The domain holds at every store the legal instance session reaches.** -/
theorem instDom_of_reachL {P : Numerics.Profile} {s₀ s : Store Nat} (hd : InstDom I s₀)
    (hr : Reach (instTripleL I P) s₀ s) : InstDom I s :=
  Proofs.CfgInst.instDom_of_reachL hd hr

/-- **The legal session keeps the store's functions**, from a store of the domain. -/
theorem funcs_of_reachL {P : Numerics.Profile} {s₀ s : Store Nat} (hd : InstDom I s₀)
    (hr : Reach (instTripleL I P) s₀ s) : s.funcs = s₀.funcs :=
  Proofs.CfgInst.funcs_of_reachL hd hr

/-- **The legal instance session is the session of the legal CFG instance triple**, from a store
of the domain. -/
theorem threadS_instTripleL_eq {s₀ : Store Nat} (hd : InstDom I s₀) :
    StratSession.threadS (instTripleL I (profile o)) s₀ =
      StratSession.threadS (cfgInstTripleL I) s₀ :=
  Proofs.CfgInst.threadS_instTripleL_eq hd

/-- **The domain holds at every store the throw-free instance session reaches.** -/
theorem instDom_of_reach {P : Numerics.Profile} {s₀ s : Store Nat} (hd : InstDom I s₀)
    (hr : Reach (noThrowT I (instTripleS I P)) s₀ s) : InstDom I s :=
  Proofs.CfgInst.instDom_of_reach hd hr

/-- **The throw-free session keeps the store's functions**, from a store of the domain. -/
theorem funcs_of_reach {P : Numerics.Profile} {s₀ s : Store Nat} (hd : InstDom I s₀)
    (hr : Reach (noThrowT I (instTripleS I P)) s₀ s) : s.funcs = s₀.funcs :=
  Proofs.CfgInst.funcs_of_reach hd hr

/-- **The throw-free instance session is the session of the throw-free CFG instance triple**,
from a store of the domain. -/
theorem threadS_noThrowT_eq {s₀ : Store Nat} (hd : InstDom I s₀) :
    StratSession.threadS (noThrowT I (instTripleS I (profile o))) s₀ =
      StratSession.threadS (cfgInstTriple I) s₀ :=
  Proofs.CfgInst.threadS_noThrowT_eq hd

/-! ## The domain from the instruction profile -/

/-- **The domain from the instruction profile**: a well-formed store whose functions are in the
supported instruction profile passes the exception checker. -/
theorem instDom_of_supported {s : Store Nat} (hw : I.WellFormed s)
    (hsup : StoreSupported s.funcs) : InstDom I s :=
  ⟨hw, storeChkE_of_storeOk hw.storeOk hsup⟩

/-- **The instruction profile persists** along the legal session. -/
theorem supported_of_reachL {P : Numerics.Profile} {s₀ s : Store Nat} (hw : I.WellFormed s₀)
    (hsup : StoreSupported s₀.funcs) (hr : Reach (instTripleL I P) s₀ s) :
    StoreSupported s.funcs := by
  rw [funcs_of_reachL (instDom_of_supported hw hsup) hr]; exact hsup

/-- **The instruction profile persists** along the throw-free session. -/
theorem supported_of_reach {P : Numerics.Profile} {s₀ s : Store Nat} (hw : I.WellFormed s₀)
    (hsup : StoreSupported s₀.funcs) (hr : Reach (noThrowT I (instTripleS I P)) s₀ s) :
    StoreSupported s.funcs := by
  rw [funcs_of_reach (instDom_of_supported hw hsup) hr]; exact hsup

/-- `instTripleL_agree` on well-formed stores in the instruction profile. -/
theorem instTripleL_agree_of_supported {s : Store Nat} (hw : I.WellFormed s)
    (hsup : StoreSupported s.funcs) (a : I.F.Op) :
    AgreeAt (instTripleL I (profile o)) (cfgInstTripleL I) s a :=
  instTripleL_agree (instDom_of_supported hw hsup) a

/-- `threadS_instTripleL_eq` on well-formed stores in the instruction profile. -/
theorem threadS_instTripleL_eq_of_supported {s₀ : Store Nat} (hw : I.WellFormed s₀)
    (hsup : StoreSupported s₀.funcs) :
    StratSession.threadS (instTripleL I (profile o)) s₀ =
      StratSession.threadS (cfgInstTripleL I) s₀ :=
  threadS_instTripleL_eq (instDom_of_supported hw hsup)

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

/-! ## (f) Session families, without fallback -/

/-- **The legal Core 3.0 semantics interprets an instance of the domain by its CFG instance
session.** -/
theorem legalSemD_sem_eq {m : NumInstance} (hm : InstDom m.inst m.inst.store) :
    (legalSemD (profile o)).sem m = (threadSemSD cfgInstSessionsL).sem m :=
  congrArg (semOfSD m) (threadS_instTripleL_eq hm)

/-- **Component denotations under the legal semantics through CFG instance sessions**: for a
component all of whose core instances are in the domain at their instantiation stores. -/
theorem denUD_legalSemD_eq_cfgInstSessionsL (c : Comp NumInstance)
    (hc : CompIn (fun m : NumInstance => InstDom m.inst m.inst.store) c) :
    c.denUD (legalSemD (profile o)) = c.denUD (threadSemSD cfgInstSessionsL) :=
  denUD_congrIn (fun _ hm => legalSemD_sem_eq hm) c hc

/-- Without imports the throw-free restriction is the identity. -/
theorem noThrowT_eq_of_nil (h : I.imports = []) {S A B : Type} (t : ObsTriple I.E S A B) :
    noThrowT I t = t :=
  Proofs.CfgInst.noThrowT_eq_of_nil h t

/-- **Without imports, the instance session is the legal CFG instance session**, from a store of
the domain. -/
theorem instSession_eq_cfgL (h : I.imports = []) {s : Store Nat} (hd : InstDom I s) :
    instSession I (profile o) s = StratSession.threadS (cfgInstTripleL I) s :=
  Proofs.CfgInst.instSession_eq_cfgL h hd

/-- **Without imports, the instance session is the throw-free CFG instance session**, from a
store of the domain. -/
theorem instSession_eq_cfg (h : I.imports = []) {s : Store Nat} (hd : InstDom I s) :
    instSession I (profile o) s = StratSession.threadS (cfgInstTriple I) s :=
  Proofs.CfgInst.instSession_eq_cfg h hd

/-- **Core 3.0 interprets an instance without imports in the domain by its CFG instance
session.** -/
theorem core3SemD_sem_eq_cfgInstSessionsL {m : NumInstance} (h : m.inst.imports = [])
    (hm : InstDom m.inst m.inst.store) :
    (core3SemD (profile o)).sem m = (threadSemSD cfgInstSessionsL).sem m :=
  congrArg (semOfSD m) (instSession_eq_cfgL h hm)

/-- **Component denotations under Core 3.0 through CFG instance sessions**: for a component all
of whose core instances have no imports and are in the domain at their instantiation stores. -/
theorem denUD_core3SemD_eq_cfgInstSessionsL (c : Comp NumInstance)
    (hc : CompIn (fun m : NumInstance => m.inst.imports = [] ∧ InstDom m.inst m.inst.store) c) :
    c.denUD (core3SemD (profile o)) = c.denUD (threadSemSD cfgInstSessionsL) :=
  denUD_congrIn (fun _ hm => core3SemD_sem_eq_cfgInstSessionsL hm.1 hm.2) c hc

end Silmaril.Wasm.Cfg.CfgInst

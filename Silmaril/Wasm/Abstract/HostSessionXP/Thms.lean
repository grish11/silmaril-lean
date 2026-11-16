module

public import Silmaril.Wasm.Abstract.HostSessionXP.Defs
public import Silmaril.Wasm.Abstract.HostClosingS.Thms
public import Silmaril.Wasm.Abstract.OpenStrat.Thms
public import Silmaril.Wasm.Abstract.HostClosingInfXPBack.Thms
public import Silmaril.Wasm.Abstract.CoreDet.Thms
import Silmaril.Proofs.Wasm.Abstract.HostSessionXP.Basic

/-!
# Sessions of invocations with exceptions against a host: theorems

**Erasure.** Forgetting the stores of traps (`StratSession.eraseTrap`) sends the session triples
to the per-round triples of `HostStratXP`:

* `eraseTrap_natTripleSXP`: the native session triple erases to
  `obsTriple Ok (NatObsXP host …)`, the triple of `natStratXP host Ok`
  (`toDStrat_eraseTrap_natTripleSXP`);
* `eraseTrap_coreTripleSXP`: the Core session triple erases to `obsTriple Ok (CoreObsLXP …)`, the
  triple of `coreStratXP P host Ok` (`toDStrat_eraseTrap_coreTripleSXP`);
* neither has a plain trap (`noPlainTrap_natTripleSXP`, `noPlainTrap_coreTripleSXP`).

**The session square** (deterministic profile `profile o`, a host with typed answers in the
native host slice whose answers keep the exception checker's store check and the tag invariants,
on the questions `InvOkXP tags`):

* `natTripleSXP_eq_coreTripleSXP`: the native session triple is the Core session triple. Off
  traps a behaviour is read back from its erasure (no plain traps on either side), and the
  erasures agree by the exact-log square (`hostSquareXP`, through `obsTriple_eq_of_square`):
  values, exceptions, divergence, pending calls and productive streams. A store-keeping trap is
  exactly a Core run to a trap in exactly its store (`wasmEvFunXPS_trap_iff`). No saturation is
  needed: the equality is of triples, before `toDStrat`;
* per question: `natTripleSXP_mem_iff` (finished behaviours, trap stores included),
  `natTripleSXP_pend_iff` (pending calls), `natTripleSXP_inf_iff` (productive streams), all as
  Core runs;
* `natSessionXP_eq_coreSessionXP`: **the native session is the Core session** from every store
  `s₀`, as strategies;
* plays of the native session read as Core runs: a trap round then a value round
  (`natSessionXP_mem_trap_ret`), divergence after completed rounds (`natSessionXP_mem_div`), and
  a productive current round (`natSessionXP_mem_inf`).

**Coherence.** The native session triple is deterministic given answers (`natTripleSXP_det`,
from `CoreDet.coreTripleSXP_det`), hence store-deterministic; native sessions identify exactly
the observationally equivalent stores (`natSessionXP_eq_iff`), and their infinite plays are
coherent (`natSessionXP_mem_inf_iff`): a productive stream after completed rounds, or the play of
a coherent infinite sequence of session rounds.

Proofs in `Silmaril.Proofs.Wasm.Abstract.HostSessionXP`.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Execution.Core
open Silmaril.Games.Abstract.StratSession (eraseTrap NoPlainTrap)

variable {H : Type}

/-! ## Erasure -/

/-- **The native session triple erases to the native triple with exceptions.** -/
theorem eraseTrap_natTripleSXP (host : HostSemantics H) (Ok : Store H → Nat × List Val → Prop) :
    eraseTrap (natTripleSXP host Ok) = obsTriple Ok (fun s q => NatObsXP host s q.1 q.2) :=
  Silmaril.Proofs.Wasm.Abstract.HostSessionXP.eraseTrap_natTripleSXP host Ok

/-- **The Core session triple with exceptions erases to the Core triple with exceptions.** -/
theorem eraseTrap_coreTripleSXP (P : Numerics.Profile) (host : HostSemantics H)
    (Ok : Store H → Nat × List Val → Prop) :
    eraseTrap (coreTripleSXP P host Ok) = obsTriple Ok (fun s q => CoreObsLXP P host s q.1 q.2) :=
  Silmaril.Proofs.Wasm.Abstract.HostSessionXP.eraseTrap_coreTripleSXP P host Ok

/-- The play object of the erased native session triple is the native strategy with
exceptions. -/
theorem toDStrat_eraseTrap_natTripleSXP (host : HostSemantics H)
    (Ok : Store H → Nat × List Val → Prop) :
    StratObs.toDStrat (eraseTrap (natTripleSXP host Ok)) = natStratXP host Ok :=
  congrArg StratObs.toDStrat (eraseTrap_natTripleSXP host Ok)

/-- The play object of the erased Core session triple is the Core strategy with exceptions. -/
theorem toDStrat_eraseTrap_coreTripleSXP (P : Numerics.Profile) (host : HostSemantics H)
    (Ok : Store H → Nat × List Val → Prop) :
    StratObs.toDStrat (eraseTrap (coreTripleSXP P host Ok)) = coreStratXP P host Ok :=
  congrArg StratObs.toDStrat (eraseTrap_coreTripleSXP P host Ok)

/-- The native session triple has no plain trap. -/
theorem noPlainTrap_natTripleSXP (host : HostSemantics H)
    (Ok : Store H → Nat × List Val → Prop) : NoPlainTrap (natTripleSXP host Ok) :=
  Silmaril.Proofs.Wasm.Abstract.HostSessionXP.noPlainTrap_natTripleSXP host Ok

/-- The Core session triple with exceptions has no plain trap. -/
theorem noPlainTrap_coreTripleSXP (P : Numerics.Profile) (host : HostSemantics H)
    (Ok : Store H → Nat × List Val → Prop) : NoPlainTrap (coreTripleSXP P host Ok) :=
  fun _ _ _ h => h.2

/-- **A store-keeping trap of the native session triple** is one of the session closure, at a
question `Ok`, with a log the host allows. -/
theorem natTripleSXP_trap_iff {host : HostSemantics H} {Ok : Store H → Nat × List Val → Prop}
    {s s₂ : Store H} {q : Nat × List Val} {cs : List (Call (wasmHostSig H))} :
    (cs, .ret (.inr PUnit.unit) s₂) ∈ (natTripleSXP host Ok).1 s q ↔
      Ok s q ∧ (cs, .ret (.inr PUnit.unit) s₂) ∈ wasmEvFunXPS s q ∧
        (coreHostRel host).Consistent cs :=
  Silmaril.Proofs.Wasm.Abstract.HostSessionXP.natTripleSXP_trap_iff

/-! ## The session square -/

section Square

open Silmaril.Wasm.Interp (NativeHostSlice HostSliceE)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

variable {o : GrowOracle} {host : HostSemantics H} {tags : List TagInst}

/-- **The session square at the triple level** (deterministic profile): the native session
triple against `host` is the store-retaining Core triple with exceptions, on `InvOkXP tags`. -/
theorem natTripleSXP_eq_coreTripleSXP (hT : HostTyped host) (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) :
    natTripleSXP host (InvOkXP tags) = coreTripleSXP (profile o) host (InvOkXP tags) :=
  Silmaril.Proofs.Wasm.Abstract.HostSessionXP.natTripleSXP_eq_coreTripleSXP hT hH hE

/-- **Finished native session behaviours are Core behaviours**, per question: values and
exceptions at their store, a trap at exactly its store, host-free divergence. -/
theorem natTripleSXP_mem_iff (hT : HostTyped host) (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {s : Store H} {q : Nat × List Val}
    {x : CallBeh (wasmHostSig H) (Store H) ((List Val ⊕ Nat) ⊕ PUnit)} :
    x ∈ (natTripleSXP host (InvOkXP tags)).1 s q ↔
      InvOkXP tags s q ∧ CoreBehSXP (profile o) host s q x := by
  rw [natTripleSXP_eq_coreTripleSXP (o := o) hT hH hE]; rfl

/-- **Pending native session calls are pending Core callouts**, per question. -/
theorem natTripleSXP_pend_iff (hT : HostTyped host) (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {s : Store H} {q : Nat × List Val}
    {x : List (Call (wasmHostSig H)) × (wasmHostSig H).Op} :
    x ∈ (natTripleSXP host (InvOkXP tags)).2.1 s q ↔ InvOkXP tags s q ∧
      (CoreObsLXP (profile o) host s q.1 q.2 (.blocked x.1 x.2) ∨
        CoreObsLXP (profile o) host s q.1 q.2 (.hostDiv x.1 x.2)) := by
  rw [natTripleSXP_eq_coreTripleSXP (o := o) hT hH hE]; rfl

/-- **Productive native session streams are productive Core runs**, per question. -/
theorem natTripleSXP_inf_iff (hT : HostTyped host) (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {s : Store H} {q : Nat × List Val}
    {ω : Nat → Call (wasmHostSig H)} :
    ω ∈ (natTripleSXP host (InvOkXP tags)).2.2 s q ↔
      InvOkXP tags s q ∧ CoreInf (profile o) host (invoke s q.1 q.2) ω := by
  rw [natTripleSXP_eq_coreTripleSXP (o := o) hT hH hE]; rfl

/-- **The session square at the strategy level** (deterministic profile): from every store, the
native session with exceptions against `host` is the Core session. -/
theorem natSessionXP_eq_coreSessionXP (hT : HostTyped host) (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) (s₀ : Store H) :
    natSessionXP host (InvOkXP tags) s₀ = coreSessionXP (profile o) host (InvOkXP tags) s₀ :=
  congrArg (StratSession.threadS · s₀) (natTripleSXP_eq_coreTripleSXP hT hH hE)

/-- **The native session continues after a trap, as Core does**: a round trapping at `q` then a
round returning `ws` at `q'` is a play from `s₀` iff `q` runs in Core to a trap configuration in
some store `s₁`, and `q'` runs from `s₁` to `ws`. -/
theorem natSessionXP_mem_trap_ret (hT : HostTyped host) (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {s₀ : Store H} {q q' : Nat × List Val}
    {c₁ c₂ : List (Call (wasmHostSig H))} {ws : List Val} :
    StratSession.sroundMoves (q, c₁, .inr PUnit.unit) ++
        StratSession.sroundMoves (q', c₂, .inl (.inl ws)) ∈
        (natSessionXP host (InvOkXP tags) s₀).toStrategy ↔
      ∃ s₁, (InvOkXP tags s₀ q ∧ EvRun (profile o) host (invoke s₀ q.1 q.2) c₁ ⟨s₁, {}, [.trap]⟩) ∧
        ∃ s₂, InvOkXP tags s₁ q' ∧
          EvRun (profile o) host (invoke s₁ q'.1 q'.2) c₂ ⟨s₂, {}, vals ws⟩ := by
  rw [natSessionXP_eq_coreSessionXP (o := o) hT hH hE]; exact StratSession.mem_trap_ret

/-- **A divergent play of the native session** after completed rounds ending at `s` is a Core
run of `q` from `s`, at exactly the log `c`, followed by host-free divergence. -/
theorem natSessionXP_mem_div (hT : HostTyped host) (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {s₀ : Store H}
    {rs : List ((Nat × List Val) × List (Call (wasmHostSig H)) × ((List Val ⊕ Nat) ⊕ PUnit))}
    {q : Nat × List Val} {c : List (Call (wasmHostSig H))} :
    StratSession.sroundsMoves rs ++ .inr (.ask q) :: StratObs.callMoves c ∈
        (natSessionXP host (InvOkXP tags) s₀).div ↔
      ∃ s, StratThread.Rounds (natTripleSXP host (InvOkXP tags)) s₀ rs s ∧ InvOkXP tags s q ∧
        ∃ c' : Config H, EvRun (profile o) host (invoke s q.1 q.2) c c' ∧
          Diverges (profile o) (fun _ _ _ _ => False) c' := by
  rw [natSessionXP, natTripleSXP_eq_coreTripleSXP (o := o) hT hH hE]; exact StratSession.mem_div

/-- **An infinite play of the current round of the native session** after completed rounds
ending at `s` is a productive Core run of `q` from `s`. -/
theorem natSessionXP_mem_inf (hT : HostTyped host) (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {s₀ : Store H}
    {rs : List ((Nat × List Val) × List (Call (wasmHostSig H)) × ((List Val ⊕ Nat) ⊕ PUnit))}
    {q : Nat × List Val} {ω : Nat → Call (wasmHostSig H)} :
    StratThread.streamPlay (StratSession.sroundsMoves rs) q ω ∈
        (natSessionXP host (InvOkXP tags) s₀).inf ↔
      ∃ s, StratThread.Rounds (natTripleSXP host (InvOkXP tags)) s₀ rs s ∧ InvOkXP tags s q ∧
        CoreInf (profile o) host (invoke s q.1 q.2) ω := by
  rw [natSessionXP, natTripleSXP_eq_coreTripleSXP (o := o) hT hH hE]; exact StratSession.mem_inf

/-! ## Coherence -/

/-- **The native session triple is deterministic given answers**: it does not depend on a
profile, and it is the Core session triple at any deterministic profile. -/
theorem natTripleSXP_det (hT : HostTyped host) (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) : AFun.Det (natTripleSXP host (InvOkXP tags)).1 :=
  natTripleSXP_eq_coreTripleSXP (o := SingleThreaded.neverFail) hT hH hE ▸
    CoreDet.coreTripleSXP_det hT fun _ _ h => ⟨h.1, h.2.2.2⟩

/-- **The native session triple is store-deterministic.** -/
theorem natTripleSXP_storeDet (hT : HostTyped host) (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) : StratThread.StoreDet (natTripleSXP host (InvOkXP tags)) :=
  StratThread.storeDet_of_det (natTripleSXP_det hT hH hE)

/-- **Native sessions identify exactly the observationally equivalent stores.** -/
theorem natSessionXP_eq_iff (hT : HostTyped host) (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {s s' : Store H} :
    natSessionXP host (InvOkXP tags) s = natSessionXP host (InvOkXP tags) s' ↔
      StratThread.ObsEq (natTripleSXP host (InvOkXP tags)) (natTripleSXP host (InvOkXP tags))
        s s' :=
  StratSession.threadS_eq_iff (natTripleSXP_storeDet hT hH hE)
    (natTripleSXP_storeDet hT hH hE) (noPlainTrap_natTripleSXP _ _)
    (noPlainTrap_natTripleSXP _ _)

/-- **Native sessions have coherent infinite plays** (deterministic profile): a productive stream
after completed session rounds, or the play of a coherent infinite sequence of session rounds,
each starting at the store the previous one left. -/
theorem natSessionXP_mem_inf_iff (hT : HostTyped host) (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {s₀ : Store H}
    {I : Set (List (Move (wasmHostSig H) (sig1 (Nat × List Val) (List Val ⊕ Nat))))} :
    I ∈ (natSessionXP host (InvOkXP tags) s₀).inf ↔
      (∃ rs s q ω, StratThread.Rounds (natTripleSXP host (InvOkXP tags)) s₀ rs s ∧
        ω ∈ (natTripleSXP host (InvOkXP tags)).2.2 s q ∧
        I = StratThread.streamPlay (StratSession.sroundsMoves rs) q ω) ∨
      ∃ a r s, StratThread.InfRounds (natTripleSXP host (InvOkXP tags)) s₀ a r s ∧
        I = StratSession.sroundsPlay a r :=
  StratSession.mem_inf_iff_of_det (natTripleSXP_det hT hH hE)

end Square

end Silmaril.Wasm.Abstract

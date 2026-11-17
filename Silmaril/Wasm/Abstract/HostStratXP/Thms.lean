module

public import Silmaril.Wasm.Abstract.HostStratXP.Defs
public import Silmaril.Wasm.Abstract.HostStrat.Thms
public import Silmaril.Wasm.Abstract.HostSquareXP.Thms

/-!
# Invocations with exceptions against a host as canonical strategies: theorems

* `obsTriple_eq_of_square`: the native and Core triples agree when the square holds on `InvOkXP`;
* `coreStratXP_eq_natStratXP_of`, `coreStratAtXP_eq_natStratAtXP_of` (deterministic profile):
  **the Core strategy with exceptions is the native one**, given the two backward directions of
  `hostSquareXP_of` (`hdiv`: host-free Core divergence after a log is a divergent canonical
  behaviour; `hinf`: a productive Core run is a productive canonical run) for every question of
  `InvOkXP`. Both are proved in `HostClosingInfXPBack` (`backDivXP`, `backInfXP`), with the
  unconditional `coreStratXP_eq_natStratXP` and `coreStratAtXP_eq_natStratAtXP` there;
* `coreStratXP_mem_throw`, `coreStratXP_mem_ret`: reading Core runs back from completed rounds,
  every profile: an answer `.inl (.inr t, s₂)` is a Core run to the uncaught exception
  `throwing t`, an answer `.inl (.inl ws, s₂)` to the values `ws`.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Interp (HostSliceT HostSliceE TagsOk StoreChkE ehExt)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

variable {H : Type} {o : GrowOracle} {host : HostSemantics H} {tags : List TagInst}

/-- The backward divergence direction, on every question of `InvOkXP tags`. -/
def BackDivXP (o : GrowOracle) (host : HostSemantics H) (tags : List TagInst) : Prop :=
  ∀ s q, InvOkXP tags s q → ∀ (cs : List (Call (wasmHostSig H))) (c' : Config H),
    EvRun (profile o) host (invoke s q.1 q.2) cs c' →
    Diverges (profile o) (fun _ _ _ _ => False) c' → (cs, .div) ∈ wasmEvFunDXP s q

/-- The backward productive direction, on every question of `InvOkXP tags`. -/
def BackInfXP (o : GrowOracle) (host : HostSemantics H) (tags : List TagInst) : Prop :=
  ∀ s q, InvOkXP tags s q → ∀ ω : Nat → Call (wasmHostSig H),
    CoreInf (profile o) host (invoke s q.1 q.2) ω → ω ∈ wasmEvInfNXP s q

/-- The native and Core triples with exceptions agree on `InvOkXP`, given the backward
directions. -/
theorem obsTriple_eq_of_square (hT : HostTyped host) (hH : HostSliceT host)
    (hE : HostSliceE tags host) (hdiv : BackDivXP o host tags) (hinf : BackInfXP o host tags) :
    obsTriple (InvOkXP tags) (fun s q => CoreObsLXP (profile o) host s q.1 q.2) =
      obsTriple (InvOkXP tags) (fun s q => NatObsXP host s q.1 q.2) :=
  obsTriple_congr fun s q hq x => (hostSquareXP_of hT hH hE hq.1 hq.2.1 hq.2.2.1 hq.2.2.2
    (hdiv s q hq) (hinf s q hq) x).symm

/-- **The Core strategy with exceptions is the native one** (deterministic profile), given the
backward directions. -/
theorem coreStratXP_eq_natStratXP_of (hT : HostTyped host) (hH : HostSliceT host)
    (hE : HostSliceE tags host) (hdiv : BackDivXP o host tags) (hinf : BackInfXP o host tags) :
    coreStratXP (profile o) host (InvOkXP tags) = natStratXP host (InvOkXP tags) :=
  congrArg StratObs.toDStrat (obsTriple_eq_of_square hT hH hE hdiv hinf)

/-- **Per function**, final store hidden, given the backward directions. -/
theorem coreStratAtXP_eq_natStratAtXP_of (hT : HostTyped host) (hH : HostSliceT host)
    (hE : HostSliceE tags host) (hdiv : BackDivXP o host tags) (hinf : BackInfXP o host tags)
    (s : Store H) (a : Nat) :
    coreStratAtXP (profile o) host (InvOkXP tags) s a = natStratAtXP host (InvOkXP tags) s a :=
  congrArg (fun t => StratObs.toDStrat (atTriple t s a)) (obsTriple_eq_of_square hT hH hE hdiv hinf)

variable {P : Numerics.Profile} {Ok : Store H → Nat × List Val → Prop}

/-- **A completed round answering an exception** is a Core run to the uncaught exception. -/
theorem coreStratXP_mem_throw (s : Store H) (q : Nat × List Val)
    (cs : List (Call (wasmHostSig H))) (t : Nat) (s₂ : Store H) :
    (.inr (.ask (s, q)) :: (StratObs.callMoves cs ++ [.inr (.ans (s, q) (.inl (.inr t, s₂)))]) :
        List (Move (wasmHostSig H) (funSig (Store H) (Nat × List Val) (List Val ⊕ Nat)))) ∈
        (coreStratXP P host Ok).toStrategy ↔
      Ok s q ∧ EvRun P host (invoke s q.1 q.2) cs ⟨s₂, {}, throwing t⟩ :=
  (StratObs.mem_ret s q cs _ s₂).trans (by simp [obsTriple, CoreObsLXP])

/-- **A completed round with values** is a Core run to those values in the empty frame. -/
theorem coreStratXP_mem_ret (s : Store H) (q : Nat × List Val)
    (cs : List (Call (wasmHostSig H))) (ws : List Val) (s₂ : Store H) :
    (.inr (.ask (s, q)) :: (StratObs.callMoves cs ++ [.inr (.ans (s, q) (.inl (.inl ws, s₂)))]) :
        List (Move (wasmHostSig H) (funSig (Store H) (Nat × List Val) (List Val ⊕ Nat)))) ∈
        (coreStratXP P host Ok).toStrategy ↔
      Ok s q ∧ EvRun P host (invoke s q.1 q.2) cs ⟨s₂, {}, vals ws⟩ :=
  (StratObs.mem_ret s q cs _ s₂).trans (by simp [obsTriple, CoreObsLXP])

end Silmaril.Wasm.Abstract

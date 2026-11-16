module

public import Silmaril.Wasm.Abstract.HostStrat.Defs
public import Silmaril.Wasm.Abstract.HostSquare.Thms
public import Silmaril.Games.Abstract.StratObs.Thms
import Silmaril.Proofs.Wasm.Abstract.HostStrat.Basic

/-!
# Invocations against a host as canonical strategies: theorems

* `coreStrat_eq_natStrat` (deterministic profile `profile o`, checked typed invocations) and
  `coreStrat_eq_natStrat_profile` (every profile, native-profile Wasm functions and a host
  satisfying `Interp.HostNative`): **the Core strategy is the native strategy**. This is the
  exact-log square `hostSquare` read in the canonical play object. Logs are exact, pending host
  calls stay, and productive host interaction is an infinite play (never `End.div`);
* `coreStrat_profile`: the Core strategy on `InvOkN` is the same at every profile;
* reading Core runs back from the plays: a completed round with values is a Core run to those
  values in the empty frame (`coreStrat_mem_ret`); a trap round is a Core run to a trap in some
  store (`coreStrat_mem_trap`, the store is erased); a divergent play is a Core run followed by
  host-free divergence (`coreStrat_mem_div`); a one-round infinite play is a productive Core run
  (`coreStrat_mem_inf`). A completed round that answers a thrown tag (`.inr t`) is never a Core
  play (`coreStrat_not_mem_throw`): Core 3.0 has no finished end for an uncaught exception.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Execution.Core

variable {H : Type} {host : HostSemantics H}

/-- Observation families that agree on the questions `Ok` give the same triple. -/
theorem obsTriple_congr {Ok : Store H → Nat × List Val → Prop}
    {O O' : Store H → Nat × List Val → FullObs H → Prop}
    (h : ∀ s q, Ok s q → ∀ x, O s q x ↔ O' s q x) : obsTriple Ok O = obsTriple Ok O' :=
  Silmaril.Proofs.Wasm.Abstract.HostStrat.obsTriple_congr h

/-- **The Core strategy is the native strategy** at the deterministic profile `profile o`, for
checked typed invocations and a host with typed answers in the native host slice. -/
theorem coreStrat_eq_natStrat {o : SingleThreaded.GrowOracle} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) :
    coreStrat (SingleThreaded.profile o) host InvOk = natStrat host InvOk :=
  congrArg StratObs.toDStrat <| obsTriple_congr fun _ _ ⟨hs, hS, hok⟩ x =>
    (hostSquare hT hH hs hS hok x).symm

/-- **The Core strategy is the native strategy at every profile**, for checked typed
invocations of stores with native-profile Wasm functions and a host with typed answers in the
native host slice satisfying `Interp.HostNative`. -/
theorem coreStrat_eq_natStrat_profile {P : Numerics.Profile} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) (hN : Interp.HostNative host) :
    coreStrat P host InvOkN = natStrat host InvOkN :=
  congrArg StratObs.toDStrat <| obsTriple_congr fun _ _ ⟨⟨hs, hS, hok⟩, hW⟩ x =>
    (hostSquare_profile hT hH hN hs hS hW hok x).symm

/-- The Core strategy on `InvOkN` does not depend on the profile. -/
theorem coreStrat_profile {P P' : Numerics.Profile} (hN : Interp.HostNative host) :
    coreStrat P host InvOkN = coreStrat P' host InvOkN :=
  congrArg StratObs.toDStrat <| obsTriple_congr fun _ _ ⟨_, hW⟩ x => coreObsL_profile hN hW x

variable {P : Numerics.Profile} {Ok : Store H → Nat × List Val → Prop}

/-- **A completed round with values** is a Core run to those values in the empty frame. -/
theorem coreStrat_mem_ret (s : Store H) (q : Nat × List Val) (cs : List (Call (wasmHostSig H)))
    (ws : List Val) (s₂ : Store H) :
    (.inr (.ask (s, q)) :: (StratObs.callMoves cs ++ [.inr (.ans (s, q) (.inl (.inl ws, s₂)))]) :
        List (Move (wasmHostSig H) (funSig (Store H) (Nat × List Val) (List Val ⊕ Nat)))) ∈
        (coreStrat P host Ok).toStrategy ↔
      Ok s q ∧ EvRun P host (invoke s q.1 q.2) cs ⟨s₂, {}, vals ws⟩ :=
  (StratObs.mem_ret s q cs _ s₂).trans (by simp [obsTriple, CoreObsL])

/-- A completed round answering a thrown tag is never a Core play. -/
theorem coreStrat_not_mem_throw (s : Store H) (q : Nat × List Val)
    (cs : List (Call (wasmHostSig H))) (t : Nat) (s₂ : Store H) :
    (.inr (.ask (s, q)) :: (StratObs.callMoves cs ++ [.inr (.ans (s, q) (.inl (.inr t, s₂)))]) :
        List (Move (wasmHostSig H) (funSig (Store H) (Nat × List Val) (List Val ⊕ Nat)))) ∉
        (coreStrat P host Ok).toStrategy :=
  fun h => by simpa [obsTriple, CoreObsL] using (StratObs.mem_ret s q cs _ s₂).1 h

/-- **A trap round** is a Core run to a trap, in some store (`End.trap` carries none). -/
theorem coreStrat_mem_trap (s : Store H) (q : Nat × List Val)
    (cs : List (Call (wasmHostSig H))) :
    (.inr (.ask (s, q)) :: (StratObs.callMoves cs ++ [.inr (.ans (s, q) (.inr PUnit.unit))]) :
        List (Move (wasmHostSig H) (funSig (Store H) (Nat × List Val) (List Val ⊕ Nat)))) ∈
        (coreStrat P host Ok).toStrategy ↔
      Ok s q ∧ ∃ s₂, EvRun P host (invoke s q.1 q.2) cs ⟨s₂, {}, [.trap]⟩ :=
  (StratObs.mem_trap s q cs).trans (by simp [obsTriple, CoreObsL])

/-- **A divergent play** is a Core run, at exactly its log, followed by host-free divergence. -/
theorem coreStrat_mem_div (s : Store H) (q : Nat × List Val)
    (cs : List (Call (wasmHostSig H))) :
    (.inr (.ask (s, q)) :: StratObs.callMoves cs :
        List (Move (wasmHostSig H) (funSig (Store H) (Nat × List Val) (List Val ⊕ Nat)))) ∈
        (coreStrat P host Ok).div ↔
      Ok s q ∧ ∃ c' : Config H, EvRun P host (invoke s q.1 q.2) cs c' ∧
        Diverges P (fun _ _ _ _ => False) c' :=
  (StratObs.mem_div (s, q) cs).trans (by simp [obsTriple, CoreObsL])

/-- **A one-round infinite play** is a productive Core run: infinitely many answered host
calls, with exactly the stream as log. -/
theorem coreStrat_mem_inf (s : Store H) (q : Nat × List Val) (ω : Nat → Call (wasmHostSig H)) :
    StratObs.streamPlay [] (s, q) ω ∈ (coreStrat P host Ok).inf ↔
      Ok s q ∧ CoreInf P host (invoke s q.1 q.2) ω :=
  (StratObs.mem_inf (s, q) ω).trans (by simp [obsTriple, CoreObsL])

/-! ## Per-function strategies -/

/-- **The Core strategy of a function is its native strategy** at `profile o`. -/
theorem coreStratAt_eq_natStratAt {o : SingleThreaded.GrowOracle} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) (s : Store H) (a : Nat) :
    coreStratAt (SingleThreaded.profile o) host InvOk s a = natStratAt host InvOk s a :=
  congrArg (fun t => StratObs.toDStrat (atTriple t s a)) <| obsTriple_congr
    fun _ _ ⟨hs, hS, hok⟩ x => (hostSquare hT hH hs hS hok x).symm

/-- **The Core strategy of a function is its native strategy at every profile**, under
`InvOkN` and `Interp.HostNative`. -/
theorem coreStratAt_eq_natStratAt_profile (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) (hN : Interp.HostNative host) (s : Store H) (a : Nat) :
    coreStratAt P host InvOkN s a = natStratAt host InvOkN s a :=
  congrArg (fun t => StratObs.toDStrat (atTriple t s a)) <| obsTriple_congr
    fun _ _ ⟨⟨hs, hS, hok⟩, hW⟩ x => (hostSquare_profile hT hH hN hs hS hW hok x).symm

/-- **A completed round with values**, final store hidden: a Core run of the function to those
values in some store. -/
theorem coreStratAt_mem_ret (s : Store H) (a : Nat) (vs : List Val)
    (cs : List (Call (wasmHostSig H))) (ws : List Val) :
    (.inr (.ask ((), vs)) :: (StratObs.callMoves cs ++ [.inr (.ans ((), vs) (.inl (.inl ws, ())))]) :
        List (Move (wasmHostSig H) (funSig Unit (List Val) (List Val ⊕ Nat)))) ∈
        (coreStratAt P host Ok s a).toStrategy ↔
      Ok s (a, vs) ∧ ∃ s₂, EvRun P host (invoke s a vs) cs ⟨s₂, {}, vals ws⟩ :=
  Silmaril.Proofs.Wasm.Abstract.HostStrat.coreStratAt_mem_ret s a vs cs ws

/-- **A trap round**, final store hidden: a Core run of the function to a trap. -/
theorem coreStratAt_mem_trap (s : Store H) (a : Nat) (vs : List Val)
    (cs : List (Call (wasmHostSig H))) :
    (.inr (.ask ((), vs)) :: (StratObs.callMoves cs ++ [.inr (.ans ((), vs) (.inr PUnit.unit))]) :
        List (Move (wasmHostSig H) (funSig Unit (List Val) (List Val ⊕ Nat)))) ∈
        (coreStratAt P host Ok s a).toStrategy ↔
      Ok s (a, vs) ∧ ∃ s₂, EvRun P host (invoke s a vs) cs ⟨s₂, {}, [.trap]⟩ :=
  Silmaril.Proofs.Wasm.Abstract.HostStrat.coreStratAt_mem_trap s a vs cs

/-- **A one-round infinite play** of the function is a productive Core run. -/
theorem coreStratAt_mem_inf (s : Store H) (a : Nat) (vs : List Val)
    (ω : Nat → Call (wasmHostSig H)) :
    StratObs.streamPlay [] ((), vs) ω ∈ (coreStratAt P host Ok s a).inf ↔
      Ok s (a, vs) ∧ CoreInf P host (invoke s a vs) ω :=
  (StratObs.mem_inf ((), vs) ω).trans (by simp [atTriple, obsTriple, CoreObsL])

end Silmaril.Wasm.Abstract

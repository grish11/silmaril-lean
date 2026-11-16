module

public import Silmaril.Wasm.Abstract.HostStrat.Defs
public import Silmaril.Wasm.Abstract.HostSquare.Thms
public import Silmaril.Games.Abstract.StratObs.Thms
public import Silmaril.Games.Abstract.StratSession.Thms
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
* sessions: erasing the trap stores of the store-retaining Core triple gives the Core triple
  (`eraseTrap_coreTripleS`); it has no plain traps (`noPlainTrap_coreTripleS`); and in the Core
  session a trap round followed by a value round is a Core run to a trap leaving `s₁`, then a
  Core run from `s₁` to the values (`coreSession_mem_trap_ret`). After completed session rounds
  ending at `s`: a pending Core callout (blocked or host-divergent) from `s` is a play ending in
  that call (`coreSession_pending_mem`); a divergent play is a Core run from `s` followed by
  host-free divergence (`coreSession_mem_div`); a stream play is a productive Core run from `s`
  (`coreSession_mem_inf`).
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

/-! ## Sessions -/

/-- **Erasing the trap stores of the store-retaining Core triple gives the Core triple.** -/
theorem eraseTrap_coreTripleS :
    StratSession.eraseTrap (coreTripleS P host Ok) =
      obsTriple Ok (fun s q => CoreObsL P host s q.1 q.2) :=
  Silmaril.Proofs.Wasm.Abstract.HostStrat.eraseTrap_coreTripleS

/-- The store-retaining Core triple has no plain traps. -/
theorem noPlainTrap_coreTripleS : StratSession.NoPlainTrap (coreTripleS P host Ok) :=
  fun _ _ _ h => h.2

/-- **The Core session continues after a trap**: a round trapping at `q` then a round returning
the values `ws` at `q'` is a play from `s₀` iff `q` runs (with the host calls `c₁`) to a trap
configuration in some store `s₁`, and `q'` runs from `s₁` (with the host calls `c₂`) to `ws`. -/
theorem coreSession_mem_trap_ret {s₀ : Store H} {q q' : Nat × List Val}
    {c₁ c₂ : List (Call (wasmHostSig H))} {ws : List Val} :
    StratSession.sroundMoves (q, c₁, .inr PUnit.unit) ++
        StratSession.sroundMoves (q', c₂, .inl (.inl ws)) ∈ (coreSession P host Ok s₀).toStrategy ↔
      ∃ s₁, (Ok s₀ q ∧ EvRun P host (invoke s₀ q.1 q.2) c₁ ⟨s₁, {}, [.trap]⟩) ∧
        ∃ s₂, Ok s₁ q' ∧ EvRun P host (invoke s₁ q'.1 q'.2) c₂ ⟨s₂, {}, vals ws⟩ :=
  StratSession.mem_trap_ret

/-- **A pending Core callout after session rounds is a play**: after completed session rounds
`rs` (continuing traps included) ending at `s`, a Core run of `q` from `s` with the host calls
`c` to a callout `m` that the host does not answer, or diverges on, is a play ending in the call
`m`. -/
theorem coreSession_pending_mem {s₀ s : Store H}
    {rs : List ((Nat × List Val) × List (Call (wasmHostSig H)) × ((List Val ⊕ Nat) ⊕ PUnit))}
    {q : Nat × List Val} {c : List (Call (wasmHostSig H))} {m : (wasmHostSig H).Op}
    (hrs : StratThread.Rounds (coreTripleS P host Ok) s₀ rs s) (hq : Ok s q)
    (h : CoreObsL P host s q.1 q.2 (.blocked c m) ∨ CoreObsL P host s q.1 q.2 (.hostDiv c m)) :
    StratSession.sroundsMoves rs ++ .inr (.ask q) :: (StratObs.callMoves c ++ [.inl (.ask m)]) ∈
      (coreSession P host Ok s₀).toStrategy :=
  StratSession.mem_pending.2 ⟨s, hrs, .inl ⟨hq, h⟩⟩

/-- **A divergent play of the Core session** after completed session rounds ending at `s` is a
Core run of `q` from `s`, at exactly the log `c`, followed by host-free divergence. -/
theorem coreSession_mem_div {s₀ : Store H}
    {rs : List ((Nat × List Val) × List (Call (wasmHostSig H)) × ((List Val ⊕ Nat) ⊕ PUnit))}
    {q : Nat × List Val} {c : List (Call (wasmHostSig H))} :
    StratSession.sroundsMoves rs ++ .inr (.ask q) :: StratObs.callMoves c ∈
        (coreSession P host Ok s₀).div ↔
      ∃ s, StratThread.Rounds (coreTripleS P host Ok) s₀ rs s ∧ Ok s q ∧
        ∃ c' : Config H, EvRun P host (invoke s q.1 q.2) c c' ∧
          Diverges P (fun _ _ _ _ => False) c' :=
  StratSession.mem_div

/-- **An infinite play of the current round of the Core session** after completed session
rounds ending at `s` is a productive Core run of `q` from `s`, with exactly the stream as log. -/
theorem coreSession_mem_inf {s₀ : Store H}
    {rs : List ((Nat × List Val) × List (Call (wasmHostSig H)) × ((List Val ⊕ Nat) ⊕ PUnit))}
    {q : Nat × List Val} {ω : Nat → Call (wasmHostSig H)} :
    StratThread.streamPlay (StratSession.sroundsMoves rs) q ω ∈ (coreSession P host Ok s₀).inf ↔
      ∃ s, StratThread.Rounds (coreTripleS P host Ok) s₀ rs s ∧ Ok s q ∧
        CoreInf P host (invoke s q.1 q.2) ω :=
  StratSession.mem_inf

end Silmaril.Wasm.Abstract

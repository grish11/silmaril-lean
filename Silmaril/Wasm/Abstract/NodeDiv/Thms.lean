module

public import Silmaril.Wasm.Abstract.NodeDiv.Defs
public import Silmaril.Wasm.Abstract.InstSessionD.Thms
public import Silmaril.Wasm.Abstract.InstSession.Thms
public import Silmaril.Games.Abstract.StratSession.Thms
public import Silmaril.Wasm.Component.DWiringLaws.Thms
import Silmaril.Proofs.Wasm.Abstract.NodeDiv.Basic

/-!
# The own divergences and productive streams of a Core 3.0 core module

`Silmaril.Wasm.Abstract.InstSessionD` interprets a numeric Core 3.0 instance `m` by its session
`instSession m.inst P m.inst.store`, read back on `ifaceSig` (`spullD`) between the coercions
`importH` (below) and `exportH` (above): `(core3SemD P).sem m = semOfSD m (instSession …)`. This
module computes what that strategy does **by itself**, on Core runs, every profile `P`, no typing
hypothesis.

**The session read back** (`I : ScalarInstance`, from any store `s`):

* `mem_div_spullD_instSession`: a play `p` diverges iff it is an instance path from `.idle s` to
  a running state `.running a u t` from which the thread runs host-free forever
  (`InstStrat.Diverges P (u, t)`). This is the `.div` of `instFinS` (host-free divergence after
  the round's import log), after completed rounds, read back from the session interface along
  `srelabel` (`StratSession.mem_div_iff`). The prefix may contain trapped rounds: the session
  continues after a trap.
* `mem_inf_spullD_instSession_stream`: after an instance play `p₀`, the question `a` and the
  import calls `ω 0, ω 1, …` forever are an infinite play iff `p₀` ends idle at a store from
  which `ω` is a productive stream of `a` (`InstStrat.instInf`). The plays are the chain
  `stream p₀ a ω`.
* `instInf_of_calls`, `calls_of_instInf`: a productive stream is the same as a running state in
  the middle of the round (after the calls `cs`) from which the instance makes import calls
  forever, the stream being `cs` then those calls (`prependStream`). This is the shape of the
  importer's side of `Linked2.Chatter`.

**The coercions add no divergence.** `importH` answers every question by exactly one call
(`allCall_importH`), and a handler that always calls has no silent chatter with the strategy
above it (`not_silentChatter_of_allCall`); `exportH` makes at most one call
(`oneCall_exportH`), so there is no chatter below it (`DStrategy.div_comp_ofHandler`). Hence:

* `div_semOfSD`: the divergences of `semOfSD m σ` are those of `spullD σ`, through `importH`
  and `exportH`;
* `div_core3SemD_sem`: **the divergences of a Core 3.0 module** under `core3SemD P` are the
  instance paths from its instantiation store to a host-free divergent running state, through
  `importH` and `exportH`.

These are the node-level halves of the linked divergences of #730: `Linked2.DivB` is
`InstStrat.Diverges` (by definition), reached after a path of the importer's instance;
`Linked2.DivA` is the same for the exporter's instance, reached through B's import call; the
importer's side of `Linked2.Chatter` is a productive stream of B's instance.

**Not claimed here.** The core node `dcoreNode` adds `implsN` below these strategies; its silent
chatter (`div_dcoreNode`) is excluded only when `implsN` is trap-silent and the strategy above
propagates traps, which this module does not prove. The read-back of the linked component's
divergences (`Linked2.linkDiv`) to `Linked2.RoundDiv` is not done here.

Proofs: `Silmaril.Proofs.Wasm.Abstract.NodeDiv.Basic`.
-/

public section

namespace Silmaril.Wasm.Abstract.NodeDiv

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
open Silmaril.Wasm.Game Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Abstract.InstSession
open Silmaril.Wasm.Abstract.InstStrat (Diverges instInf)
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Numerics (Profile)

/-! ## The session read back -/

section Session

variable {I : ScalarInstance} {P : Profile}

/-- **The divergences of the read-back instance session**: the instance paths from `.idle s` to a
running state that diverges host-free. -/
theorem mem_div_spullD_instSession {s : Store Nat} {p : List (Move I.E I.F)} :
    p ∈ (spullD (instSession I P s)).div ↔
      ∃ a u t, I.Path P (.idle s) p (.running a u t) ∧ Diverges P (u, t) :=
  Silmaril.Proofs.Wasm.Abstract.NodeDiv.mem_div_spullD_instSession

/-- **The productive stream of the current round**: after the instance play `p₀`, the question
`a` and the import calls `ω` forever are an infinite play of the read-back session iff `p₀` ends
idle at a store from which `ω` is a productive stream of `a`. -/
theorem mem_inf_spullD_instSession_stream {s : Store Nat} {p₀ : List (Move I.E I.F)}
    {a : I.F.Op} {ω : ℕ → Call I.E} :
    (stream p₀ a ω).lim ∈ (spullD (instSession I P s)).inf ↔
      ∃ s₁, I.Path P (.idle s) p₀ (.idle s₁) ∧ ω ∈ instInf I P s₁ a :=
  Silmaril.Proofs.Wasm.Abstract.NodeDiv.mem_inf_spullD_instSession_stream

/-- Instance paths compose. -/
theorem path_append {x y z : I.HState} {p q : List (Move I.E I.F)} (h₁ : I.Path P x p y)
    (h₂ : I.Path P y q z) : I.Path P x (p ++ q) z :=
  Silmaril.Proofs.Wasm.Abstract.NodeDiv.path_append h₁ h₂

/-- **Import calls forever, in the middle of a round, are a productive stream of the round**:
after the question `f` and the import calls `cs` from `.idle u`, the instance makes the import
calls `c 0, c 1, …` one by one; then `cs` followed by `c` is a productive stream of `f` at `u`. -/
theorem instInf_of_calls {u s : Store Nat} {f : I.F.Op} {cs : List (Call I.E)}
    {t : Silmaril.Wasm.SingleThreaded.Thread} {q : ℕ → I.HState} {c : ℕ → Call I.E}
    (hp : I.Path P (.idle u) (.inr (.ask f) :: callMoves cs) (.running f s t))
    (hq0 : q 0 = .running f s t) (hq : ∀ k, I.Path P (q k) (callMoves [c k]) (q (k + 1))) :
    prependStream cs c ∈ instInf I P u f :=
  Silmaril.Proofs.Wasm.Abstract.NodeDiv.instInf_of_calls hp hq0 hq

/-- **A productive stream of a round, cut after `n` calls**: the round so far ends running, and
the remaining calls are made one by one from there. -/
theorem calls_of_instInf {u : Store Nat} {f : I.F.Op} {ω : ℕ → Call I.E}
    (hω : ω ∈ instInf I P u f) (n : ℕ) :
    ∃ s t, ∃ q : ℕ → I.HState,
      I.Path P (.idle u) (.inr (.ask f) :: callMoves (streamTake ω n)) (.running f s t) ∧
      q 0 = .running f s t ∧ ∀ k, I.Path P (q k) (callMoves [ω (n + k)]) (q (k + 1)) :=
  Silmaril.Proofs.Wasm.Abstract.NodeDiv.calls_of_instInf hω n

end Session

/-! ## The coercions -/

/-- **A handler that always calls has no silent chatter** with the strategy above it. -/
theorem not_silentChatter_of_allCall {E F G : Sig.{0}} {h : Handler E F} (hh : AllCall h)
    {σ : DStrategy F G} {s : List (Move E G)} : ¬ SilentChatter h σ s :=
  Silmaril.Proofs.Wasm.Abstract.NodeDiv.not_silentChatter_of_allCall hh

/-- `importH` answers every question by exactly one call. -/
theorem allCall_importH (m : NumInstance) : AllCall (importH m) :=
  Silmaril.Proofs.Wasm.Abstract.NodeDiv.allCall_importH m

/-- `exportH` answers every question by at most one call. -/
theorem oneCall_exportH (m : NumInstance) : OneCall (exportH m) :=
  Silmaril.Proofs.Wasm.Abstract.NodeDiv.oneCall_exportH m

/-- **The coercions add no divergence**: `semOfSD m σ` diverges exactly where `spullD σ` does,
through `importH` and `exportH`. -/
theorem div_semOfSD (m : NumInstance) (σ : DStrategy m.inst.E (ssig m.inst.exports)) :
    (semOfSD m σ).div = {p | ∃ u v, Zip u v p ∧ u ∈ Strategy.ofHandler (importH m) ∧
      ∃ a b, Zip a b v ∧ a ∈ (spullD σ).div ∧ b ∈ Strategy.ofHandler (exportH m)} :=
  Silmaril.Proofs.Wasm.Abstract.NodeDiv.div_semOfSD m σ

/-- **The divergences of a Core 3.0 module** under `core3SemD P`: an instance path from the
instantiation store to a running state that diverges host-free, through `importH` and
`exportH`. -/
theorem div_core3SemD_sem (P : Profile) (m : NumInstance) :
    ((core3SemD P).sem m).div = {p | ∃ u v, Zip u v p ∧ u ∈ Strategy.ofHandler (importH m) ∧
      ∃ a b, Zip a b v ∧
        (∃ f s t, m.inst.Path P (.idle m.inst.store) a (.running f s t) ∧ Diverges P (s, t)) ∧
        b ∈ Strategy.ofHandler (exportH m)} :=
  Silmaril.Proofs.Wasm.Abstract.NodeDiv.div_core3SemD_sem P m

end Silmaril.Wasm.Abstract.NodeDiv

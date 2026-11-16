module

public import Silmaril.Games.Abstract.SessionLink.Defs
public import Silmaril.Games.Abstract.StratSession.Thms
public import Silmaril.Games.DivComp.Defs
import Silmaril.Proofs.Games.Abstract.SessionLink.Plays
import Silmaril.Proofs.Games.Abstract.SessionLink.Div
import Silmaril.Proofs.Games.Abstract.SessionLink.InfBwd
import Silmaril.Proofs.Games.Abstract.SessionLink.Det
import Silmaril.Proofs.Games.Abstract.SessionLink.InfFwd
import Silmaril.Proofs.Games.Abstract.SessionLink.Trap

/-!
# Linking sessions: theorems

The server session `threadS t s₀ : DStrategy E (sig1 A B)` serves the imports of the client
session `threadS u s₀' : DStrategy (sig1 A B) (sig1 A' B')`; their composite
`(threadS t s₀).comp (threadS u s₀')` hides the interaction on `sig1 A B`.

**Linking is composition with hiding** (`comp_threadS`): for a server without plain traps
(`StratSession.NoPlainTrap t`) that is store-deterministic (`StratThread.StoreDet t`), and a
store-deterministic linked triple (`StoreDet (linkS t u)`),

  `(threadS t s₀).comp (threadS u s₀') = threadS (linkS t u) (s₀, s₀')`,

all three components (finite plays, divergence, infinite plays). For components deterministic
given answers (`AFun.Det` of `t.1` and `u.1`) the hypotheses on stores hold
(`comp_threadS_of_det`). The parts hold under fewer hypotheses:

* **Finite plays** (`comp_threadS_toStrategy`): `NoPlainTrap t` only. The interaction is tracked by
  relating the states of the three session automata: while the client runs a round, the server is
  idle at the store reached by the rounds that served the client's calls so far, and the linked
  automaton runs the same round at the stores of the round's start; while the client waits on a
  call, the server runs the session round serving it. Conversely each linked run is realized by an
  interaction, built round by round from the witnesses of the linked behaviours and pending calls.
* **Divergence**: every linked divergence is one of the composite (`div_linkS_subset`, no
  hypothesis): a client divergence or a server divergence inside a served call is a local divergence
  of a component, and a served client stream with finitely many server calls is hidden chatter.
  Conversely (`div_comp_subset`, `NoPlainTrap t` and `StoreDet t`), hidden chatter is a client
  stream inside one round served by a *coherent* infinite play of the server.
* **Infinite plays**: an infinite play of the composite is one of the linked session
  (`inf_comp_subset`, `NoPlainTrap t` and `StoreDet t`): the client completes infinitely many rounds,
  or streams inside one round with infinitely many server calls, or waits on one call while the
  server streams inside it. Conversely (`inf_linkS_subset`, `StoreDet (linkS t u)`), a linked stream
  or a coherent infinite sequence of linked rounds is the limit of an interaction.

**Why the hypotheses.**

* `NoPlainTrap t`: a plain trap of the server answers `.inr ()` and kills the server session, so a
  later call of the client is never answered, which the store `S × S'` cannot record.
* `StoreDet t`: the linked streams and chatter divergences of `linkS` serve infinitely many client
  calls by a coherent infinite sequence of server rounds (`InfServe`), while an infinite play of
  the server session only requires every finite prefix of its rounds to be completed
  (`StratThread.not_coherent`). With `StoreDet t` the server's runs are unique and cohere.
* `StoreDet (linkS t u)`: the linked session's infinite plays completing infinitely many rounds
  also need only every finite prefix to be completed, but the composite needs one interaction whose
  hidden part extends round by round. A client whose first round makes a hidden call choosing a
  bound `n` on its later rounds, against a server answering everything, has every finite number of
  linked rounds but no infinite interaction.

**The linked triple is saturated** (`saturated_linkS`): every call forced by a linked behaviour
or stream is a pending call of the linked triple, a call prefix of the server inside a served call.

**Plain traps.** The linked triple has no plain traps when the client has none
(`noPlainTrap_linkS`): server divergence and hidden chatter end in `div`.

**Determinism.** If the server and the client are deterministic given answers, the linked triple is
store-deterministic (`storeDet_linkS`), so the linked session has coherent infinite plays
(`mem_inf_linkS_iff_of_det`). The linked triple itself need not be `AFun.Det`: `AFun.Det u.1` does
not relate the client's finished behaviours to its pending calls, so a client that may return at
once or call `a` gives, against a server diverging at `a`, a linked return and a linked divergence
with the same empty log.

Proofs are in `Silmaril.Proofs.Games.Abstract.SessionLink`.
-/

public section

namespace Silmaril.Games.Abstract.SessionLink

open Silmaril.Games Silmaril.Games.Abstract.StratObs Silmaril.Games.Abstract.StratThread
  Silmaril.Games.Abstract.StratSession

universe u

variable {E : Sig.{u}} {S S' A B A' B' : Type u} {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})}
  {u : ObsTriple (sig1 A B) S' A' (B' ⊕ PUnit.{u + 1})}

/-- **The linked triple is saturated**: its call prefixes are its pending calls. -/
theorem saturated_linkS : Saturated (linkS t u) :=
  saturated_iff.2 <| funext fun _ => funext fun _ => Set.ext fun _ =>
    ⟨Silmaril.Proofs.Games.Abstract.SessionLink.satP_linkS, .inl⟩

/-- **The finite plays of linked sessions**: for a server without plain traps, the composite of
the server session and the client session has the finite plays of the linked session. -/
theorem comp_threadS_toStrategy (hnt : NoPlainTrap t) (s₀ : S) (s₀' : S') :
    ((threadS t s₀).comp (threadS u s₀')).toStrategy =
      (threadS (linkS t u) (s₀, s₀')).toStrategy :=
  Strategy.ext fun _ => Silmaril.Proofs.Games.Abstract.SessionLink.mem_comp_iff hnt

/-- **Linked divergences are divergences of the composite.** -/
theorem div_linkS_subset (s₀ : S) (s₀' : S') :
    (threadS (linkS t u) (s₀, s₀')).div ⊆ ((threadS t s₀).comp (threadS u s₀')).div :=
  fun _ => Silmaril.Proofs.Games.Abstract.SessionLink.div_bwd

/-- **Linked infinite plays are infinite plays of the composite**, for a store-deterministic
linked triple. -/
theorem inf_linkS_subset (hL : StoreDet (linkS t u)) (s₀ : S) (s₀' : S') :
    (threadS (linkS t u) (s₀, s₀')).inf ⊆ ((threadS t s₀).comp (threadS u s₀')).inf :=
  fun _ => Silmaril.Proofs.Games.Abstract.SessionLink.inf_bwd hL

/-- **A client without plain traps gives a linked triple without plain traps.** -/
theorem noPlainTrap_linkS (hu : NoPlainTrap u) : NoPlainTrap (linkS t u) :=
  Silmaril.Proofs.Games.Abstract.SessionLink.noPlainTrap_linkS hu

/-- **Deterministic components give a store-deterministic linked triple.** -/
theorem storeDet_linkS (ht : AFun.Det t.1) (hu : AFun.Det u.1) : StoreDet (linkS t u) :=
  Silmaril.Proofs.Games.Abstract.SessionLink.storeDet_linkS ht hu

/-- **Linked deterministic components have coherent infinite plays**: a stream after completed
linked rounds, or the play of a coherent infinite sequence of linked rounds. -/
theorem mem_inf_linkS_iff_of_det (ht : AFun.Det t.1) (hu : AFun.Det u.1) {σ₀ : S × S'}
    {I : Set (List (Move E (sig1 A' B')))} :
    I ∈ (threadS (linkS t u) σ₀).inf ↔
      (∃ rs σ a ω, Rounds (linkS t u) σ₀ rs σ ∧ ω ∈ (linkS t u).2.2 σ a ∧
        I = streamPlay (sroundsMoves rs) a ω) ∨
      ∃ a r st, InfRounds (linkS t u) σ₀ a r st ∧ I = sroundsPlay a r :=
  mem_inf_iff_of_storeDet (storeDet_linkS ht hu)

/-- **Divergences of the composite are linked divergences**, for a store-deterministic server
without plain traps. -/
theorem div_comp_subset (hnt : NoPlainTrap t) (htd : StoreDet t) (s₀ : S) (s₀' : S') :
    ((threadS t s₀).comp (threadS u s₀')).div ⊆ (threadS (linkS t u) (s₀, s₀')).div :=
  fun _ => Silmaril.Proofs.Games.Abstract.SessionLink.div_fwd hnt htd

/-- **Infinite plays of the composite are linked infinite plays**, for a store-deterministic
server without plain traps. -/
theorem inf_comp_subset (hnt : NoPlainTrap t) (htd : StoreDet t) (s₀ : S) (s₀' : S') :
    ((threadS t s₀).comp (threadS u s₀')).inf ⊆ (threadS (linkS t u) (s₀, s₀')).inf :=
  fun _ => Silmaril.Proofs.Games.Abstract.SessionLink.inf_fwd hnt htd

/-- **Linking is composition with hiding**: the composite of the server session and the client
session is the session of the linked triple. -/
theorem comp_threadS (hnt : NoPlainTrap t) (htd : StoreDet t) (hL : StoreDet (linkS t u))
    (s₀ : S) (s₀' : S') :
    (threadS t s₀).comp (threadS u s₀') = threadS (linkS t u) (s₀, s₀') :=
  Silmaril.Proofs.Games.Abstract.SessionLink.comp_threadS hnt htd hL s₀ s₀'

/-- **Linking deterministic components is composition with hiding.** -/
theorem comp_threadS_of_det (hnt : NoPlainTrap t) (ht : AFun.Det t.1) (hu : AFun.Det u.1)
    (s₀ : S) (s₀' : S') :
    (threadS t s₀).comp (threadS u s₀') = threadS (linkS t u) (s₀, s₀') :=
  comp_threadS hnt (storeDet_of_det ht) (storeDet_linkS ht hu) s₀ s₀'

end Silmaril.Games.Abstract.SessionLink

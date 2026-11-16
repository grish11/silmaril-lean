module

public import Silmaril.Games.Abstract.SessionLinkCex.Defs
public import Silmaril.Games.Abstract.SessionLink.Thms
import Silmaril.Proofs.Games.Abstract.SessionLinkCex.PlainTrap
import Silmaril.Proofs.Games.Abstract.SessionLinkCex.Coherent
import Silmaril.Proofs.Games.Abstract.SessionLinkCex.LinkCoherent
import Silmaril.Proofs.Games.Abstract.SessionLinkCex.Det

/-!
# Linking sessions: counterexamples

Each hypothesis of `SessionLink.comp_threadS`,

  `(threadS t s₀).comp (threadS u s₀') = threadS (linkS t u) (s₀, s₀')`
  for `NoPlainTrap t`, `StoreDet t` and `StoreDet (linkS t u)`,

is needed: dropping one, with the other two kept, breaks the equality, in the component that the
corresponding partial theorem of `SessionLink.Thms` covers.

* **`NoPlainTrap t`** (`comp_ne_linkS_plainTrap`): the server traps plainly, the client calls it
  once and returns. The composite answers the question (`askRet_mem_comp`), the linked session
  does not (`askRet_not_mem_linkS`): the finite plays differ (`comp_threadS_toStrategy`). Both
  components are deterministic given answers, so this is also the counterexample for
  `comp_threadS_of_det` without `NoPlainTrap t`.
* **`StoreDet t`** (`comp_ne_linkS_cd`): the countdown server (`StratThread.not_coherent`) serves
  every finite number of calls of the chattering client, so the composite diverges after the
  question (`div_comp_cd`), but no infinite service is coherent (`not_infServe`), so the linked
  session does not (`not_div_linkS_cd`): `div_comp_subset` fails.
* **`StoreDet (linkS t u)`** (`comp_ne_linkS_bound`): the client's first round calls the echo
  server with a bound `n` on its later rounds. The server is deterministic and the client
  store-deterministic, but the linked triple is not (`not_storeDet_linkS_bound`): the call is
  hidden. The linked session plays `unitRounds`, infinitely many rounds
  (`unitRounds_mem_linkS`); no interaction does (`unitRounds_not_mem_comp`):
  `inf_linkS_subset` fails.
* **`AFun.Det` is not preserved by linking** (`not_det_linkS_may`): the client may return at once
  or call the diverging server; the linked triple returns and diverges with the empty log. It is
  still store-deterministic (`storeDet_linkS_may`), so `comp_threadS_of_det` does not need it.

Proofs are in `Silmaril.Proofs.Games.Abstract.SessionLinkCex`.
-/

public section

namespace Silmaril.Games.Abstract.SessionLinkCex

open Silmaril.Games Silmaril.Games.Abstract.StratObs Silmaril.Games.Abstract.StratThread
  Silmaril.Games.Abstract.StratSession Silmaril.Games.Abstract.SessionLink

variable {E : Sig.{0}}

/-! ## A plain server trap -/

/-- The trapping server is deterministic given answers. -/
theorem det_trapServer : AFun.Det (trapServer (E := E)).1 :=
  Silmaril.Proofs.Games.Abstract.SessionLinkCex.det_trapServer

/-- The calling client is deterministic given answers. -/
theorem det_trapClient : AFun.Det trapClient.1 :=
  Silmaril.Proofs.Games.Abstract.SessionLinkCex.det_trapClient

/-- The trapping server has a plain trap. -/
theorem not_noPlainTrap_trapServer : ¬ NoPlainTrap (trapServer (E := E)) :=
  Silmaril.Proofs.Games.Abstract.SessionLinkCex.not_noPlainTrap_trapServer

/-- The server's plain trap answers the client's call, which returns: the composite answers. -/
theorem askRet_mem_comp :
    [.inr (.ask ()), .inr (.ans () (Sum.inl ()))] ∈
      ((threadS (trapServer (E := E)) ()).comp (threadS trapClient ())).toStrategy :=
  Silmaril.Proofs.Games.Abstract.SessionLinkCex.askRet_mem_comp

/-- `linkS` serves calls by returning rounds only: the linked session never answers. -/
theorem askRet_not_mem_linkS :
    [.inr (.ask ()), .inr (.ans () (Sum.inl ()))] ∉
      (threadS (linkS (trapServer (E := E)) trapClient) ((), ())).toStrategy :=
  Silmaril.Proofs.Games.Abstract.SessionLinkCex.askRet_not_mem_linkS

/-- **`NoPlainTrap t` is needed**, even for components deterministic given answers: the finite
plays of the composite are not those of the linked session. -/
theorem comp_ne_linkS_plainTrap :
    ((threadS (trapServer (E := E)) ()).comp (threadS trapClient ())).toStrategy ≠
      (threadS (linkS (trapServer (E := E)) trapClient) ((), ())).toStrategy :=
  fun h => askRet_not_mem_linkS (h ▸ askRet_mem_comp)

/-! ## A non-coherent server -/

/-- The countdown server has no plain trap. -/
theorem noPlainTrap_cdServer : NoPlainTrap (cdServer (E := E)) :=
  Silmaril.Proofs.Games.Abstract.SessionLinkCex.noPlainTrap_cdServer

/-- The countdown server is not store-deterministic. -/
theorem not_storeDet_cdServer : ¬ StoreDet (cdServer (E := E)) :=
  Silmaril.Proofs.Games.Abstract.SessionLinkCex.not_storeDet_cdServer

/-- The linked triple of the countdown and the chattering client is store-deterministic: it never
returns. -/
theorem storeDet_linkS_cd : StoreDet (linkS (cdServer (E := E)) chatClient) :=
  Silmaril.Proofs.Games.Abstract.SessionLinkCex.storeDet_linkS_cd

/-- **No infinite service by the countdown is coherent.** -/
theorem not_infServe {ω : ℕ → Call (sig1 Unit Unit)} {l : ℕ → List (Call E)}
    {st : ℕ → Option ℕ} : ¬ InfServe (cdServer (E := E)) none ω l st :=
  Silmaril.Proofs.Games.Abstract.SessionLinkCex.not_infServe

/-- The composite chatters: the countdown serves every finite number of calls. -/
theorem div_comp_cd :
    [.inr (.ask ())] ∈ ((threadS (cdServer (E := E)) none).comp (threadS chatClient ())).div :=
  Silmaril.Proofs.Games.Abstract.SessionLinkCex.div_comp_chat

/-- The linked session does not diverge after the question. -/
theorem not_div_linkS_cd :
    [.inr (.ask ())] ∉ (threadS (linkS (cdServer (E := E)) chatClient) (none, ())).div :=
  Silmaril.Proofs.Games.Abstract.SessionLinkCex.not_div_linkS_chat

/-- **`StoreDet t` is needed**: the divergences of the composite are not linked divergences. -/
theorem comp_ne_linkS_cd :
    ¬ ((threadS (cdServer (E := E)) none).comp (threadS chatClient ())).div ⊆
      (threadS (linkS (cdServer (E := E)) chatClient) (none, ())).div :=
  fun h => not_div_linkS_cd (h div_comp_cd)

/-! ## A non-coherent linked triple -/

/-- The echo server has no plain trap. -/
theorem noPlainTrap_echoServer : NoPlainTrap (echoServer (E := E)) :=
  Silmaril.Proofs.Games.Abstract.SessionLinkCex.noPlainTrap_echoServer

/-- The echo server is deterministic given answers. -/
theorem det_echoServer : AFun.Det (echoServer (E := E)).1 :=
  Silmaril.Proofs.Games.Abstract.SessionLinkCex.det_echoServer

/-- The echo server is store-deterministic. -/
theorem storeDet_echoServer : StoreDet (echoServer (E := E)) := storeDet_of_det det_echoServer

/-- The bounding client is store-deterministic: its call shows the bound. -/
theorem storeDet_boundClient : StoreDet boundClient :=
  Silmaril.Proofs.Games.Abstract.SessionLinkCex.storeDet_boundClient

/-- The linked triple is not store-deterministic: the bound is hidden. -/
theorem not_storeDet_linkS_bound : ¬ StoreDet (linkS (echoServer (E := E)) boundClient) :=
  Silmaril.Proofs.Games.Abstract.SessionLinkCex.not_storeDet_linkS_bound

/-- The linked session plays infinitely many rounds. -/
theorem unitRounds_mem_linkS :
    unitRounds ∈ (threadS (linkS (echoServer (E := E)) boundClient) ((), none)).inf :=
  Silmaril.Proofs.Games.Abstract.SessionLinkCex.unitRounds_mem_linkS

/-- No interaction of the echo server and the bounding client plays infinitely many rounds. -/
theorem unitRounds_not_mem_comp :
    unitRounds ∉ ((threadS (echoServer (E := E)) ()).comp (threadS boundClient none)).inf :=
  Silmaril.Proofs.Games.Abstract.SessionLinkCex.unitRounds_not_mem_comp

/-- **`StoreDet (linkS t u)` is needed**: the linked infinite plays are not infinite plays of the
composite. -/
theorem comp_ne_linkS_bound :
    ¬ (threadS (linkS (echoServer (E := E)) boundClient) ((), none)).inf ⊆
      ((threadS (echoServer (E := E)) ()).comp (threadS boundClient none)).inf :=
  fun h => unitRounds_not_mem_comp (h unitRounds_mem_linkS)

/-! ## Linking does not preserve `AFun.Det` -/

/-- The diverging server is deterministic given answers. -/
theorem det_divServer : AFun.Det (divServer (E := E)).1 :=
  Silmaril.Proofs.Games.Abstract.SessionLinkCex.det_divServer

/-- The client that may call is deterministic given answers. -/
theorem det_mayClient : AFun.Det mayClient.1 :=
  Silmaril.Proofs.Games.Abstract.SessionLinkCex.det_mayClient

/-- The diverging server has no plain trap. -/
theorem noPlainTrap_divServer : NoPlainTrap (divServer (E := E)) :=
  Silmaril.Proofs.Games.Abstract.SessionLinkCex.noPlainTrap_divServer

/-- The client that may call has no plain trap. -/
theorem noPlainTrap_mayClient : NoPlainTrap mayClient :=
  Silmaril.Proofs.Games.Abstract.SessionLinkCex.noPlainTrap_mayClient

/-- **Linking does not preserve `AFun.Det`**: the linked triple returns and diverges with the
empty log. -/
theorem not_det_linkS_may : ¬ AFun.Det (linkS (divServer (E := E)) mayClient).1 :=
  Silmaril.Proofs.Games.Abstract.SessionLinkCex.not_det_linkS_may

/-- The linked triple is still store-deterministic (`storeDet_linkS`). -/
theorem storeDet_linkS_may : StoreDet (linkS (divServer (E := E)) mayClient) :=
  storeDet_linkS det_divServer det_mayClient

end Silmaril.Games.Abstract.SessionLinkCex

module

public import Silmaril.Games.Abstract.SessionRoute.Defs
public import Silmaril.Games.Abstract.SessionCat.Thms
public import Silmaril.Games.DivLTS.Defs
import Silmaril.Proofs.Games.Abstract.SessionRoute.Limits
import Silmaril.Proofs.Games.Abstract.SessionRoute.Handler
import Silmaril.Proofs.Games.Abstract.SessionRoute.Map

/-!
# Sessions composed with one-call handlers: theorems

**Handlers have every limit of their plays** (`ofHandler_eq_limits`): the transition system of a
handler is deterministic and has no silent steps, so `DStrategy.ofHandler h` never diverges and
its infinite plays are all the infinite traces of its finite plays (`DStrategy.limits`).

**A one-call handler is a session** (`threadS_callS`): the session of the stateless triple
`callS g f` is the strategy of `callH g f`,

  `threadS (callS g f) () = DStrategy.ofHandler (callH g f)`,

for any lower interface `E`. It has deterministic returns and no plain traps (`retDet_callS`,
`noPlainTrap_callS`), so it can be linked as a client or a server (`SessionLink`).

**Routing a session** (`threadS_comp_callH`): a session `threadS t s` on `sig1 A B` composed with
a one-call handler `callH g f : Handler (sig1 A B) (sig1 A' B')` (question `a'` asks `g a'`, the
answer `x` is returned as `f a' x`) is the session of the mapped triple,

  `(threadS t s).comp (DStrategy.ofHandler (callH g f)) = threadS (mapS g f t) s`,

for a server `t` without plain traps (`NoPlainTrap t`) whose returns are deterministic given
answers (`SessionCat.RetDet t`). The proof links `t` with `callS g f`
(`SessionLink.comp_threadS`): the linked triple is bisimilar to `mapS g f t` through the first
store component (`obsEq_linkS_callS`). `NoPlainTrap t` is needed: a plain trap of `t` ends the
server session, which the linked triple does not record, while `mapS g f t` keeps it as a plain
trap. Mapping keeps the absence of plain traps and deterministic returns (`noPlainTrap_mapS`,
`retDet_mapS`).

Proofs are in `Silmaril.Proofs.Games.Abstract.SessionRoute`.
-/

public section

namespace Silmaril.Games.Abstract.SessionRoute

open Silmaril.Games Silmaril.Games.Abstract.StratObs Silmaril.Games.Abstract.StratThread
  Silmaril.Games.Abstract.StratSession Silmaril.Games.Abstract.SessionLink
  Silmaril.Games.Abstract.SessionCat

universe u

/-- **A handler's strategy has no divergence and every limit of its plays.** -/
theorem ofHandler_eq_limits {E F : Sig.{u}} (h : Handler E F) :
    DStrategy.ofHandler h = DStrategy.limits (Strategy.ofHandler h) :=
  Silmaril.Proofs.Games.Abstract.SessionRoute.ofHandler_eq_limits h

section CallS

variable {E : Sig.{u}} {A B : Type u} {g : A → E.Op} {f : (a : A) → E.Ar (g a) → B ⊕ PUnit.{u + 1}}

/-- **The session of a one-call handler is the handler's strategy.** -/
theorem threadS_callS : threadS (callS g f) PUnit.unit = DStrategy.ofHandler (callH g f) :=
  Silmaril.Proofs.Games.Abstract.SessionRoute.threadS_callS

/-- The session triple of a one-call handler has deterministic returns. -/
theorem retDet_callS : RetDet (callS g f) :=
  Silmaril.Proofs.Games.Abstract.SessionRoute.retDet_callS

/-- The session triple of a one-call handler has no plain traps. -/
theorem noPlainTrap_callS : NoPlainTrap (callS g f) :=
  Silmaril.Proofs.Games.Abstract.SessionRoute.noPlainTrap_callS

end CallS

variable {E : Sig.{u}} {S A A' B B' : Type u} {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})}
  {g : A' → A} {f : A' → B ⊕ PUnit.{u + 1} → B' ⊕ PUnit.{u + 1}}

/-- A round of the mapped triple is a round of `t` at the mapped question, its end mapped. -/
theorem mem_mapS {s : S} {a' : A'} {x : List (Call E) × End S (B' ⊕ PUnit.{u + 1})} :
    x ∈ (mapS g f t).1 s a' ↔ ∃ e, (x.1, e) ∈ t.1 s (g a') ∧ x.2 = mapEnd (f a') e :=
  Silmaril.Proofs.Games.Abstract.SessionRoute.mem_mapS

/-- Mapping keeps the absence of plain traps. -/
theorem noPlainTrap_mapS (h : NoPlainTrap t) : NoPlainTrap (mapS g f t) :=
  Silmaril.Proofs.Games.Abstract.SessionRoute.noPlainTrap_mapS h

/-- Mapping keeps deterministic returns. -/
theorem retDet_mapS (h : RetDet t) : RetDet (mapS g f t) :=
  Silmaril.Proofs.Games.Abstract.SessionRoute.retDet_mapS h

/-- **Linking a one-call client is mapping the server**, up to bisimilarity of stores. -/
theorem obsEq_linkS_callS (hnt : NoPlainTrap t) (s : S) :
    ObsEq (linkS t (callS (E := sig1 A B) g f)) (mapS g f t) (s, PUnit.unit) s :=
  Silmaril.Proofs.Games.Abstract.SessionRoute.obsEq_linkS_callS hnt s

/-- **A session served to a one-call handler is the session of the mapped triple.** -/
theorem threadS_comp_callH (hnt : NoPlainTrap t) (ht : RetDet t) (s : S) :
    (threadS t s).comp (DStrategy.ofHandler (callH (E := sig1 A B) g f)) =
      threadS (mapS g f t) s :=
  Silmaril.Proofs.Games.Abstract.SessionRoute.threadS_comp_callH hnt ht s

end Silmaril.Games.Abstract.SessionRoute

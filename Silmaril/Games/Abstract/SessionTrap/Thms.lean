module

public import Silmaril.Games.Abstract.SessionTrap.Defs
import Silmaril.Proofs.Games.Abstract.SessionTrap.Thread

/-!
# Sessions whose rounds abort on a trap from below: theorems

**Threading** (`threadS_trapAbortsBelow`): if every round of the store-retaining triple `t`
aborts at a trap from below (`TrapAbortsRound T t`), then in every play of the session
`threadS t s₀`, a trap answer from below is followed, if at all, by the trap answer `.inr ()` to
the current question (`TrapAbortsBelow T`). In particular the session makes no further call in
that round (`TrapAbortsBelow.trapEndsBelow`).

The proof follows the threading automaton: the trap answer leaves the round at the call log
`c ++ [⟨m, n⟩]`; a further call would need a call prefix of `t` past the trapped call, which
`TrapAbortsRound` excludes for pending calls, for calls forced by behaviours and for productive
streams; a return there is a trap keeping its store, shown as `.inr ()` after the relabelling of
`threadS`; a plain trap is shown as `.inr ()` too.

Proofs are in `Silmaril.Proofs.Games.Abstract.SessionTrap`.
-/

public section

namespace Silmaril.Games.Abstract.SessionTrap

open Silmaril.Games Silmaril.Games.Abstract.StratSession

universe u

variable {E : Sig.{u}} {S A B : Type u} {T : (m : E.Op) → E.Ar m → Prop}

/-- Answering a trap ends the round. -/
theorem TrapAbortsBelow.trapEndsBelow {σ : DStrategy E (sig1 A B)} (h : TrapAbortsBelow T σ) :
    TrapEndsBelow T σ := fun p m n y hT hp =>
  let ⟨_, hy⟩ := h p m n y hT hp; ⟨_, hy⟩

/-- **A session whose rounds abort on a trap from below answers a trap after it.** -/
theorem threadS_trapAbortsBelow {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})}
    (ht : TrapAbortsRound T t) (s₀ : S) : TrapAbortsBelow T (threadS t s₀) :=
  Silmaril.Proofs.Games.Abstract.SessionTrap.threadS_next ht s₀

end Silmaril.Games.Abstract.SessionTrap

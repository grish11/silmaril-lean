module

public import Silmaril.Wasm.Abstract.InstStrat.Defs
public import Silmaril.Games.Abstract.StratThread.Thms
public import Silmaril.Wasm.Game.Strategy.Thms
import Silmaril.Proofs.Wasm.Abstract.InstStrat.Basic

/-!
# Scalar Core 3.0 instances as threaded canonical play objects: theorems

**The main theorem.** For every instance `I`, profile `P` (nondeterministic profiles included)
and store `s`, the finite plays of the threaded instance triple are exactly the relabelled plays
of the instance strategy:

* `mem_instThread`: `p' ∈ (instThread I P s).toStrategy ↔ ∃ p ∈ I.strategy P s, p.map relabel = p'`;
* `map_relabel_mem`: `p.map relabel ∈ (instThread I P s).toStrategy ↔ p ∈ I.strategy P s`;
* `pull_instThread`: `pull (instThread I P s).toStrategy = I.strategy P s`.

So the threaded strategy never plays the sig1 trap answer `.inr ()` or a mistagged answer, and
`relabel` is a bijection between the two sets of plays (`relabel_injective`). No closure is
needed on either side: both are prefix closed and receptive by construction (the threading
automaton accepts every Opponent move, the hidden transition system accepts every export
question when idle and every import answer when waiting), and the call prefixes `satP` of the
triple are already pending calls of the instance (prefixes of runs are runs).

**Persistence.** The stores reachable by threading are the stores reachable by complete
activations of the instance (`reach_iff_reachableStore`); a Wasm trap is a returning round, so it
keeps the store.

**The component level.** `core3Sem P` is the core semantics of the threaded canonical objects
(`core3Sem_eq`), so `Comp.den (core3Sem P) c` sees each core module only through
`instThread m.inst P m.inst.store` (`den_core3Sem`). Replacing the instance triple of every
module by an observationally equivalent triple (`StratThread.ObsEq`, possibly with another store
type, `den_core3Sem_eq_of_obsEq`), or by a triple that agrees with it on every reachable store
(`den_core3Sem_eq_of_reach`), does not change the denotation of any component; nor does
changing the profile when the triples of the two profiles are observationally equivalent
(`den_core3Sem_eq_of_obsEq_profile`).

Not claimed (obligations, see `Silmaril.Wasm.Abstract.InstStrat.Defs`): component injectivity
modulo an independent component equivalence, adequacy of the reference machine, and correctness
of the passage from bytes to `Comp`. The `div` and `inf` components of `instThread` are defined
but not compared with anything here: `Strategy.ofLTS` exposes only finite plays.

Proofs are in `Silmaril.Proofs.Wasm.Abstract.InstStrat.Basic`.
-/

public section

namespace Silmaril.Wasm.Abstract.InstStrat

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
open Silmaril.Wasm.Game Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Numerics (Profile)

universe u

/-- The move map is injective. -/
theorem relabel_injective {E F : Sig.{u}} : Function.Injective (relabel (E := E) (F := F)) :=
  Silmaril.Proofs.Wasm.Abstract.InstStrat.relabel_injective

variable {I : ScalarInstance} {P : Profile}

/-- **Wasm traps do not end the threading**: the instance triple has no `End.trap`. -/
theorem trap_not_mem {s : Store Nat} {a : I.F.Op} {c : List (Call I.E)} :
    (c, .trap) ∉ (instTriple I P).1 s a := by
  rintro (⟨_, _, he, -⟩ | ⟨he, -⟩) <;> cases he

/-- **The plays of the threaded instance** are the relabelled plays of the instance, at every
store and profile. -/
theorem mem_instThread {s : Store Nat} {p' : List (Move I.E (tsig I.F))} :
    p' ∈ (instThread I P s).toStrategy ↔ ∃ p ∈ I.strategy P s, p.map relabel = p' :=
  Silmaril.Proofs.Wasm.Abstract.InstStrat.mem_instThread

/-- A relabelled play is a play of the threaded instance iff it is a play of the instance. -/
theorem map_relabel_mem {s : Store Nat} {p : List (Move I.E I.F)} :
    p.map relabel ∈ (instThread I P s).toStrategy ↔ p ∈ I.strategy P s :=
  Silmaril.Proofs.Wasm.Abstract.InstStrat.map_relabel_mem

/-- **The threaded instance read back on `I.F` is the instance strategy.** -/
theorem pull_instThread (s : Store Nat) : pull (instThread I P s).toStrategy = I.strategy P s :=
  Silmaril.Proofs.Wasm.Abstract.InstStrat.pull_instThread s

/-- The stores reachable by threading are those reachable by complete activations. -/
theorem reach_iff_reachableStore {s₀ s : Store Nat} :
    StratThread.Reach (instTriple I P) s₀ s ↔ I.ReachableStore P s₀ s :=
  Silmaril.Proofs.Wasm.Abstract.InstStrat.reach_iff_reachableStore

/-! ## The component level -/

/-- **`core3Sem P` is built from the threaded canonical objects** of the instances at their
instantiation stores. -/
theorem core3Sem_eq (P : Profile) :
    core3Sem P = threadSem fun m => instThread m.inst P m.inst.store := by
  unfold core3Sem threadSem; congr 1; funext m; rw [semOf, pull_instThread]

/-- Component denotations over Core 3.0 instances see each module only through its threaded
canonical object. -/
theorem den_core3Sem (P : Profile) (c : Comp NumInstance) :
    c.den (core3Sem P) = c.den (threadSem fun m => instThread m.inst P m.inst.store) := by
  rw [← core3Sem_eq]

/-- **Observationally equivalent triples give the same component denotations**: replacing the
instance triple of every module by an observationally equivalent one (on any store type). -/
theorem den_core3Sem_eq_of_obsEq {S' : NumInstance → Type}
    (t : (m : NumInstance) → ObsTriple m.inst.E (S' m) m.inst.F.Op (Ans m.inst.F))
    (s' : (m : NumInstance) → S' m)
    (h : ∀ m, StratThread.ObsEq (instTriple m.inst P) (t m) m.inst.store (s' m))
    (c : Comp NumInstance) :
    c.den (core3Sem P) = c.den (threadSem fun m => StratThread.threadT (t m) (s' m)) := by
  rw [den_core3Sem]
  exact congrArg (fun T => c.den (threadSem T)) (funext fun m => StratThread.threadT_eq_of_obsEq (h m))

/-- **Triples agreeing on reachable stores give the same component denotations.** -/
theorem den_core3Sem_eq_of_reach
    (t : (m : NumInstance) → ObsTriple m.inst.E (Store Nat) m.inst.F.Op (Ans m.inst.F))
    (h : ∀ m s, m.inst.ReachableStore P m.inst.store s →
      (instTriple m.inst P).1 s = (t m).1 s ∧ satP (instTriple m.inst P) s = satP (t m) s ∧
        (instTriple m.inst P).2.2 s = (t m).2.2 s)
    (c : Comp NumInstance) :
    c.den (core3Sem P) = c.den (threadSem fun m => StratThread.threadT (t m) m.inst.store) := by
  rw [den_core3Sem]
  exact congrArg (fun T => c.den (threadSem T)) (funext fun m =>
    StratThread.threadT_congr fun s hs => h m s (reach_iff_reachableStore.1 hs))

/-- Two profiles whose instance triples are observationally equivalent at the instantiation
stores give the same component denotations. -/
theorem den_core3Sem_eq_of_obsEq_profile {Q : Profile}
    (h : ∀ m : NumInstance,
      StratThread.ObsEq (instTriple m.inst P) (instTriple m.inst Q) m.inst.store m.inst.store)
    (c : Comp NumInstance) : c.den (core3Sem P) = c.den (core3Sem Q) := by
  rw [den_core3Sem_eq_of_obsEq _ _ h, den_core3Sem]; rfl

end Silmaril.Wasm.Abstract.InstStrat

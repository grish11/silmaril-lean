module

public import Silmaril.Wasm.Abstract.InstSessionD.Thms
public import Silmaril.Wasm.Component.Algebra.Equiv.Thms

public section

namespace Silmaril.Wasm.Abstract.InstSession

open Silmaril.Games.Abstract.StratThread (RoundEq ObsEq)
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Algebra Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

/-- Replace stores at a fixed numeric-instance interface. The obligation is one actual session
round at each related store: matched host traces, divergence, pending calls, productive streams,
and matched return stores (including the store after a Wasm trap). `ModuleEquiv` on its own
does not provide this invariant. -/
theorem denUD_core3SemD_eq_of_related_stores (oracle : GrowOracle)
    (replacement : NumInstance → Store Nat) (rel : NumInstance → Store Nat → Store Nat → Prop)
    (initial : ∀ m, rel m m.inst.store (replacement m))
    (rounds : ∀ m s t, rel m s t → RoundEq (instTripleS m.inst (profile oracle))
      (instTripleS m.inst (profile oracle)) (rel m) s t) (component : Comp NumInstance) :
    component.denUD (core3SemD (profile oracle)) =
      component.denUD (threadSemSD fun m => instSession m.inst (profile oracle) (replacement m)) :=
  denUD_core3SemD_eq_of_obsEq _ _ (fun m => ⟨rel m, rounds m, initial m⟩) component

/-- The same adapter preserves and reflects the existing finite-play component equivalence.
This is transport along equal sessions, not a new contextual congruence theorem. -/
theorem compEquiv_of_equal_replacement_sessions_iff (oracle : GrowOracle)
    (replacement : NumInstance → Store Nat)
    (rounds : ∀ m : NumInstance, ObsEq (instTripleS m.inst (profile oracle))
      (instTripleS m.inst (profile oracle)) m.inst.store (replacement m))
    (first second : Comp NumInstance) :
    CompEquiv (core3Sem (profile oracle)) first second ↔
      CompEquiv (threadSemS fun m => instSession m.inst (profile oracle) (replacement m)) first second := by
  rw [core3Sem_eq_threadSemS]
  have same := funext fun m => (instSession_eq_iff oracle oracle).mpr (rounds m)
  exact Iff.of_eq (congrArg (fun sessions => CompEquiv (threadSemS sessions) first second) same)

end Silmaril.Wasm.Abstract.InstSession

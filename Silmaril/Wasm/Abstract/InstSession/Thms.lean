module

public import Silmaril.Wasm.Abstract.InstSession.Defs
public import Silmaril.Games.Abstract.StratSession.Thms
public import Silmaril.Wasm.Game.Strategy.Thms
import Silmaril.Proofs.Wasm.Abstract.InstSession.Basic

/-!
# Scalar Core 3.0 instances as session play objects: theorems

**The triple.** The store-retaining instance triple has no plain traps
(`noPlainTrap_instTripleS`): every Wasm trap is a continuing trap `.ret (.inr ()) s'`, exactly a
run of the instance answering `.trap` and leaving `s'` (`mem_trap`). It is the `InstStrat`
triple with its answers relabelled by `sAns` (`instTripleS_eq`).

**The main theorem.** For every instance `I`, profile `P` (nondeterministic profiles included)
and store `s`, the finite plays of the session are exactly the relabelled plays of the instance
strategy:

* `mem_instSession`:
  `q ∈ (instSession I P s).toStrategy ↔ ∃ p ∈ I.strategy P s, p.map srelabel = q`;
* `map_srelabel_mem`: `p.map srelabel ∈ (instSession I P s).toStrategy ↔ p ∈ I.strategy P s`;
* `spull_instSession`: `spull (instSession I P s).toStrategy = I.strategy P s`.

It goes through `InstStrat`: the session plays are the images of the plays of
`InstStrat.instThread` under `relMove ∘ mapMove ansS` (`mem_instSession_iff_instThread`), and
that map after `InstStrat.relabel` is `srelabel`.

**Persistence.** The stores reachable in the session, through returns *and continuing traps*,
are the stores reachable by complete activations of the instance (`reach_iff_reachableStore`).

**Divergence and infinite plays** are those of `threadS`: images of the divergent and infinite
plays of `threadT (instTripleS I P) s`. At the deterministic profiles `profile o` the triple is
store-deterministic (`storeDet_instTripleS`), so the infinite plays are the productive streams
after completed session rounds and the plays of coherent infinite round sequences
(`mem_inf_instSession`). They are not compared with `I.strategy`, which exposes only finite
plays.

**The component level.** `core3Sem P` is the core semantics of the instance sessions
(`core3Sem_eq_threadSemS`), so `Comp.den (core3Sem P) c` sees each core module only through
`threadS (instTripleS m.inst P) m.inst.store` (`den_core3Sem_session`). Replacing every instance
triple by a bisimilar store-retaining triple (`den_core3Sem_eq_of_obsEq`), or by one agreeing
with it on the stores reachable from the instantiation store (`den_core3Sem_eq_of_reach`), does
not change any component denotation; nor does changing the profile when the triples of the two
profiles are bisimilar (`den_core3Sem_eq_of_obsEq_profile`).

**Exactness at deterministic profiles.** `instSession_eq_threadS_iff`: the session of `I` at
`profile o` from `s` equals the session of a store-deterministic triple without plain traps from
`s'` iff the two stores are bisimilar (`StratThread.ObsEq`). Bisimilarity, not pointwise
agreement on reachable stores: agreement is sufficient (`StratSession.threadS_congr`) but not
necessary (`StratThread.not_pointwise`).

Not claimed: component injectivity modulo an independent reference equivalence of components
(separate work), adequacy of the reference machine, correctness of the passage from bytes to
`Comp`.

Proofs are in `Silmaril.Proofs.Wasm.Abstract.InstSession.Basic`.
-/

public section

namespace Silmaril.Wasm.Abstract.InstSession

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
open Silmaril.Games.Abstract.StratThread (Reach StoreDet ObsEq Rounds InfRounds streamPlay)
open Silmaril.Games.Abstract.StratSession (threadS NoPlainTrap relMove sroundsMoves sroundsPlay)
open Silmaril.Wasm.Game Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Abstract.InstStrat (instTriple instThread)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Numerics (Profile)

/-- The session move map is injective. -/
theorem srelabel_injective {E : Sig.{0}} {ts : List FnType} :
    Function.Injective (srelabel (E := E) (ts := ts)) :=
  Silmaril.Proofs.Wasm.Abstract.InstSession.srelabel_injective

variable {I : ScalarInstance} {P : Profile}

/-! ## The triple -/

/-- **Every Wasm trap keeps its store**: the instance triple has no plain `End.trap`. -/
theorem noPlainTrap_instTripleS : NoPlainTrap (instTripleS I P) := by
  rintro s a c (⟨_, _, he, -⟩ | ⟨he, -⟩) <;> cases he

/-- A continuing trap of the triple is a run of the instance answering `.trap`. -/
theorem mem_trap {s s' : Store Nat} {a : I.F.Op} {c : List (Call I.E)} :
    (c, .ret (.inr PUnit.unit) s') ∈ (instTripleS I P).1 s a ↔
      I.Path P (.idle s) (.inr (.ask a) :: (callMoves c ++ [.inr (.ans a .trap)])) (.idle s') :=
  Silmaril.Proofs.Wasm.Abstract.InstSession.mem_trap

/-- **The store-retaining triple is the `InstStrat` triple with relabelled answers.** -/
theorem instTripleS_eq : instTripleS I P = mapAns ansS (instTriple I P) :=
  Silmaril.Proofs.Wasm.Abstract.InstSession.instTripleS_eq

/-! ## The plays of the session -/

/-- The session plays are the relabelled plays of the `InstStrat` threaded object. -/
theorem mem_instSession_iff_instThread {s : Store Nat} {q : List (Move I.E (ssig I.exports))} :
    q ∈ (instSession I P s).toStrategy ↔
      ∃ p ∈ (instThread I P s).toStrategy, p.map (relMove ∘ mapMove ansS) = q :=
  Silmaril.Proofs.Wasm.Abstract.InstSession.mem_instSession_iff

/-- **The plays of the session** are the relabelled plays of the instance, at every store and
profile. -/
theorem mem_instSession {s : Store Nat} {q : List (Move I.E (ssig I.exports))} :
    q ∈ (instSession I P s).toStrategy ↔ ∃ p ∈ I.strategy P s, p.map srelabel = q :=
  Silmaril.Proofs.Wasm.Abstract.InstSession.mem_instSession

/-- A relabelled play is a play of the session iff it is a play of the instance. -/
theorem map_srelabel_mem {s : Store Nat} {p : List (Move I.E I.F)} :
    p.map srelabel ∈ (instSession I P s).toStrategy ↔ p ∈ I.strategy P s :=
  Silmaril.Proofs.Wasm.Abstract.InstSession.map_srelabel_mem

/-- **The session read back on `I.F` is the instance strategy.** -/
theorem spull_instSession (s : Store Nat) : spull (instSession I P s).toStrategy = I.strategy P s :=
  Silmaril.Proofs.Wasm.Abstract.InstSession.spull_instSession s

/-- The stores reachable in the session (through returns and continuing traps) are those
reachable by complete activations. -/
theorem reach_iff_reachableStore {s₀ s : Store Nat} :
    Reach (instTripleS I P) s₀ s ↔ I.ReachableStore P s₀ s :=
  Silmaril.Proofs.Wasm.Abstract.InstSession.reach_iff_reachableStore

/-! ## Deterministic profiles -/

/-- **Store determinism** at the deterministic profiles. -/
theorem storeDet_instTripleS (o : GrowOracle) : StoreDet (instTripleS I (profile o)) :=
  Silmaril.Proofs.Wasm.Abstract.InstSession.storeDet_instTripleS o

/-- **The infinite plays of the session** at a deterministic profile: a productive stream after
completed session rounds, or the play of a coherent infinite sequence of session rounds. -/
theorem mem_inf_instSession (o : GrowOracle) {s₀ : Store Nat}
    {J : Set (List (Move I.E (ssig I.exports)))} :
    J ∈ (instSession I (profile o) s₀).inf ↔
      (∃ rs s a ω, Rounds (instTripleS I (profile o)) s₀ rs s ∧
        ω ∈ (instTripleS I (profile o)).2.2 s a ∧ J = streamPlay (sroundsMoves rs) a ω) ∨
      ∃ a r s, InfRounds (instTripleS I (profile o)) s₀ a r s ∧ J = sroundsPlay a r :=
  StratSession.mem_inf_iff_of_storeDet (storeDet_instTripleS o)

/-- **Equal sessions at a deterministic profile are exactly bisimilar stores**, against any
store-deterministic triple without plain traps. -/
theorem instSession_eq_threadS_iff (o : GrowOracle) {S' : Type}
    {t' : ObsTriple I.E S' I.F.Op (Res I.exports ⊕ PUnit)} (ht' : StoreDet t')
    (hn' : NoPlainTrap t') {s : Store Nat} {s' : S'} :
    instSession I (profile o) s = threadS t' s' ↔ ObsEq (instTripleS I (profile o)) t' s s' :=
  StratSession.threadS_eq_iff (storeDet_instTripleS o) ht' noPlainTrap_instTripleS hn'

/-- Two sessions of the instance at deterministic profiles are equal iff their stores are
bisimilar. -/
theorem instSession_eq_iff (o o' : GrowOracle) {s s' : Store Nat} :
    instSession I (profile o) s = instSession I (profile o') s' ↔
      ObsEq (instTripleS I (profile o)) (instTripleS I (profile o')) s s' :=
  instSession_eq_threadS_iff o (storeDet_instTripleS o') noPlainTrap_instTripleS

/-! ## The component level -/

/-- **`core3Sem P` is built from the instance sessions** at the instantiation stores. -/
theorem core3Sem_eq_threadSemS (P : Profile) :
    core3Sem P = threadSemS fun m => threadS (instTripleS m.inst P) m.inst.store := by
  unfold core3Sem threadSemS; congr 1; funext m
  show _ = semOfS m (instSession m.inst P m.inst.store)
  rw [semOfS, spull_instSession]

/-- Component denotations over Core 3.0 instances see each module only through its session. -/
theorem den_core3Sem_session (P : Profile) (c : Comp NumInstance) :
    c.den (core3Sem P) =
      c.den (threadSemS fun m => threadS (instTripleS m.inst P) m.inst.store) := by
  rw [← core3Sem_eq_threadSemS]

/-- **Bisimilar store-retaining triples give the same component denotations**: replacing the
instance triple of every module by a bisimilar one (on any store type). -/
theorem den_core3Sem_eq_of_obsEq {S' : NumInstance → Type}
    (t : (m : NumInstance) → ObsTriple m.inst.E (S' m) m.inst.F.Op (Res m.inst.exports ⊕ PUnit))
    (s' : (m : NumInstance) → S' m)
    (h : ∀ m, ObsEq (instTripleS m.inst P) (t m) m.inst.store (s' m))
    (c : Comp NumInstance) :
    c.den (core3Sem P) = c.den (threadSemS fun m => threadS (t m) (s' m)) := by
  rw [den_core3Sem_session]
  exact congrArg (fun T => c.den (threadSemS T))
    (funext fun m => StratSession.threadS_eq_of_obsEq (h m))

/-- **Triples agreeing on reachable stores give the same component denotations.** -/
theorem den_core3Sem_eq_of_reach
    (t : (m : NumInstance) →
      ObsTriple m.inst.E (Store Nat) m.inst.F.Op (Res m.inst.exports ⊕ PUnit))
    (h : ∀ m s, m.inst.ReachableStore P m.inst.store s →
      (instTripleS m.inst P).1 s = (t m).1 s ∧ satP (instTripleS m.inst P) s = satP (t m) s ∧
        (instTripleS m.inst P).2.2 s = (t m).2.2 s)
    (c : Comp NumInstance) :
    c.den (core3Sem P) = c.den (threadSemS fun m => threadS (t m) m.inst.store) := by
  rw [den_core3Sem_session]
  exact congrArg (fun T => c.den (threadSemS T)) (funext fun m =>
    StratSession.threadS_congr fun s hs => h m s (reach_iff_reachableStore.1 hs))

/-- Two profiles whose store-retaining instance triples are bisimilar at the instantiation stores
give the same component denotations. -/
theorem den_core3Sem_eq_of_obsEq_profile {Q : Profile}
    (h : ∀ m : NumInstance,
      ObsEq (instTripleS m.inst P) (instTripleS m.inst Q) m.inst.store m.inst.store)
    (c : Comp NumInstance) : c.den (core3Sem P) = c.den (core3Sem Q) := by
  rw [den_core3Sem_eq_of_obsEq _ _ h, den_core3Sem_session]

end Silmaril.Wasm.Abstract.InstSession

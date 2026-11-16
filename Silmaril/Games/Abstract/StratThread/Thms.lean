module

public import Silmaril.Games.Abstract.StratThread.Defs
public import Silmaril.Games.Abstract.StratOps.Thms
import Silmaril.Proofs.Games.Abstract.StratThread.Basic

/-!
# Threading a state-passing function: theorems

**Plays after completed rounds.** `roundsMoves rs` is a play of `threadT t s₀`
iff `Rounds t s₀ rs s` for some store `s` (`mem_rounds`): each round is a
finished returning behaviour of `t` at the previous store, ending in the next.
After the completed rounds `rs` ending at `s`:

* a trap round is a trapping behaviour at `s`, after which only one more
  Opponent question is possible (`mem_trap`);
* a play ending in a call is a call prefix `satP t s a` (`mem_pending`);
* a divergent play is a divergent behaviour at `s` (`mem_div`);
* an infinite play of the current round is a productive stream at `s`
  (`mem_inf`).

**Infinite plays.** For any triple, an infinite play of `threadT t s₀` is
either a productive stream after finitely many completed rounds, or the play
`roundsPlay a r` of an infinite sequence of rounds each of whose finite prefixes
is completed rounds from `s₀` (`mem_inf_iff`). This second form is a trace
limit: each prefix has *some* chain of stores, and these chains need not extend
one another. A coherent sequence (`InfRounds`, one store sequence through all
rounds) always gives an infinite play (`InfRounds.mem_inf`). For
store-deterministic triples the automaton state after a play is unique
(`TRun.det_of_storeDet`), so the stores cohere and the infinite plays are
exactly the stream plays and the plays of coherent sequences
(`exists_infRounds`, `mem_inf_iff_of_storeDet`). Without store determinism
coherence fails: a countdown store, which may start at any `n` and then counts
down to `0`, plays every finite number of identical rounds and hence their
infinite play, but no infinite sequence of rounds has coherent stores
(`not_coherent`).

The general forms `mem_append_rounds` and `div_append_rounds` split any play
after completed rounds. Reachability (`Reach`) is reachability by completed
rounds (`reach_iff`).

**Congruence.** Bisimilar stores thread to the same strategy
(`threadT_eq_of_obsEq`). In particular triples that agree on every store
reachable from `s₀` (same finished behaviours, call prefixes and productive
streams there) thread to the same strategy from `s₀` (`threadT_congr`).

**The converse.** Pointwise agreement on reachable stores is *not* necessary:
threading never shows the final store, so a function that keeps a boolean
store and one that flips it thread to the same strategy although they differ at
the reachable store `false` (`not_pointwise`). The right notion is
observational equivalence of stores, `ObsEq`, a bisimulation that also allows
the two triples to have different store types. For store-deterministic
triples (`StoreDet`: the final store of a return is determined by the visible
round) it is exact: `threadT t s = threadT t' s' ↔ ObsEq t t' s s'`
(`threadT_eq_iff`). No admissibility hypothesis is needed, because `RoundEq`
compares the call prefixes `satP`; for admissible triples these are the
pending components (`StratObs.saturated_iff`).

Without store determinism the converse of `threadT_eq_of_obsEq` fails in
general: threading is a trace semantics, and a return that may reach either of
two stores is indistinguishable from one reaching a single store with the
union of their futures, while no bisimulation relates them. This is not
formalised here.

Proofs are in `Silmaril.Proofs.Games.Abstract.StratThread.Basic`.
-/

public section

namespace Silmaril.Games.Abstract.StratThread

open Silmaril.Games Silmaril.Games.Abstract.StratObs

universe u

variable {E : Sig.{u}} {S A B : Type u} {t : ObsTriple E S A B} {s₀ : S}

/-- The finite plays are the runs of the automaton. -/
theorem mem_threadT {p : List (Move E (sig1 A B))} :
    p ∈ (threadT t s₀).toStrategy ↔ ∃ y, TRun t.1 (satP t) (.idle s₀) p y := Iff.rfl

/-! ## Plays after completed rounds -/

/-- A play after completed rounds is a play from their final store. -/
theorem mem_append_rounds {rs : List (A × List (Call E) × B)} {p : List (Move E (sig1 A B))} :
    roundsMoves rs ++ p ∈ (threadT t s₀).toStrategy ↔
      ∃ s, Rounds t s₀ rs s ∧ p ∈ (threadT t s).toStrategy :=
  Silmaril.Proofs.Games.Abstract.StratThread.mem_append_rounds

/-- A divergent play after completed rounds is divergent from their final store. -/
theorem div_append_rounds {rs : List (A × List (Call E) × B)} {p : List (Move E (sig1 A B))} :
    roundsMoves rs ++ p ∈ (threadT t s₀).div ↔ ∃ s, Rounds t s₀ rs s ∧ p ∈ (threadT t s).div :=
  Silmaril.Proofs.Games.Abstract.StratThread.div_append_rounds

/-- **Completed rounds** are finished returning behaviours chained through the stores. -/
theorem mem_rounds {rs : List (A × List (Call E) × B)} :
    roundsMoves rs ∈ (threadT t s₀).toStrategy ↔ ∃ s, Rounds t s₀ rs s :=
  Silmaril.Proofs.Games.Abstract.StratThread.mem_rounds

/-- One completed round is a returning behaviour. -/
theorem mem_roundMoves {a : A} {c : List (Call E)} {b : B} :
    roundMoves (a, c, b) ∈ (threadT t s₀).toStrategy ↔ ∃ s₁, (c, .ret b s₁) ∈ t.1 s₀ a :=
  Silmaril.Proofs.Games.Abstract.StratThread.mem_roundMoves

/-- **A trap ends the threading**: a trap round after completed rounds is a trapping
behaviour at their final store, and afterwards only an Opponent question follows. -/
theorem mem_trap {rs : List (A × List (Call E) × B)} {a : A} {c : List (Call E)}
    {u : List (Move E (sig1 A B))} :
    roundsMoves rs ++ (trapMoves a c ++ u) ∈ (threadT t s₀).toStrategy ↔
      (∃ s, Rounds t s₀ rs s ∧ (c, .trap) ∈ t.1 s a) ∧ (u = [] ∨ ∃ a', u = [.inr (.ask a')]) :=
  Silmaril.Proofs.Games.Abstract.StratThread.mem_trap

/-- **Plays ending in a call** after completed rounds are call prefixes at their final
store. -/
theorem mem_pending {rs : List (A × List (Call E) × B)} {a : A} {c : List (Call E)} {m : E.Op} :
    roundsMoves rs ++ .inr (.ask a) :: (callMoves c ++ [.inl (.ask m)]) ∈
      (threadT t s₀).toStrategy ↔ ∃ s, Rounds t s₀ rs s ∧ (c, m) ∈ satP t s a :=
  Silmaril.Proofs.Games.Abstract.StratThread.mem_pending

/-- **Divergent plays** after completed rounds are divergent behaviours at their final
store. -/
theorem mem_div {rs : List (A × List (Call E) × B)} {a : A} {c : List (Call E)} :
    roundsMoves rs ++ .inr (.ask a) :: callMoves c ∈ (threadT t s₀).div ↔
      ∃ s, Rounds t s₀ rs s ∧ (c, .div) ∈ t.1 s a :=
  Silmaril.Proofs.Games.Abstract.StratThread.mem_div

/-- A stream play is an infinite trace. -/
theorem isInfPlay_streamPlay (pre : List (Move E (sig1 A B))) (a : A) (ω : ℕ → Call E) :
    IsInfPlay (streamPlay pre a ω) :=
  Silmaril.Proofs.Games.Abstract.StratThread.isInfPlay_streamPlay pre a ω

/-- After a run to an idle store, a productive stream there gives an infinite play. -/
theorem streamPlay_mem {pre : List (Move E (sig1 A B))} {s : S} {a : A} {ω : ℕ → Call E}
    (hpre : TRun t.1 (satP t) (.idle s₀) pre (.idle s)) (hω : ω ∈ t.2.2 s a) :
    streamPlay pre a ω ∈ (threadT t s₀).inf :=
  Silmaril.Proofs.Games.Abstract.StratThread.streamPlay_mem hpre hω

/-- **Infinite plays of the current round** after completed rounds are productive streams
at their final store. -/
theorem mem_inf {rs : List (A × List (Call E) × B)} {a : A} {ω : ℕ → Call E} :
    streamPlay (roundsMoves rs) a ω ∈ (threadT t s₀).inf ↔
      ∃ s, Rounds t s₀ rs s ∧ ω ∈ t.2.2 s a :=
  Silmaril.Proofs.Games.Abstract.StratThread.mem_inf

/-! ## Infinite plays -/

/-- **Under store determinism the automaton state after a play is unique.** -/
theorem TRun.det_of_storeDet (ht : StoreDet t) {x y y' : TSt E S A}
    {p : List (Move E (sig1 A B))} (h : TRun t.1 (satP t) x p y)
    (h' : TRun t.1 (satP t) x p y') : y = y' :=
  Silmaril.Proofs.Games.Abstract.StratThread.trun_det ht h h'

/-- A play of rounds is an infinite play when every finite prefix of the rounds is completed
rounds (each from *some* chain of stores). -/
theorem roundsPlay_mem {a : ℕ → A} {r : ℕ → List (Call E) × B}
    (h : ∀ k, ∃ s, Rounds t s₀ (streamTake (fun i => (a i, r i)) k) s) :
    roundsPlay a r ∈ (threadT t s₀).inf :=
  Silmaril.Proofs.Games.Abstract.StratThread.roundsPlay_mem h

/-- The first `k` rounds of a coherent sequence are completed rounds ending at `s k`. -/
theorem InfRounds.rounds {a : ℕ → A} {r : ℕ → List (Call E) × B} {s : ℕ → S}
    (h : InfRounds t s₀ a r s) (k : ℕ) : Rounds t s₀ (streamTake (fun i => (a i, r i)) k) (s k) :=
  Silmaril.Proofs.Games.Abstract.StratThread.infRounds_rounds h k

/-- **Soundness**: a coherent infinite sequence of rounds is an infinite play. -/
theorem InfRounds.mem_inf {a : ℕ → A} {r : ℕ → List (Call E) × B} {s : ℕ → S}
    (h : InfRounds t s₀ a r s) : roundsPlay a r ∈ (threadT t s₀).inf :=
  roundsPlay_mem fun k => ⟨s k, h.rounds k⟩

/-- **The infinite plays** (no hypothesis on `t`): a productive stream after finitely many
completed rounds, or the play of rounds whose every finite prefix is completed rounds. The
stores of the prefixes need not cohere (`not_coherent`). -/
theorem mem_inf_iff {I : Set (List (Move E (sig1 A B)))} :
    I ∈ (threadT t s₀).inf ↔
      (∃ pre s a ω, TRun t.1 (satP t) (.idle s₀) pre (.idle s) ∧ ω ∈ t.2.2 s a ∧
        I = streamPlay pre a ω) ∨
      ∃ a r, I = roundsPlay a r ∧ ∀ k, ∃ s, Rounds t s₀ (streamTake (fun i => (a i, r i)) k) s :=
  Silmaril.Proofs.Games.Abstract.StratThread.mem_inf_iff

/-- **The converse under store determinism**: an infinite play completing infinitely many
rounds is the play of a coherent infinite sequence of rounds. -/
theorem exists_infRounds (ht : StoreDet t) {I : Set (List (Move E (sig1 A B)))}
    (hI : I ∈ (threadT t s₀).inf)
    (hk : ∀ p ∈ I, ∃ p' ∈ I, p <+: p' ∧ ∃ s, TRun t.1 (satP t) (.idle s₀) p' (.idle s)) :
    ∃ a r s, InfRounds t s₀ a r s ∧ I = roundsPlay a r :=
  Silmaril.Proofs.Games.Abstract.StratThread.exists_infRounds ht hI hk

/-- **The infinite plays of a store-deterministic triple**: a productive stream after finitely
many completed rounds, or the play of a coherent infinite sequence of rounds. -/
theorem mem_inf_iff_of_storeDet (ht : StoreDet t) {I : Set (List (Move E (sig1 A B)))} :
    I ∈ (threadT t s₀).inf ↔
      (∃ pre s a ω, TRun t.1 (satP t) (.idle s₀) pre (.idle s) ∧ ω ∈ t.2.2 s a ∧
        I = streamPlay pre a ω) ∨
      ∃ a r s, InfRounds t s₀ a r s ∧ I = roundsPlay a r :=
  Silmaril.Proofs.Games.Abstract.StratThread.mem_inf_iff_of_storeDet ht

/-- **Coherence fails without store determinism**: for a countdown (from `none` return to any
`some n`, from `some (n + 1)` return to `some n`) the play of infinitely many identical rounds
is an infinite play from `none`, but no infinite sequence of rounds has coherent stores. -/
theorem not_coherent {E : Sig.{0}} :
    ∃ (t : ObsTriple E (Option ℕ) PUnit PUnit) (a : ℕ → PUnit) (r : ℕ → List (Call E) × PUnit),
      roundsPlay a r ∈ (threadT t none).inf ∧ ∀ a' r' s, ¬ InfRounds t none a' r' s :=
  ⟨_, _, _, Silmaril.Proofs.Games.Abstract.StratThread.Counter.countdown_mem,
    fun _ _ _ => Silmaril.Proofs.Games.Abstract.StratThread.Counter.countdown_not_infRounds⟩

/-! ## Reachable stores -/

/-- Reachable stores are the final stores of completed rounds. -/
theorem reach_iff {s : S} : Reach t s₀ s ↔ ∃ rs, Rounds t s₀ rs s :=
  Silmaril.Proofs.Games.Abstract.StratThread.reach_iff

/-- One more returning round stays reachable. -/
theorem Reach.tail {s s₁ : S} {a : A} {c : List (Call E)} {b : B} (h : Reach t s₀ s)
    (hr : (c, .ret b s₁) ∈ t.1 s a) : Reach t s₀ s₁ :=
  Silmaril.Proofs.Games.Abstract.StratThread.reach_tail h hr

/-! ## Congruence -/

section Congr

variable {S' : Type u} {t' : ObsTriple E S' A B}

/-- Bisimulations are symmetric. -/
theorem IsBisim.flip {R : S → S' → Prop} (hR : IsBisim t t' R) :
    IsBisim t' t (fun s' s => R s s') :=
  Silmaril.Proofs.Games.Abstract.StratThread.isBisim_flip hR

/-- Equality of stores is a bisimulation of a triple with itself. -/
theorem isBisim_eq : IsBisim t t Eq := by
  rintro s _ rfl
  exact ⟨fun _ _ => .rfl, fun _ _ => .rfl, rfl, rfl, fun _ _ _ s₁ h => ⟨s₁, h, rfl⟩,
    fun _ _ _ s₁ h => ⟨s₁, h, rfl⟩⟩

/-- Observational equivalence is reflexive. -/
theorem ObsEq.refl (s : S) : ObsEq t t s s := ⟨Eq, isBisim_eq, rfl⟩

/-- Observational equivalence is symmetric. -/
theorem ObsEq.symm {s : S} {s' : S'} (h : ObsEq t t' s s') : ObsEq t' t s' s :=
  let ⟨_, hR, hs⟩ := h; ⟨_, hR.flip, hs⟩

/-- **Bisimilar stores thread to the same strategy.** -/
theorem threadT_eq_of_obsEq {s : S} {s' : S'} (h : ObsEq t t' s s') :
    threadT t s = threadT t' s' :=
  let ⟨_, hR, hs⟩ := h
  Silmaril.Proofs.Games.Abstract.StratThread.threadT_eq_of_isBisim hR hs

end Congr

/-- **Congruence on reachable stores**: triples with the same finished behaviours, call
prefixes and productive streams at every store reachable from `s₀` thread to the same
strategy from `s₀`. -/
theorem threadT_congr {t' : ObsTriple E S A B}
    (h : ∀ s, Reach t s₀ s → t.1 s = t'.1 s ∧ satP t s = satP t' s ∧ t.2.2 s = t'.2.2 s) :
    threadT t s₀ = threadT t' s₀ :=
  Silmaril.Proofs.Games.Abstract.StratThread.threadT_congr h

/-- **Pointwise agreement is not necessary**: a function keeping a boolean store and one
flipping it thread to the same strategy from `false`, but differ at the reachable store
`false`. -/
theorem not_pointwise {E : Sig.{0}} :
    ∃ t t' : ObsTriple E Bool PUnit PUnit, threadT t false = threadT t' false ∧
      ¬ ∀ s, Reach t false s → t.1 s = t'.1 s :=
  ⟨_, _, Silmaril.Proofs.Games.Abstract.StratThread.Counter.not_pointwise⟩

/-! ## The converse -/

/-- **For store-deterministic triples, threading identifies exactly the observationally
equivalent stores.** -/
theorem threadT_eq_iff {S' : Type u} {t' : ObsTriple E S' A B} (ht : StoreDet t)
    (ht' : StoreDet t') {s : S} {s' : S'} : threadT t s = threadT t' s' ↔ ObsEq t t' s s' :=
  ⟨fun h => ⟨fun s s' => threadT t s = threadT t' s',
      fun _ _ h => Silmaril.Proofs.Games.Abstract.StratThread.roundEq_of_eq ht ht' h, h⟩,
    threadT_eq_of_obsEq⟩

/-! ## Threading play objects -/

/-- Threading does not see saturation. -/
theorem threadT_sat (t : ObsTriple E S A B) (s₀ : S) : threadT (sat t) s₀ = threadT t s₀ := by
  have h : satP (sat t) = satP t := congrArg (fun t => t.2.1) (sat_idem (t := t))
  show build (sat t).1 (satP (sat t)) (sat t).2.2 s₀ = _
  rw [h]; rfl

/-- **The threading of a triple's play object is the threading of the triple.** -/
theorem thread_toDStrat (t : ObsTriple E S A B) (s₀ : S) : thread (toDStrat t) s₀ = threadT t s₀ := by
  rw [thread, StratOps.readback_toDStrat, threadT_sat]

end Silmaril.Games.Abstract.StratThread

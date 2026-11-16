module

public import Silmaril.Games.Abstract.StratThreadW.Defs
public import Silmaril.Games.Abstract.StratSession.Thms
import Silmaril.Proofs.Games.Abstract.StratThreadW.Basic

/-!
# Threading with coherent execution witnesses: theorems

**Same finite behaviour.** `threadW t s₀` has the finite plays and the divergent plays of
`threadT t s₀` (`threadW_toStrategy`, `threadW_div`). Its infinite plays are exactly a
productive stream after completed rounds, or the play of a coherent infinite sequence of rounds
with an explicit store sequence (`mem_inf_iff`); each is an infinite play of `threadT t s₀`
(`threadW_inf_subset`), so `threadW t s₀ ≤ threadT t s₀` (`threadW_le`).

**Agreement and strictness.** For store-deterministic triples, in particular triples
deterministic given answers, the two semantics agree (`threadW_eq_threadT_of_storeDet`,
`threadW_eq_threadT_of_det`). In general they differ: for the countdown triple of
`StratThread.not_coherent` the play of infinitely many identical rounds is an infinite play of
`threadT` but not of `threadW` (`exists_inf_not_witnessed`, `threadW_ne_threadT`).

**Congruence.** Bisimilar stores carry completed rounds and coherent round sequences to each
other, so they give the same witness threading (`threadW_eq_of_obsEq`). The converse is not
claimed.

**Sessions.** The same results hold for the session threading `threadSW` of store-retaining
triples against `StratSession.threadS`: `threadSW_toStrategy`, `threadSW_div`, `mem_sinf_iff`,
`threadSW_inf_subset`, `threadSW_eq_threadS_of_storeDet`, `threadSW_ne_threadS` and
`threadSW_eq_of_obsEq`.

Proofs are in `Silmaril.Proofs.Games.Abstract.StratThreadW.Basic`.
-/

public section

namespace Silmaril.Games.Abstract.StratThreadW

open Silmaril.Games Silmaril.Games.Abstract.StratObs Silmaril.Games.Abstract.StratThread
open Silmaril.Games.Abstract.StratSession

universe u

variable {E : Sig.{u}} {S A B : Type u}

/-! ## Store-erasing threading -/

section Thread

variable {t : ObsTriple E S A B} {s₀ : S}

/-- The finite plays are those of the trace-limit threading. -/
theorem threadW_toStrategy : (threadW t s₀).toStrategy = (threadT t s₀).toStrategy := rfl

/-- The divergent plays are those of the trace-limit threading. -/
theorem threadW_div : (threadW t s₀).div = (threadT t s₀).div := rfl

/-- **The infinite plays of the witness threading**: a productive stream after finitely many
completed rounds, or the play of a coherent infinite sequence of rounds. -/
theorem mem_inf_iff {I : Set (List (Move E (sig1 A B)))} :
    I ∈ (threadW t s₀).inf ↔
      (∃ rs s a ω, Rounds t s₀ rs s ∧ ω ∈ t.2.2 s a ∧ I = streamPlay (roundsMoves rs) a ω) ∨
      ∃ a r s, InfRounds t s₀ a r s ∧ I = roundsPlay a r :=
  Iff.rfl

/-- **Witnessed infinite plays are trace-limit infinite plays.** -/
theorem threadW_inf_subset : (threadW t s₀).inf ⊆ (threadT t s₀).inf := winfs_subset t s₀

/-- The witness threading refines the trace-limit threading. -/
theorem threadW_le : threadW t s₀ ≤ threadT t s₀ := ⟨le_rfl, subset_rfl, threadW_inf_subset⟩

/-- **For store-deterministic triples the witness threading is the trace-limit threading.** -/
theorem threadW_eq_threadT_of_storeDet (ht : StoreDet t) : threadW t s₀ = threadT t s₀ :=
  DStrategy.ext rfl rfl (Silmaril.Proofs.Games.Abstract.StratThreadW.winfs_eq_of_storeDet ht)

/-- For triples deterministic given answers the witness threading is the trace-limit
threading. -/
theorem threadW_eq_threadT_of_det (ht : AFun.Det t.1) : threadW t s₀ = threadT t s₀ :=
  threadW_eq_threadT_of_storeDet (storeDet_of_det ht)

/-- **Bisimilar stores give the same witness threading.** -/
theorem threadW_eq_of_obsEq {S' : Type u} {t' : ObsTriple E S' A B} {s : S} {s' : S'}
    (h : ObsEq t t' s s') : threadW t s = threadW t' s' :=
  DStrategy.ext (congrArg (·.toStrategy) (threadT_eq_of_obsEq h))
    (congrArg (·.div) (threadT_eq_of_obsEq h))
    (Silmaril.Proofs.Games.Abstract.StratThreadW.winfs_eq_of_obsEq h)

end Thread

/-- **A trace-limit infinite play with no witness**: for the countdown triple (from `none` return
to any `some n`, from `some (n + 1)` return to `some n`) the play of infinitely many identical
rounds is an infinite play of `threadT` from `none`, but not of `threadW`. -/
theorem exists_inf_not_witnessed {E : Sig.{0}} :
    ∃ (t : ObsTriple E (Option ℕ) PUnit PUnit) (a : ℕ → PUnit) (r : ℕ → List (Call E) × PUnit),
      roundsPlay a r ∈ (threadT t none).inf ∧ roundsPlay a r ∉ (threadW t none).inf :=
  ⟨_, _, _, Silmaril.Proofs.Games.Abstract.StratThreadW.Counter.countdown_mem (),
    Silmaril.Proofs.Games.Abstract.StratThreadW.Counter.not_mem_winfs_countdown ()⟩

/-- **The witness semantics differs from the trace-limit semantics** for nondeterministic
sources. -/
theorem threadW_ne_threadT {E : Sig.{0}} :
    ∃ (t : ObsTriple E (Option ℕ) PUnit PUnit) (s₀ : Option ℕ), threadW t s₀ ≠ threadT t s₀ :=
  let ⟨t, _, _, h₁, h₂⟩ := exists_inf_not_witnessed (E := E)
  ⟨t, none, fun h => h₂ (h ▸ h₁)⟩

/-! ## Session threading -/

section Session

variable {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})} {s₀ : S}

/-- The finite plays are those of the session threading. -/
theorem threadSW_toStrategy : (threadSW t s₀).toStrategy = (threadS t s₀).toStrategy := rfl

/-- The divergent plays are those of the session threading. -/
theorem threadSW_div : (threadSW t s₀).div = (threadS t s₀).div := rfl

/-- **The infinite plays of the witness session threading**: a productive stream after finitely
many completed session rounds, or the play of a coherent infinite sequence of session rounds. -/
theorem mem_sinf_iff {I : Set (List (Move E (sig1 A B)))} :
    I ∈ (threadSW t s₀).inf ↔
      (∃ rs s a ω, Rounds t s₀ rs s ∧ ω ∈ t.2.2 s a ∧ I = streamPlay (sroundsMoves rs) a ω) ∨
      ∃ a r s, InfRounds t s₀ a r s ∧ I = sroundsPlay a r :=
  Silmaril.Proofs.Games.Abstract.StratThreadW.mem_sinf_iff

/-- **Witnessed session infinite plays are trace-limit session infinite plays.** -/
theorem threadSW_inf_subset : (threadSW t s₀).inf ⊆ (threadS t s₀).inf := by
  rintro _ ⟨I, hI, rfl⟩
  exact ⟨I, winfs_subset t s₀ hI, rfl⟩

/-- The witness session threading refines the session threading. -/
theorem threadSW_le : threadSW t s₀ ≤ threadS t s₀ := ⟨le_rfl, subset_rfl, threadSW_inf_subset⟩

/-- **For store-deterministic triples the witness session threading is the session
threading.** -/
theorem threadSW_eq_threadS_of_storeDet (ht : StoreDet t) : threadSW t s₀ = threadS t s₀ :=
  congrArg relabel (threadW_eq_threadT_of_storeDet ht)

/-- For triples deterministic given answers the witness session threading is the session
threading. -/
theorem threadSW_eq_threadS_of_det (ht : AFun.Det t.1) : threadSW t s₀ = threadS t s₀ :=
  threadSW_eq_threadS_of_storeDet (storeDet_of_det ht)

/-- **Bisimilar stores give the same witness session threading.** -/
theorem threadSW_eq_of_obsEq {S' : Type u} {t' : ObsTriple E S' A (B ⊕ PUnit.{u + 1})} {s : S}
    {s' : S'} (h : ObsEq t t' s s') : threadSW t s = threadSW t' s' :=
  congrArg relabel (threadW_eq_of_obsEq h)

end Session

/-- **A trace-limit session infinite play with no witness**: the countdown returning `.inl ()`
plays infinitely many identical session rounds in `threadS` from `none`, but not in
`threadSW`. -/
theorem exists_sinf_not_witnessed {E : Sig.{0}} :
    ∃ (t : ObsTriple E (Option ℕ) PUnit (PUnit ⊕ PUnit)) (a : ℕ → PUnit)
      (r : ℕ → List (Call E) × (PUnit ⊕ PUnit)),
      sroundsPlay a r ∈ (threadS t none).inf ∧ sroundsPlay a r ∉ (threadSW t none).inf :=
  ⟨_, _, _, ⟨_, Silmaril.Proofs.Games.Abstract.StratThreadW.Counter.countdown_mem (Sum.inl ()),
      (Silmaril.Proofs.Games.Abstract.StratThreadW.image_roundsPlay _ _).symm⟩,
    fun ⟨_, hJ, _⟩ => Silmaril.Proofs.Games.Abstract.StratThreadW.Counter.not_mem_winfs_countdown
      (Sum.inl ()) hJ⟩

/-- **The witness session semantics differs from the trace-limit session semantics** for
nondeterministic sources. -/
theorem threadSW_ne_threadS {E : Sig.{0}} :
    ∃ (t : ObsTriple E (Option ℕ) PUnit (PUnit ⊕ PUnit)) (s₀ : Option ℕ),
      threadSW t s₀ ≠ threadS t s₀ :=
  let ⟨t, _, _, h₁, h₂⟩ := exists_sinf_not_witnessed (E := E)
  ⟨t, none, fun h => h₂ (h ▸ h₁)⟩

end Silmaril.Games.Abstract.StratThreadW

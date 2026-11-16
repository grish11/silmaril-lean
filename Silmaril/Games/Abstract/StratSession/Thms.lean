module

public import Silmaril.Games.Abstract.StratSession.Defs
public import Silmaril.Games.Abstract.StratThread.Thms
import Silmaril.Proofs.Games.Abstract.StratSession.Basic

/-!
# Sessions: theorems

`threadS t s₀` is `threadT t s₀` relabelled (`relabel`), so its plays are the images of the
plays of `threadT t s₀` under `relMove` (`mem_threadS`), and the results of `StratThread`
transfer.

**Completed rounds.** `sroundsMoves rs` is a play of `threadS t s₀` iff the session rounds `rs`
are completed rounds of `t` from `s₀` (`Rounds t s₀ rs s`, the stores chaining through returns
*and* continuing traps), or `rs` ends with a trap round that is a plain trap of `t` after
completed rounds (`mem_srounds`). Without plain traps only the first case occurs
(`mem_srounds_of_noPlainTrap`), and the second never occurs when the last round returns a value
(`mem_srounds_snoc_ret`).

**The key witness** (`mem_trap_ret`, `mem_trap_ret_nil`): the play ask `a`, trap, ask `a'`,
value `b` is a play of `threadS t s₀` iff `t` traps at `(s₀, a)` leaving some `s₁` and then
returns `b` at `(s₁, a')`. In `threadT (eraseTrap t) s₀` the trap ends the threading instead
(`StratThread.mem_trap`).

**Reachable stores** are the final stores of completed session rounds, including continuing
traps (`reach_iff`, `Reach.trap`).

**Congruence.** Bisimilar stores (`StratThread.ObsEq`, of the store-retaining triples) give the
same session (`threadS_eq_of_obsEq`); triples agreeing on the stores reachable from `s₀` give the
same session from `s₀` (`threadS_congr`). For store-deterministic triples without plain traps
this is exact (`threadS_eq_iff`). `NoPlainTrap` is needed for the converse: a plain trap and a
continuing trap to a store with no behaviour give the same session but are not bisimilar.

**Infinite plays.** A coherent infinite sequence of session rounds is an infinite play
(`InfRounds.mem_sinf`); for store-deterministic triples the infinite plays are exactly the
productive streams after completed rounds and the plays of coherent infinite round sequences
(`mem_inf_iff_of_storeDet`).

Proofs are in `Silmaril.Proofs.Games.Abstract.StratSession.Basic`.
-/

public section

namespace Silmaril.Games.Abstract.StratSession

open Silmaril.Games Silmaril.Games.Abstract.StratObs Silmaril.Games.Abstract.StratThread

universe u

variable {E : Sig.{u}} {S A B : Type u} {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})} {s₀ : S}

/-- The finite plays of a session are the relabelled plays of the threading. -/
theorem mem_threadS {q : List (Move E (sig1 A B))} :
    q ∈ (threadS t s₀).toStrategy ↔ ∃ p ∈ (threadT t s₀).toStrategy, p.map relMove = q :=
  Iff.rfl

/-! ## Completed rounds -/

/-- **Completed session rounds** are completed rounds of the store-retaining triple, the stores
chaining through continuing traps, or end with a plain trap. -/
theorem mem_srounds {rs : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))} :
    sroundsMoves rs ∈ (threadS t s₀).toStrategy ↔ (∃ s, Rounds t s₀ rs s) ∨
      ∃ rs' a c, rs = rs' ++ [(a, c, .inr PUnit.unit)] ∧
        ∃ s, Rounds t s₀ rs' s ∧ (c, .trap) ∈ t.1 s a :=
  Silmaril.Proofs.Games.Abstract.StratSession.mem_srounds

/-- **Completed session rounds without plain traps** are completed rounds. -/
theorem mem_srounds_of_noPlainTrap (ht : NoPlainTrap t)
    {rs : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))} :
    sroundsMoves rs ∈ (threadS t s₀).toStrategy ↔ ∃ s, Rounds t s₀ rs s :=
  mem_srounds.trans (or_iff_left fun ⟨_, _, _, _, _, _, h⟩ => ht _ _ _ h)

/-- Completed session rounds ending in a value are completed rounds. -/
theorem mem_srounds_snoc_ret {rs : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))} {a : A}
    {c : List (Call E)} {b : B} :
    sroundsMoves (rs ++ [(a, c, .inl b)]) ∈ (threadS t s₀).toStrategy ↔
      ∃ s, Rounds t s₀ (rs ++ [(a, c, .inl b)]) s :=
  Silmaril.Proofs.Games.Abstract.StratSession.mem_srounds_snoc_ret

/-- **The session continues after a trap**: a trap round at `a` then a value round at `a'` is a
play iff `t` traps at `(s₀, a)` leaving `s₁` and returns `b` at `(s₁, a')`. -/
theorem mem_trap_ret {a a' : A} {c₁ c₂ : List (Call E)} {b : B} :
    sroundMoves (a, c₁, .inr PUnit.unit) ++ sroundMoves (a', c₂, .inl b) ∈
        (threadS t s₀).toStrategy ↔
      ∃ s₁, (c₁, .ret (.inr PUnit.unit) s₁) ∈ t.1 s₀ a ∧ ∃ s₂, (c₂, .ret (.inl b) s₂) ∈ t.1 s₁ a' :=
  Silmaril.Proofs.Games.Abstract.StratSession.mem_trap_ret

/-- **The key witness**, without host calls: ask `a`, trap, ask `a'`, value `b`. -/
theorem mem_trap_ret_nil {a a' : A} {b : B} :
    ([.inr (.ask a), .inr (.ans a (.inr PUnit.unit)), .inr (.ask a'), .inr (.ans a' (.inl b))] :
        List (Move E (sig1 A B))) ∈ (threadS t s₀).toStrategy ↔
      ∃ s₁, ([], .ret (.inr PUnit.unit) s₁) ∈ t.1 s₀ a ∧ ∃ s₂, ([], .ret (.inl b) s₂) ∈ t.1 s₁ a' :=
  mem_trap_ret (c₁ := []) (c₂ := [])

/-! ## Reachable stores -/

/-- **Reachable stores** are the final stores of completed session rounds. -/
theorem reach_iff {s : S} :
    Reach t s₀ s ↔ ∃ rs, Rounds t s₀ rs s ∧ sroundsMoves rs ∈ (threadS t s₀).toStrategy :=
  ⟨fun h => let ⟨rs, hrs⟩ := StratThread.reach_iff.1 h; ⟨rs, hrs, mem_srounds.2 (.inl ⟨s, hrs⟩)⟩,
    fun ⟨rs, hrs, _⟩ => StratThread.reach_iff.2 ⟨rs, hrs⟩⟩

/-- A continuing trap leaves its store reachable. -/
theorem Reach.trap {s s₁ : S} {a : A} {c : List (Call E)} (h : Reach t s₀ s)
    (hr : (c, .ret (.inr PUnit.unit) s₁) ∈ t.1 s a) : Reach t s₀ s₁ :=
  h.tail hr

/-! ## Congruence -/

/-- **Bisimilar stores give the same session.** -/
theorem threadS_eq_of_obsEq {S' : Type u} {t' : ObsTriple E S' A (B ⊕ PUnit.{u + 1})} {s : S}
    {s' : S'} (h : ObsEq t t' s s') : threadS t s = threadS t' s' :=
  congrArg relabel (threadT_eq_of_obsEq h)

/-- **Congruence on reachable stores.** -/
theorem threadS_congr {t' : ObsTriple E S A (B ⊕ PUnit.{u + 1})}
    (h : ∀ s, Reach t s₀ s → t.1 s = t'.1 s ∧ satP t s = satP t' s ∧ t.2.2 s = t'.2.2 s) :
    threadS t s₀ = threadS t' s₀ :=
  congrArg relabel (threadT_congr h)

/-- **For store-deterministic triples without plain traps, sessions identify exactly the
observationally equivalent stores.** -/
theorem threadS_eq_iff {S' : Type u} {t' : ObsTriple E S' A (B ⊕ PUnit.{u + 1})}
    (ht : StoreDet t) (ht' : StoreDet t') (hn : NoPlainTrap t) (hn' : NoPlainTrap t') {s : S}
    {s' : S'} : threadS t s = threadS t' s' ↔ ObsEq t t' s s' :=
  ⟨fun h => (threadT_eq_iff ht ht').1
      (Silmaril.Proofs.Games.Abstract.StratSession.threadT_eq_of_threadS_eq hn hn' h),
    threadS_eq_of_obsEq⟩

/-! ## Infinite plays -/

/-- **A coherent infinite sequence of session rounds is an infinite play.** -/
theorem InfRounds.mem_sinf {a : ℕ → A} {r : ℕ → List (Call E) × (B ⊕ PUnit.{u + 1})}
    {s : ℕ → S} (h : InfRounds t s₀ a r s) : sroundsPlay a r ∈ (threadS t s₀).inf :=
  ⟨_, h.mem_inf, (Silmaril.Proofs.Games.Abstract.StratSession.image_roundsPlay a r).symm⟩

/-- **The infinite plays of a store-deterministic session**: a productive stream after completed
rounds, or the play of a coherent infinite sequence of session rounds. -/
theorem mem_inf_iff_of_storeDet (ht : StoreDet t) {I : Set (List (Move E (sig1 A B)))} :
    I ∈ (threadS t s₀).inf ↔
      (∃ rs s a ω, Rounds t s₀ rs s ∧ ω ∈ t.2.2 s a ∧ I = streamPlay (sroundsMoves rs) a ω) ∨
      ∃ a r s, InfRounds t s₀ a r s ∧ I = sroundsPlay a r :=
  Silmaril.Proofs.Games.Abstract.StratSession.mem_inf_iff_of_storeDet ht

end Silmaril.Games.Abstract.StratSession

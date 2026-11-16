module

public import Silmaril.Games.Abstract.StratThread.Defs

/-!
# Sessions: threading a function whose traps keep the store

`StratThread.threadT` threads a *store-erasing* source: a trap is `End.trap`,
which carries no store, so a trap ends the threading. That is not the session
semantics of Wasm, where a trap aborts only the current invocation: the store
persists, and the next call starts from the store the trap left.

**Store-retaining sources.** A source whose traps keep the store is a triple
`t : ObsTriple E S A (B ⊕ PUnit)`:

* `.ret (.inl b) s` returns `b`, leaving the store `s`;
* `.ret (.inr ()) s` traps, leaving the store `s`;
* a plain `.trap` traps with an unknown store;
* `.div` diverges.

`eraseTrap t : ObsTriple E S A B` forgets the stores of traps
(`.ret (.inr ()) s ↦ .trap`), keeping pending calls and productive streams; it
is the store-erasing source of `StratThread`.

**Session threading.** `threadS t s₀ : DStrategy E (sig1 A B)` runs `t`
repeatedly from `s₀`. A round that returns `.ret x s'` answers `x` (a value
`.inl b`, or a trap `.inr ()`), and the next round starts at `s'`: **the session
continues after a trap**. A plain `End.trap` round answers `.inr ()` and ends
the session, as in `threadT`, because its store is unknown. Divergence and
productive streams are as in `threadT`.

**Construction (the choice).** No new automaton: `threadS t s₀` is
`threadT t s₀`, a strategy on `sig1 A (B ⊕ PUnit)`, relabelled along the answer
map `merge : (B ⊕ PUnit) ⊕ PUnit → B ⊕ PUnit` that sends a returned `x` to `x`
and a plain trap to `.inr ()` (`relabel`). The plays, divergences and infinite
plays of `relabel σ` are the images of those of `σ` under `relMove`, which
changes only the answers to Opponent questions. So every result of
`StratThread` about rounds, reachability and bisimulation applies to the
store-retaining triple itself. The relabelling merges continuing traps with
plain traps; it is injective on the plays of a triple with no plain traps
(`NoPlainTrap`), which is what the converse `threadS_eq_iff` needs.

**Rounds.** A completed session round is `(a, c, x)` with `x : B ⊕ PUnit`; its
moves are `sroundMoves`. The completed rounds of `threadS t s₀` are
`StratThread.Rounds t s₀`, of the store-retaining triple, so the stores chain
through continuing traps. `sroundsPlay a r` is the infinite play of an infinite
sequence of session rounds.

Theorems in `Silmaril.Games.Abstract.StratSession.Thms`.
-/

@[expose] public section

namespace Silmaril.Games.Abstract.StratSession

open Silmaril.Games Silmaril.Games.Abstract.StratObs Silmaril.Games.Abstract.StratThread

universe u

variable {E : Sig.{u}} {S A B : Type u}

/-! ## Store-retaining triples -/

/-- Erase the store of a trap: `.ret (.inr ()) s ↦ .trap`. -/
def eraseEnd : End S (B ⊕ PUnit.{u + 1}) → End S B
  | .ret (.inl b) s => .ret b s
  | .ret (.inr _) _ => .trap
  | .trap => .trap
  | .div => .div

/-- **The store-erasing triple** of a store-retaining one: the stores of traps are forgotten;
logs, pending calls and productive streams are kept. -/
def eraseTrap (t : ObsTriple E S A (B ⊕ PUnit.{u + 1})) : ObsTriple E S A B :=
  (fun s a => (fun x => (x.1, eraseEnd x.2)) '' t.1 s a, t.2.1, t.2.2)

/-- A store-retaining triple with no plain traps: every trap keeps its store. -/
def NoPlainTrap (t : ObsTriple E S A (B ⊕ PUnit.{u + 1})) : Prop :=
  ∀ s a c, (c, End.trap) ∉ t.1 s a

/-! ## Relabelling answers -/

/-- The answer map: a returned `x` is the answer `x`, a plain trap is a trap. -/
def merge : (B ⊕ PUnit.{u + 1}) ⊕ PUnit.{u + 1} → B ⊕ PUnit.{u + 1}
  | .inl x => x
  | .inr _ => .inr PUnit.unit

/-- Relabel a move along `merge`; moves other than answers to Opponent questions are unchanged. -/
def relMove : Move E (sig1 A (B ⊕ PUnit.{u + 1})) → Move E (sig1 A B)
  | .inl e => .inl e
  | .inr (.ask a) => .inr (.ask a)
  | .inr (.ans a x) => .inr (.ans a (merge x))

/-- The same position, at the relabelled interface. -/
def relPos : Pos E (sig1 A (B ⊕ PUnit.{u + 1})) → Pos E (sig1 A B)
  | .idle => .idle
  | .run a => .run a
  | .wait a m => .wait a m

/-- Relabelling preserves steps. -/
theorem relStep {x y : Pos E (sig1 A (B ⊕ PUnit.{u + 1}))} {o : Move E (sig1 A (B ⊕ PUnit))}
    (h : Step x o y) : Step (relPos x) (relMove o) (relPos y) := by
  cases h <;> constructor

/-- Relabelling preserves paths. -/
theorem relPath {x y : Pos E (sig1 A (B ⊕ PUnit.{u + 1}))} {p : List (Move E (sig1 A (B ⊕ PUnit)))}
    (h : Path x p y) : Path (relPos x) (p.map relMove) (relPos y) := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (relStep h) ih

/-- Relabelling preserves infinite traces. -/
theorem isInfPlay_image {I : Set (List (Move E (sig1 A (B ⊕ PUnit.{u + 1}))))} (hI : IsInfPlay I) :
    IsInfPlay (List.map (relMove (E := E)) '' I) where
  of_prefix := by
    rintro s _ ⟨t, ht, rfl⟩ hs
    refine ⟨t.take s.length, hI.of_prefix ht (List.take_prefix _ _), ?_⟩
    rw [List.map_take]
    exact (List.prefix_iff_eq_take.1 hs).symm
  total := by
    rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
    rcases hI.total hs ht with h | h
    · exact .inl (h.map _)
    · exact .inr (h.map _)
  unbounded k := by
    obtain ⟨s, hs, hk⟩ := hI.unbounded k
    exact ⟨_, ⟨s, hs, rfl⟩, by simpa using hk⟩

/-- **Relabel a strategy along `merge`**: its plays, divergences and infinite plays are the
images under `relMove`. -/
def relabel (σ : DStrategy E (sig1 A (B ⊕ PUnit.{u + 1}))) : DStrategy E (sig1 A B) where
  toStrategy :=
    { plays := {q | ∃ p ∈ σ.toStrategy.plays, p.map relMove = q}
      nil_mem := ⟨[], σ.toStrategy.nil_mem, rfl⟩
      legal := by
        rintro _ ⟨p, hp, rfl⟩
        obtain ⟨y, hy⟩ := σ.toStrategy.legal hp
        exact ⟨_, relPath hy⟩
      of_prefix := by
        rintro s _ ⟨p, hp, rfl⟩ hs
        refine ⟨p.take s.length, σ.toStrategy.of_prefix hp (List.take_prefix _ _), ?_⟩
        rw [List.map_take]
        exact (List.prefix_iff_eq_take.1 hs).symm
      receptive := by
        rintro _ x y o ⟨p, hp, rfl⟩ hx hs ho
        obtain ⟨x₀, hx₀⟩ := σ.toStrategy.legal hp
        have hxx : relPos x₀ = x := Path.det (relPath hx₀) hx
        cases hs with
        | ask a =>
          cases x₀ <;> simp [relPos] at hxx
          exact ⟨_, σ.toStrategy.receptive hp hx₀
            (Step.ask (E := E) (F := sig1 A (B ⊕ PUnit)) a) trivial, by simp [relMove]⟩
        | reply a m n =>
          cases x₀ <;> simp [relPos] at hxx
          obtain ⟨rfl, rfl⟩ := hxx
          exact ⟨_, σ.toStrategy.receptive hp hx₀
            (Step.reply (E := E) (F := sig1 A (B ⊕ PUnit)) _ _ n) trivial, by simp [relMove]⟩
        | call => simp [Move.IsO] at ho
        | ret => simp [Move.IsO] at ho }
  div := {q | ∃ p ∈ σ.div, p.map relMove = q}
  inf := {J | ∃ I ∈ σ.inf, J = List.map relMove '' I}
  div_mem := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨p, σ.div_mem hp, rfl⟩
  div_run := by
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨a, ha⟩ := σ.div_run hp
    exact ⟨a, relPath ha⟩
  inf_isInf := by
    rintro _ ⟨I, hI, rfl⟩
    exact isInfPlay_image (σ.inf_isInf hI)
  inf_sub := by
    rintro _ ⟨I, hI, rfl⟩ _ ⟨p, hp, rfl⟩
    exact ⟨p, σ.inf_sub hI hp, rfl⟩

/-! ## Session threading -/

/-- **The session threading of a store-retaining triple from the store `s₀`**: a trap that keeps
its store continues the session from that store; a plain trap ends it. -/
def threadS (t : ObsTriple E S A (B ⊕ PUnit.{u + 1})) (s₀ : S) : DStrategy E (sig1 A B) :=
  relabel (threadT t s₀)

/-- The moves of a completed session round `(a, c, x)`: the question `a`, the calls `c`, and the
answer `x` (a value `.inl b` or a trap `.inr ()`). -/
def sroundMoves (r : A × List (Call E) × (B ⊕ PUnit.{u + 1})) : List (Move E (sig1 A B)) :=
  .inr (.ask r.1) :: (callMoves r.2.1 ++ [.inr (.ans r.1 r.2.2)])

/-- The moves of a sequence of completed session rounds. -/
def sroundsMoves (rs : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))) : List (Move E (sig1 A B)) :=
  rs.flatMap sroundMoves

/-- The infinite play of the session rounds `a`, `r`: the limit of the moves of their first `k`
rounds. -/
def sroundsPlay (a : ℕ → A) (r : ℕ → List (Call E) × (B ⊕ PUnit.{u + 1})) :
    Set (List (Move E (sig1 A B))) :=
  Chain.lim fun k => sroundsMoves (streamTake (fun i => (a i, r i)) k)

end Silmaril.Games.Abstract.StratSession

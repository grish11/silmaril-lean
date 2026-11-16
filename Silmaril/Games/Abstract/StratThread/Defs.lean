module

public import Silmaril.Games.Abstract.StratObs.Defs

/-!
# Threading a state-passing function into a persistent strategy

A function observed by a triple `t : ObsTriple E S A B` (`StratObs`) takes a
state and an argument and returns a result with a final state. Threading runs
it repeatedly on a *stateless* interface `sig1 A B`, where a question is an
argument and an answer is a result or a trap, and the store persists between
calls: round `k` is a round of `t` at question `(s_{k-1}, a_k)`, and round
`k + 1` starts at the final store `s_k` of round `k`.

**Plays.** A play of `threadT t s₀` is a sequence of rounds. Round `k` starts
with an Opponent question `a_k`, continues with the import calls of a
behaviour of `t` at `(s_{k-1}, a_k)` (each call `⟨m, n⟩` is a Proponent
`ask m` followed by the Opponent `ans m n`), and ends with a Proponent answer:

* a return `.ret b s_k` is shown as `.inl b`, and the next round starts at `s_k`;
* a trap is shown as `.inr ()`. **A trap ends the threading**: `End.trap`
  carries no store, so after the trap answer the strategy accepts Opponent
  questions (receptiveness) but never answers again.

The final store is not visible, so the automaton is nondeterministic: the same
answer `.inl b` may lead to several stores. The plays are the move lists with
*some* run.

**The automaton** (`TSt`, `TStep`, `TRun`) has states idle at a store, running
a question at a store after some calls, waiting for the answer to a call,
dead after a trap, and stuck on a question asked after a trap. Opponent moves
are always accepted, Proponent calls follow the call prefixes `satP t`, and
Proponent answers follow the finished behaviours, as in `StratObs`. Prefix
closure and receptiveness are structural.

**Divergence.** The plays with a run ending at `run s a c` with
`(c, .div) ∈ t.1 s a`.

**Infinite plays.** Infinite traces of plays of two kinds:

* finitely many completed rounds ending at a store `s`, then a question `a`
  and the calls of a productive stream `ω ∈ t.2.2 s a` (`streamPlay`);
* infinitely many completed rounds: every member extends, within the trace, to
  a member with a run ending idle. As in `StratObs` this is a limit condition
  on the trace; it does not ask for one coherent run of stores through the
  whole trace (for store-deterministic triples, `StoreDet`, runs are unique).

**Observational equivalence of stores.** Threading only sees a store through
its future observations. `RoundEq t t' R s s'` says one round at `s` (for `t`)
and at `s'` (for `t'`) has the same traps, divergences, call prefixes and
productive streams, and the same returns up to related final stores;
`ObsEq t t' s s'` is bisimilarity: some relation `R` that is a bisimulation
(`IsBisim`) relates `s` and `s'`. The theorems
(`Silmaril.Games.Abstract.StratThread.Thms`) show that bisimilar stores thread
to the same strategy, and that for store-deterministic triples this is exact.

**The DStrategy-level form.** For a play object `σ : DStrategy E (funSig S A
B)` the threading will be `threadT (readback σ) s₀`, with `readback` reading the
triple back from the plays; it is not defined here.
-/

@[expose] public section

namespace Silmaril.Games.Abstract

open Silmaril.Games

universe u

/-- The stateless interface of a function: a question is an argument, an
answer is a result or a trap. -/
abbrev sig1 (A B : Type u) : Sig.{u} := ⟨A, fun _ => B ⊕ PUnit⟩

namespace StratThread

open StratObs

variable {E : Sig.{u}} {S A B : Type u}

/-! ## Rounds and reachable stores -/

/-- `Rounds t s rs s'`: the returning rounds `rs` (argument, calls, result)
are finished behaviours of `t`, starting at the store `s` and ending at `s'`. -/
inductive Rounds (t : ObsTriple E S A B) : S → List (A × List (Call E) × B) → S → Prop
  | nil (s : S) : Rounds t s [] s
  | cons {s s₁ s₂ : S} {a : A} {c : List (Call E)} {b : B} {rs : List (A × List (Call E) × B)} :
      (c, .ret b s₁) ∈ t.1 s a → Rounds t s₁ rs s₂ → Rounds t s ((a, c, b) :: rs) s₂

/-- `Reach t s₀ s`: `s` is reachable from `s₀` by finitely many finished
returning rounds, at any arguments. -/
inductive Reach (t : ObsTriple E S A B) : S → S → Prop
  | refl (s : S) : Reach t s s
  | step {s s₁ s₂ : S} {a : A} {c : List (Call E)} {b : B} :
      (c, .ret b s₁) ∈ t.1 s a → Reach t s₁ s₂ → Reach t s s₂

/-- The moves of a completed returning round. -/
def roundMoves (r : A × List (Call E) × B) : List (Move E (sig1 A B)) :=
  .inr (.ask r.1) :: (callMoves r.2.1 ++ [.inr (.ans r.1 (.inl r.2.2))])

/-- The moves of a sequence of completed returning rounds. -/
def roundsMoves (rs : List (A × List (Call E) × B)) : List (Move E (sig1 A B)) :=
  rs.flatMap roundMoves

/-- The moves of a round at `a` with the calls `c` ending in a trap. -/
def trapMoves (a : A) (c : List (Call E)) : List (Move E (sig1 A B)) :=
  .inr (.ask a) :: (callMoves c ++ [.inr (.ans a (.inr PUnit.unit))])

/-- Store determinism: the final store of a return is determined by the
initial store, the argument, the calls and the result. -/
def StoreDet (t : ObsTriple E S A B) : Prop :=
  ∀ s a c b s₁ s₂, (c, .ret b s₁) ∈ t.1 s a → (c, .ret b s₂) ∈ t.1 s a → s₁ = s₂

/-! ## The automaton -/

/-- States of the threading automaton: idle at a store, running the argument
`a` at store `s` after the calls `c`, waiting for the answer to the call `m`,
dead after a trap, or stuck on a question asked after a trap. -/
inductive TSt (E : Sig.{u}) (S A : Type u) : Type u
  | idle (s : S)
  | run (s : S) (a : A) (c : List (Call E))
  | wait (s : S) (a : A) (c : List (Call E)) (m : E.Op)
  | dead
  | stuck (a : A)

/-- The game position of a state. -/
def TSt.pos {B : Type u} : TSt E S A → Pos E (sig1 A B)
  | .idle _ => .idle
  | .run _ a _ => .run a
  | .wait _ a _ m => .wait a m
  | .dead => .idle
  | .stuck a => .run a

/-- One move of the automaton for finished behaviours `f` and call prefixes
`P`. -/
inductive TStep (f : AFun E S A B) (P : Pending E S A) :
    TSt E S A → Move E (sig1 A B) → TSt E S A → Prop
  /-- Opponent asks `a`. -/
  | ask (s : S) (a : A) : TStep f P (.idle s) (.inr (.ask a)) (.run s a [])
  /-- Proponent calls `m` after the calls `c`. -/
  | call (s : S) (a : A) (c : List (Call E)) (m : E.Op) :
      (c, m) ∈ P s a → TStep f P (.run s a c) (.inl (.ask m)) (.wait s a c m)
  /-- Opponent answers the call `m` with any `n`. -/
  | reply (s : S) (a : A) (c : List (Call E)) (m : E.Op) (n : E.Ar m) :
      TStep f P (.wait s a c m) (.inl (.ans m n)) (.run s a (c ++ [⟨m, n⟩]))
  /-- Proponent returns `b`; the next round starts at `s'`. -/
  | ret (s : S) (a : A) (c : List (Call E)) (b : B) (s' : S) :
      (c, .ret b s') ∈ f s a → TStep f P (.run s a c) (.inr (.ans a (.inl b))) (.idle s')
  /-- Proponent traps; the threading ends. -/
  | trap (s : S) (a : A) (c : List (Call E)) :
      (c, .trap) ∈ f s a → TStep f P (.run s a c) (.inr (.ans a (.inr PUnit.unit))) .dead
  /-- After a trap, Opponent may still ask. -/
  | deadAsk (a : A) : TStep f P .dead (.inr (.ask a)) (.stuck a)

/-- Runs of the automaton. -/
inductive TRun (f : AFun E S A B) (P : Pending E S A) :
    TSt E S A → List (Move E (sig1 A B)) → TSt E S A → Prop
  | nil (x : TSt E S A) : TRun f P x [] x
  | cons {x y z : TSt E S A} {o : Move E (sig1 A B)} {s : List (Move E (sig1 A B))} :
      TStep f P x o y → TRun f P y s z → TRun f P x (o :: s) z

/-! ## Basic facts

Stated with the definitions because the strategy below needs them in its
proof fields.
-/

section Basic

variable {f : AFun E S A B} {P : Pending E S A}

/-- Automaton steps are game steps. -/
theorem TStep.pos {x y : TSt E S A} {o : Move E (sig1 A B)} (h : TStep f P x o y) :
    Step x.pos o y.pos := by
  cases h <;> constructor

/-- Automaton runs are game paths. -/
theorem TRun.pos {x y : TSt E S A} {s : List (Move E (sig1 A B))} (h : TRun f P x s y) :
    Path x.pos s y.pos := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons h.pos ih

/-- Runs compose along concatenation. -/
theorem TRun.append {x y z : TSt E S A} {s u : List (Move E (sig1 A B))}
    (h₁ : TRun f P x s y) (h₂ : TRun f P y u z) : TRun f P x (s ++ u) z := by
  induction h₁ with
  | nil => exact h₂
  | cons h _ ih => exact .cons h (ih h₂)

/-- A run through `s ++ u` passes through some state after `s`. -/
theorem TRun.of_append {x z : TSt E S A} {s u : List (Move E (sig1 A B))}
    (h : TRun f P x (s ++ u) z) : ∃ y, TRun f P x s y ∧ TRun f P y u z := by
  induction s generalizing x with
  | nil => exact ⟨x, .nil x, h⟩
  | cons o s ih =>
    cases h with
    | cons h hr => obtain ⟨y, h₁, h₂⟩ := ih hr; exact ⟨y, .cons h h₁, h₂⟩

/-- Every legal Opponent move is accepted. -/
theorem TRun.receptive {x₀ y : TSt E S A} {s : List (Move E (sig1 A B))}
    {x x' : Pos E (sig1 A B)} {o : Move E (sig1 A B)} (h : TRun f P x₀ s y)
    (hx : Path x₀.pos s x) (hs : Step x o x') (ho : o.IsO) : ∃ z, TRun f P x₀ (s ++ [o]) z := by
  have hy : y.pos = x := Path.det h.pos hx
  cases hs with
  | ask a =>
    cases y <;> simp [TSt.pos] at hy
    · exact ⟨_, h.append (.cons (.ask _ a) (.nil _))⟩
    · exact ⟨_, h.append (.cons (.deadAsk a) (.nil _))⟩
  | reply a m n =>
    cases y <;> simp [TSt.pos] at hy
    obtain ⟨rfl, rfl⟩ := hy
    exact ⟨_, h.append (.cons (.reply _ _ _ _ n) (.nil _))⟩
  | call => simp [Move.IsO] at ho
  | ret => simp [Move.IsO] at ho

end Basic

/-! ## The strategy -/

/-- The finite plays: the moves the automaton accepts from idle at `s₀`. -/
def plays (f : AFun E S A B) (P : Pending E S A) (s₀ : S) : Set (List (Move E (sig1 A B))) :=
  {p | ∃ y, TRun f P (.idle s₀) p y}

/-- The divergent plays: those with a run reaching `run s a c` with
`(c, .div)` a behaviour at `(s, a)`. -/
def divs (f : AFun E S A B) (P : Pending E S A) (s₀ : S) : Set (List (Move E (sig1 A B))) :=
  {p | ∃ s a c, TRun f P (.idle s₀) p (.run s a c) ∧ (c, .div) ∈ f s a}

/-- The infinite play of the rounds `pre`, then the question `a` and the calls
of the stream `ω`. -/
def streamPlay (pre : List (Move E (sig1 A B))) (a : A) (ω : ℕ → Call E) :
    Set (List (Move E (sig1 A B))) :=
  {p | ∃ k, p <+: pre ++ .inr (.ask a) :: callMoves (streamTake ω k)}

/-- The infinite plays: infinite traces of plays that end in a productive
stream after finitely many completed rounds, or that complete infinitely many
rounds. -/
def infs (f : AFun E S A B) (P : Pending E S A) (Q : PInf E S A) (s₀ : S) :
    Set (Set (List (Move E (sig1 A B)))) :=
  {I | IsInfPlay I ∧ I ⊆ plays f P s₀ ∧
    ((∃ pre s a ω, TRun f P (.idle s₀) pre (.idle s) ∧ ω ∈ Q s a ∧ I = streamPlay pre a ω) ∨
      ∀ p ∈ I, ∃ p' ∈ I, p <+: p' ∧ ∃ s, TRun f P (.idle s₀) p' (.idle s))}

/-- The strategy of finished behaviours `f` and call prefixes `P` from `s₀`. -/
def strat (f : AFun E S A B) (P : Pending E S A) (s₀ : S) : Strategy E (sig1 A B) where
  plays := plays f P s₀
  nil_mem := ⟨_, .nil _⟩
  legal := fun ⟨_, h⟩ => ⟨_, h.pos⟩
  of_prefix := by
    rintro s t ⟨y, h⟩ ⟨u, rfl⟩
    obtain ⟨z, hz, -⟩ := h.of_append
    exact ⟨z, hz⟩
  receptive := fun ⟨_, h⟩ hx hs ho => h.receptive hx hs ho

/-- The divergence-observing strategy of finished behaviours `f`, call
prefixes `P` and productive runs `Q`, threaded from `s₀`. -/
def build (f : AFun E S A B) (P : Pending E S A) (Q : PInf E S A) (s₀ : S) :
    DStrategy E (sig1 A B) where
  toStrategy := strat f P s₀
  div := divs f P s₀
  inf := infs f P Q s₀
  div_mem := fun ⟨_, _, _, h, _⟩ => ⟨_, h⟩
  div_run := fun ⟨_, a, _, h, _⟩ => ⟨a, h.pos⟩
  inf_isInf h := h.1
  inf_sub h := h.2.1

/-- **The threading of a triple from the store `s₀`.** -/
def threadT (t : ObsTriple E S A B) (s₀ : S) : DStrategy E (sig1 A B) :=
  build t.1 (satP t) t.2.2 s₀

/-! ## Observational equivalence of stores -/

/-- One round of `t` at `s` and of `t'` at `s'` agree, with final stores of
returns related by `R`. -/
structure RoundEq {S' : Type u} (t : ObsTriple E S A B) (t' : ObsTriple E S' A B)
    (R : S → S' → Prop) (s : S) (s' : S') : Prop where
  /-- The same trapping behaviours. -/
  trap : ∀ a c, (c, End.trap) ∈ t.1 s a ↔ (c, End.trap) ∈ t'.1 s' a
  /-- The same divergent behaviours. -/
  div : ∀ a c, (c, End.div) ∈ t.1 s a ↔ (c, End.div) ∈ t'.1 s' a
  /-- The same call prefixes. -/
  pend : satP t s = satP t' s'
  /-- The same productive streams. -/
  inf : t.2.2 s = t'.2.2 s'
  /-- Every return of `t` is matched by `t'` with a related final store. -/
  ret : ∀ a c b s₁, (c, End.ret b s₁) ∈ t.1 s a → ∃ s₁', (c, End.ret b s₁') ∈ t'.1 s' a ∧ R s₁ s₁'
  /-- Every return of `t'` is matched by `t` with a related final store. -/
  ret' : ∀ a c b s₁', (c, End.ret b s₁') ∈ t'.1 s' a → ∃ s₁, (c, End.ret b s₁) ∈ t.1 s a ∧ R s₁ s₁'

/-- A bisimulation between the stores of `t` and of `t'`. -/
def IsBisim {S' : Type u} (t : ObsTriple E S A B) (t' : ObsTriple E S' A B)
    (R : S → S' → Prop) : Prop :=
  ∀ s s', R s s' → RoundEq t t' R s s'

/-- **Observational equivalence of stores**: bisimilarity. -/
def ObsEq {S' : Type u} (t : ObsTriple E S A B) (t' : ObsTriple E S' A B) (s : S) (s' : S') :
    Prop :=
  ∃ R, IsBisim t t' R ∧ R s s'

end StratThread

end Silmaril.Games.Abstract

module

public import Silmaril.Games.Abstract.SessionLegal.Defs
public import Silmaril.Games.Abstract.StratSession.Thms
import Silmaril.Proofs.Games.Abstract.SessionLegal.Basic

/-!
# Store-dependent legality of import answers in a session: theorems

For a store-retaining triple `t`, a prefix-closed log legality `Lg`, and the legal part
`restrictLog Lg t`:

* `satP_restrictLog`: the call prefixes of the legal part are the legal call prefixes of `t`.
* `threadS_restrictLog_le`: the legal session refines the session (no hypothesis on `t`).

**The legal session is the exact legal pullback of the session**, for a store-deterministic `t`
without plain traps (`StoreDet t`, `NoPlainTrap t`; the Wasm instance triples have both), on
all three observations of a `DStrategy`:

* `mem_threadS_restrictLog` (finite plays): `q` is a play of `threadS (restrictLog Lg t) s₀`
  iff it is a play of `threadS t s₀` and Proponent-legal (`PLegal`). Plays ending in a call
  (pending calls) are among them; `mem_pending_restrictLog` reads them as rounds.
* `div_threadS_restrictLog` (divergences): iff a divergence of `threadS t s₀` that is legal up
  to its end (`SLegal`).
* `inf_threadS_restrictLog` (infinite plays): iff an infinite play of `threadS t s₀` all of whose
  finite prefixes are Proponent-legal.

Store determinism is used once: the automaton state after a play, hence the store at which the
round was asked, is unique (`StratThread.TRun.det_of_storeDet`), so a legal run of the legal
part makes **every** run of `t` legal. The backward directions need no hypothesis on `t`.

**Injectivity** (`threadS_restrictLog_eq_iff`): the legal part keeps store determinism and the
absence of plain traps, so legal sessions identify exactly the observationally equivalent stores
of the legal parts (`StratThread.ObsEq`), by `StratSession.threadS_eq_iff`.
-/

public section

namespace Silmaril.Games.Abstract.SessionLegal

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
open Silmaril.Games.Abstract.StratThread Silmaril.Games.Abstract.StratSession

universe u

variable {E : Sig.{u}} {S A B : Type u} {Lg : S → A → List (Call E) → Prop}

/-- **The call prefixes of the legal part are the legal call prefixes.** -/
theorem satP_restrictLog {t : ObsTriple E S A B} (hL : PrefixClosed Lg) (s : S) (a : A) :
    satP (restrictLog Lg t) s a = {x | x ∈ satP t s a ∧ Lg s a x.1} :=
  Silmaril.Proofs.Games.Abstract.SessionLegal.satP_restrictLog hL s a

/-- The first `k + 1` calls of a stream. -/
theorem streamTake_succ {α : Type u} (ω : ℕ → α) (k : ℕ) :
    streamTake ω (k + 1) = streamTake ω k ++ [ω k] :=
  Silmaril.Proofs.Games.Abstract.SessionLegal.streamTake_succ ω k

/-- Call prefixes are closed under call prefixes. -/
theorem satP_of_callPre {t : ObsTriple E S A B} {s : S} {a : A} {x : List (Call E) × E.Op}
    {d : List (Call E)} {m' : E.Op} (hd : (d, m') ∈ satP t s a) (hp : CallPre x.1 x.2 d) :
    x ∈ satP t s a :=
  Silmaril.Proofs.Games.Abstract.SessionLegal.satP_satP hd hp

variable {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})} {s₀ : S}

/-- **The legal session refines the session.** -/
theorem threadS_restrictLog_le (hL : PrefixClosed Lg) :
    threadS (restrictLog Lg t) s₀ ≤ threadS t s₀ :=
  Silmaril.Proofs.Games.Abstract.SessionLegal.threadS_restrictLog_le hL

/-- **Finite plays of the legal session**: the Proponent-legal plays of the session. -/
theorem mem_threadS_restrictLog (hd : StoreDet t) (hn : NoPlainTrap t) (hL : PrefixClosed Lg)
    {q : List (Move E (sig1 A B))} :
    q ∈ (threadS (restrictLog Lg t) s₀).toStrategy ↔
      q ∈ (threadS t s₀).toStrategy ∧ PLegal Lg t s₀ q :=
  Silmaril.Proofs.Games.Abstract.SessionLegal.mem_threadS_restrictLog hd hn hL

/-- **Divergences of the legal session**: the divergences of the session legal up to their end. -/
theorem div_threadS_restrictLog (hd : StoreDet t) (hn : NoPlainTrap t) (hL : PrefixClosed Lg)
    {q : List (Move E (sig1 A B))} :
    q ∈ (threadS (restrictLog Lg t) s₀).div ↔ q ∈ (threadS t s₀).div ∧ SLegal Lg t s₀ q :=
  Silmaril.Proofs.Games.Abstract.SessionLegal.div_threadS_restrictLog hd hn hL

/-- **Infinite plays of the legal session**: the infinite plays of the session whose finite
prefixes are all Proponent-legal. -/
theorem inf_threadS_restrictLog (hd : StoreDet t) (hn : NoPlainTrap t) (hL : PrefixClosed Lg)
    {J : Set (List (Move E (sig1 A B)))} :
    J ∈ (threadS (restrictLog Lg t) s₀).inf ↔
      J ∈ (threadS t s₀).inf ∧ ∀ q ∈ J, PLegal Lg t s₀ q :=
  Silmaril.Proofs.Games.Abstract.SessionLegal.inf_threadS_restrictLog hd hn hL

/-- **A play ending in a Proponent move (a call or an answer) is Proponent-legal iff the play
before it is legal, its end included.** -/
theorem pLegal_snoc {q : List (Move E (sig1 A B))} {o : Move E (sig1 A B)} (ho : o.IsP) :
    PLegal Lg t s₀ (q ++ [o]) ↔ SLegal Lg t s₀ q :=
  Silmaril.Proofs.Games.Abstract.SessionLegal.pLegal_snoc ho

/-- **Pending calls of the legal session**, read as rounds: after completed legal rounds, a call
prefix of `t` after a legal log at the current store. -/
theorem mem_pending_restrictLog (hL : PrefixClosed Lg)
    {rs : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))} {a : A} {c : List (Call E)}
    {m : E.Op} :
    sroundsMoves rs ++ .inr (.ask a) :: (callMoves c ++ [.inl (.ask m)]) ∈
        (threadS (restrictLog Lg t) s₀).toStrategy ↔
      ∃ s, Rounds (restrictLog Lg t) s₀ rs s ∧ (c, m) ∈ satP t s a ∧ Lg s a c := by
  rw [StratSession.mem_pending]
  simp only [satP_restrictLog hL]
  rfl

/-! ## Injectivity of the legal session -/

/-- The legal part of a store-deterministic triple is store-deterministic. -/
theorem storeDet_restrictLog (hd : StoreDet t) : StoreDet (restrictLog Lg t) :=
  fun s a c b _ _ h₁ h₂ => hd s a c b _ _ h₁.1 h₂.1

/-- The legal part of a triple without plain traps has none. -/
theorem noPlainTrap_restrictLog (hn : NoPlainTrap t) : NoPlainTrap (restrictLog Lg t) :=
  fun s a c h => hn s a c h.1

/-- **Legal sessions identify exactly the observationally equivalent stores of the legal parts**
(store-deterministic triples without plain traps). -/
theorem threadS_restrictLog_eq_iff {S' : Type u} {t' : ObsTriple E S' A (B ⊕ PUnit.{u + 1})}
    {Lg' : S' → A → List (Call E) → Prop} (hd : StoreDet t) (hd' : StoreDet t')
    (hn : NoPlainTrap t) (hn' : NoPlainTrap t') {s : S} {s' : S'} :
    threadS (restrictLog Lg t) s = threadS (restrictLog Lg' t') s' ↔
      ObsEq (restrictLog Lg t) (restrictLog Lg' t') s s' :=
  StratSession.threadS_eq_iff (storeDet_restrictLog hd) (storeDet_restrictLog hd')
    (noPlainTrap_restrictLog hn) (noPlainTrap_restrictLog hn')

end Silmaril.Games.Abstract.SessionLegal

module

public import Silmaril.Wasm.Abstract.NodeTrap.Defs
public import Silmaril.Wasm.Game.Trapped.Thms
public import Silmaril.Wasm.SingleThreaded.Soundness

/-!
# Core 3.0 instance rounds abort on an import trap (proofs)

**Trapped threads.** A thread `.active fr (E.fill [.trap])` is trapped. A host-free step from it
keeps the store and the frame, stays trapped and decreases the size of the code
(`internalP_trapped`, from `trapped_step` and `trapped_step_lt`). So every host-free run from it
stays trapped in the same store (`reach_trapped`), and none is infinite
(`not_diverges_trapped`). A trapped thread is at no callout (`Ctx.decompose?_fill_trap`) and
finishes only with a trap (`trapped_eq_toAdmin`). Hence the only move of the instance from a
running trapped thread is the trap answer to the current export question (`trans_trapped`).

**Trapped calls.** An import call answered by a trap resumes the thread stopped at the callout
with `TRAP` in the callout context: the thread is trapped (`trans_ans_trap`). The four parts of
`TrapAbortsRound` follow by cutting the instance paths at the trapped call.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.NodeTrap

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
open Silmaril.Games.Abstract.SessionTrap
open Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Abstract.InstStrat (Diverges instPend instInf)
open Silmaril.Wasm.Abstract.InstSession
open Silmaril.Wasm.Abstract.NodeTrap
open Silmaril.Wasm.Numerics (Profile)

variable {P : Profile}

/-! ## Trapped threads -/

/-- A host-free step of a trapped thread keeps the store and the frame, stays trapped and
decreases the size of the code. -/
theorem internalP_trapped {s : Store Nat} {fr : Frame} {E : Ctx} {y : Store Nat × Thread}
    (h : InternalP P (s, .active fr (E.fill [.trap])) y) :
    y.1 = s ∧ ∃ E' : Ctx, y.2 = .active fr (E'.fill [.trap]) ∧
      sizeOf (E'.fill [.trap]) < sizeOf (E.fill [.trap]) := by
  obtain ⟨f', code', hy, hst⟩ := h
  have hst' : Step P Det.noHost ⟨s, fr, E.fill [.trap]⟩ ⟨y.1, f', code'⟩ := hst
  have hlt := trapped_step_lt hst'
  obtain ⟨hs, hf, E', hc⟩ := trapped_step hst'
  change y.1 = s at hs
  change f' = fr at hf
  change code' = E'.fill [.trap] at hc
  change sizeOf code' < _ at hlt
  subst hf hc
  exact ⟨hs, E', hy, hlt⟩

/-- A host-free run of a trapped thread stays trapped, in the same store and frame. -/
theorem reach_trapped {s : Store Nat} {fr : Frame} {E : Ctx} {y : Store Nat × Thread}
    (h : Reach P (s, .active fr (E.fill [.trap])) y) :
    y.1 = s ∧ ∃ E' : Ctx, y.2 = .active fr (E'.fill [.trap]) := by
  induction h with
  | refl => exact ⟨rfl, E, rfl⟩
  | @tail b c _ hbc ih =>
    obtain ⟨hs, E', hE'⟩ := ih
    obtain ⟨b₁, b₂⟩ := b
    change b₁ = s at hs
    change b₂ = _ at hE'
    subst hs hE'
    obtain ⟨hs', E'', hE'', -⟩ := internalP_trapped hbc
    exact ⟨hs', E'', hE''⟩

/-- A trapped thread does not diverge. -/
theorem not_diverges_trapped {s : Store Nat} {fr : Frame} {E : Ctx} :
    ¬ Diverges P (s, .active fr (E.fill [.trap])) := by
  rintro ⟨g, hg0, hg⟩
  have key : ∀ k, ∃ E' : Ctx, g k = (s, .active fr (E'.fill [.trap])) ∧
      sizeOf (E'.fill [.trap]) + k ≤ sizeOf (E.fill [.trap]) := by
    intro k
    induction k with
    | zero => exact ⟨E, hg0, by omega⟩
    | succ k ih =>
      obtain ⟨E', hk, hle⟩ := ih
      have h := hg k
      rw [hk] at h
      obtain ⟨hs, E'', hE'', hlt⟩ := internalP_trapped h
      exact ⟨E'', Prod.ext hs hE'', by omega⟩
  obtain ⟨E', -, hle⟩ := key (sizeOf (E.fill [.trap]) + 1)
  omega

/-- A trapped thread is at no callout. -/
theorem not_calloutAt_trapped {s : Store Nat} {fr : Frame} {E : Ctx} {h : Nat}
    {args : List Val} : ¬ CalloutAt s (.active fr (E.fill [.trap])) h args := by
  rintro ⟨E', a, hd⟩
  have hd' : decompose? s (E.fill [.trap]) = some (E', a, h, args) := hd
  rw [Ctx.decompose?_fill_trap] at hd'
  cases hd'

variable {I : ScalarInstance}

/-- **The only move from a running trapped thread is the trap answer**, back to the idle
store. -/
theorem trans_trapped {f : I.F.Op} {s : Store Nat} {fr : Frame} {E : Ctx}
    {m : Move I.E I.F} {q : I.HState}
    (h : I.Trans P (.running f s (.active fr (E.fill [.trap]))) m q) :
    m = .inr (.ans f .trap) ∧ q = .idle s := by
  cases h with
  | ucall run callout op =>
    obtain ⟨hs, E', hE'⟩ := reach_trapped run
    change _ = s at hs
    change _ = _ at hE'
    subst hs hE'
    exact absurd callout not_calloutAt_trapped
  | oret run final answer =>
    obtain ⟨hs, E', hE'⟩ := reach_trapped run
    change _ = s at hs
    change _ = _ at hE'
    subst hs hE'
    have hr := trapped_eq_toAdmin (E := E') final
    subst hr
    simp only [Answer.ofResult?, Option.some.injEq] at answer
    subst answer
    exact ⟨rfl, rfl⟩

/-- No import question is asked from a running trapped thread. -/
theorem not_path_trapped_inl {f : I.F.Op} {s : Store Nat} {fr : Frame} {E : Ctx}
    {x : Ev I.E} {rest : List (Move I.E I.F)} {q : I.HState} :
    ¬ I.Path P (.running f s (.active fr (E.fill [.trap]))) (.inl x :: rest) q := by
  intro h
  cases h with
  | cons ht _ => exact Sum.inl_ne_inr (trans_trapped ht).1

/-- **An import call answered by a trap leaves the thread trapped.** -/
theorem trans_ans_trap {q q' q'' : I.HState} {e : I.E.Op} {v : I.E.Ar e}
    (hv : v = Answer.trap) (h₁ : I.Trans P q (.inl (.ask e)) q')
    (h₂ : I.Trans P q' (.inl (.ans e v)) q'') :
    ∃ (f : I.F.Op) (s : Store Nat) (fr : Frame) (E : Ctx),
      q'' = .running f s (.active fr (E.fill [.trap])) := by
  subst hv
  cases h₁ with
  | ucall run callout op =>
    cases h₂ with
    | uret v =>
      obtain ⟨E, a, hd⟩ := callout
      simp only [resumeResult, hd, Answer.toResult, Result.toAdmin]
      exact ⟨_, _, _, E, rfl⟩

/-- Paths along a concatenation split. -/
theorem path_append {q q'' : I.HState} {l₁ l₂ : List (Move I.E I.F)}
    (h : I.Path P q (l₁ ++ l₂) q'') : ∃ q', I.Path P q l₁ q' ∧ I.Path P q' l₂ q'' := by
  induction l₁ generalizing q with
  | nil => exact ⟨q, .nil q, h⟩
  | cons m l ih =>
    rw [List.cons_append] at h
    cases h with
    | cons ht hp =>
      obtain ⟨q', h₁, h₂⟩ := ih hp
      exact ⟨q', .cons ht h₁, h₂⟩

/-- **After a trapped call, the path continues from a running trapped thread.** -/
theorem path_after_trap {q₀ q : I.HState} {c d : List (Call I.E)} {m : I.E.Op} {n : I.E.Ar m}
    (hn : n = Answer.trap) {rest : List (Move I.E I.F)}
    (h : I.Path P q₀ (callMoves (c ++ ⟨m, n⟩ :: d) ++ rest) q) :
    ∃ (f : I.F.Op) (s : Store Nat) (fr : Frame) (E : Ctx),
      I.Path P (.running f s (.active fr (E.fill [.trap]))) (callMoves d ++ rest) q := by
  have hsplit : (callMoves (c ++ ⟨m, n⟩ :: d) ++ rest : List (Move I.E I.F)) =
      callMoves c ++ (.inl (.ask m) :: .inl (.ans m n) :: (callMoves d ++ rest)) := by
    simp [callMoves, List.flatMap_append]
  rw [hsplit] at h
  obtain ⟨q₁, -, h⟩ := path_append h
  cases h with
  | cons h₁ h =>
    cases h with
    | cons h₂ h =>
      obtain ⟨f, s, fr, E, rfl⟩ := trans_ans_trap hn h₁ h₂
      exact ⟨f, s, fr, E, h⟩

/-- A nonempty import log starts with an import question. -/
theorem callMoves_cons_append (x : Call I.E) (d : List (Call I.E)) (r : List (Move I.E I.F)) :
    ∃ rest, callMoves (x :: d) ++ r = .inl (.ask x.1) :: rest :=
  ⟨_, rfl⟩

/-! ## The triple -/

theorem instTripleS_beh (s : Store Nat) (a : I.F.Op) (c : List (Call I.E)) (m : I.E.Op)
    (n : I.E.Ar m) (d : List (Call I.E)) (e : End (Store Nat) (Res I.exports ⊕ PUnit.{1}))
    (hT : IsTrapA m n) (hx : (c ++ ⟨m, n⟩ :: d, e) ∈ (instTripleS I P).1 s a) :
    d = [] ∧ TrapEnd e := by
  rcases hx with ⟨v, s', he, hp⟩ | ⟨he, s', t, hp, hdiv⟩
  · cases hp with
    | cons _ hp =>
      obtain ⟨f, s₁, fr, E, hp⟩ := path_after_trap hT hp
      cases d with
      | nil =>
        cases hp with
        | cons ht _ =>
          obtain ⟨hy, -⟩ := trans_trapped ht
          simp only [Sum.inr.injEq, Ev.ans.injEq] at hy
          obtain ⟨rfl, hv⟩ := hy
          cases hv
          subst he
          exact ⟨rfl, trivial⟩
      | cons x d =>
        obtain ⟨rest, hr⟩ := callMoves_cons_append x d [.inr (.ans a v)]
        rw [hr] at hp
        exact (not_path_trapped_inl hp).elim
  · cases hp with
    | cons _ hp =>
      rw [← List.append_nil (callMoves _)] at hp
      obtain ⟨f, s₁, fr, E, hp⟩ := path_after_trap hT hp
      cases d with
      | nil =>
        cases hp
        exact (not_diverges_trapped hdiv).elim
      | cons x d =>
        obtain ⟨rest, hr⟩ := callMoves_cons_append x d []
        rw [hr] at hp
        exact (not_path_trapped_inl hp).elim

theorem instTripleS_pend (s : Store Nat) (a : I.F.Op) (c : List (Call I.E)) (m : I.E.Op)
    (n : I.E.Ar m) (d : List (Call I.E)) (m' : I.E.Op) (hT : IsTrapA m n) :
    (c ++ ⟨m, n⟩ :: d, m') ∉ (instTripleS I P).2.1 s a := by
  rintro ⟨q, hp⟩
  cases hp with
  | cons _ hp =>
    obtain ⟨f, s₁, fr, E, hp⟩ := path_after_trap hT hp
    cases d with
    | nil => exact not_path_trapped_inl hp
    | cons x d =>
      obtain ⟨rest, hr⟩ := callMoves_cons_append x d [.inl (.ask m')]
      rw [hr] at hp
      exact not_path_trapped_inl hp

theorem instTripleS_inf (s : Store Nat) (a : I.F.Op) (ω : ℕ → Call I.E)
    (hω : ω ∈ (instTripleS I P).2.2 s a) (k : ℕ) : ¬ IsTrapA (ω k).1 (ω k).2 := by
  intro hT
  obtain ⟨x, -, hx⟩ := hω
  obtain ⟨y, h₁, h₂⟩ := hx k
  obtain ⟨f, s₁, fr, E, he⟩ := trans_ans_trap hT h₁ h₂
  obtain ⟨y', h₁', -⟩ := hx (k + 1)
  rw [he] at h₁'
  exact Sum.inl_ne_inr (trans_trapped h₁').1

/-- **Every round of a Core 3.0 instance aborts at an import trap.** -/
theorem instTripleS_trapAbortsRound : TrapAbortsRound IsTrapA (instTripleS I P) :=
  ⟨instTripleS_beh, instTripleS_pend, instTripleS_inf⟩

end Silmaril.Proofs.Wasm.Abstract.NodeTrap

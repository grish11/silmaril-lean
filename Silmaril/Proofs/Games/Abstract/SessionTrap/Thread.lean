module

public import Silmaril.Games.Abstract.SessionTrap.Defs
public import Silmaril.Games.Abstract.StratSession.Thms

/-!
# Threading a triple whose rounds abort on a trap

* `not_satP`: under `TrapAbortsRound`, no call prefix continues past a trapped call: not a
  pending call, not a call forced by a pending call or by a behaviour, not a call of a stream.
* `threadT_next`: in the threading automaton, a trapped call is answered (`reply`) into the
  configuration `run s a (c ++ [⟨m, n⟩])`; from there the only moves are a call (excluded by
  `not_satP`), a return (a trap keeping the store, by `TrapAbortsRound.beh`) or a plain trap.
* `threadS_next`: the same through the relabelling `relMove` of `threadS`.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.SessionTrap

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Games.Abstract.StratObs Silmaril.Games.Abstract.StratThread
  Silmaril.Games.Abstract.StratSession Silmaril.Games.Abstract.SessionTrap

universe u

variable {E : Sig.{u}} {S A B : Type u} {T : (m : E.Op) → E.Ar m → Prop}
  {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})}

/-- A list mapped onto two final elements. -/
theorem map_eq_append_pair {α β : Type u} {f : α → β} {l : List α} {L : List β} {b c : β}
    (h : l.map f = L ++ [b, c]) : ∃ l₀ x y, l = l₀ ++ [x, y] ∧ f x = b ∧ f y = c := by
  obtain ⟨l₁, l₂, rfl, -, h₂⟩ := List.map_eq_append_iff.1 h
  obtain ⟨x, l₃, rfl, hx, h₃⟩ := List.map_eq_cons_iff.1 h₂
  obtain ⟨y, l₄, rfl, hy, h₄⟩ := List.map_eq_cons_iff.1 h₃
  obtain rfl := List.map_eq_nil_iff.1 h₄
  exact ⟨l₁, x, y, rfl, hx, hy⟩

/-- The call at the end of a stream prefix. -/
theorem streamTake_eq_snoc {ω : ℕ → Call E} {k : ℕ} {c : List (Call E)} {x : Call E}
    (h : streamTake ω k = c ++ [x]) : ω c.length = x := by
  have hk : k = c.length + 1 := by
    have := congrArg List.length h
    simpa [streamTake] using this
  subst hk
  have := congrArg (fun l => l[c.length]?) h
  simp only [streamTake, List.getElem?_ofFn] at this
  simpa using this

/-- **No call prefix continues past a trapped call.** -/
theorem not_satP (ht : TrapAbortsRound T t) {s : S} {a : A} {c : List (Call E)} {m : E.Op}
    {n : E.Ar m} (hT : T m n) (m' : E.Op) : (c ++ [⟨m, n⟩], m') ∉ satP t s a := by
  rintro (h | ⟨d, m'', hd, n', c', rfl⟩ | ⟨d, e, hd, n', c', rfl⟩ | ⟨ω, hω, k, hk, -⟩)
  · exact ht.pend s a c m n [] m' hT h
  · exact ht.pend s a c m n (⟨m', n'⟩ :: c') m'' hT (by simpa using hd)
  · obtain ⟨h, -⟩ := ht.beh s a c m n (⟨m', n'⟩ :: c') e hT (by simpa using hd)
    cases h
  · have := ht.inf s a ω hω c.length
    rw [streamTake_eq_snoc hk] at this
    exact this hT

/-- **In the threading, a trapped call is followed by a trap answer.** -/
theorem threadT_next (ht : TrapAbortsRound T t) {s₀ : S}
    {p : List (Move E (sig1 A (B ⊕ PUnit.{u + 1})))} {m : E.Op} {n : E.Ar m}
    {y : Move E (sig1 A (B ⊕ PUnit.{u + 1}))} (hT : T m n)
    (hp : p ++ [.inl (.ans m n), y] ∈ (threadT t s₀).toStrategy) :
    ∃ a, y = .inr (.ans a (.inl (.inr PUnit.unit))) ∨ y = .inr (.ans a (.inr PUnit.unit)) := by
  obtain ⟨z, hz⟩ := hp
  obtain ⟨w, -, hw⟩ := TRun.of_append hz
  cases hw with
  | cons h₁ hw =>
    cases hw with
    | cons h₂ _ =>
      cases h₁ with
      | reply s a c _ _ =>
        cases h₂ with
        | call _ _ _ m' hc => exact (not_satP ht hT m' hc).elim
        | ret _ _ _ b s' hb =>
          obtain ⟨-, he⟩ := ht.beh s a c m n [] _ hT hb
          rcases b with b | ⟨⟩
          · exact he.elim
          · exact ⟨a, .inl rfl⟩
        | trap _ _ _ _ => exact ⟨a, .inr rfl⟩

/-- **In a session, a trapped call is followed by a trap answer.** -/
theorem threadS_next (ht : TrapAbortsRound T t) (s₀ : S) :
    TrapAbortsBelow T (threadS t s₀) := by
  intro q m n y hT hq
  obtain ⟨p, hp, hpq⟩ := mem_threadS.1 hq
  obtain ⟨p₀, x, y', rfl, hx, rfl⟩ := map_eq_append_pair hpq
  obtain ⟨e, rfl⟩ : ∃ e, x = .inl e := by
    rcases x with e | (_ | _) <;> simp [relMove] at hx ⊢
  simp only [relMove, Sum.inl.injEq] at hx
  subst hx
  obtain ⟨a, rfl | rfl⟩ := threadT_next ht hT hp <;> exact ⟨a, rfl⟩

end Silmaril.Proofs.Games.Abstract.SessionTrap

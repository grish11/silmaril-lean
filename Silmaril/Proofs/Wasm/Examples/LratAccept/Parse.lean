module

public import Silmaril.Wasm.Examples.LratAccept.Defs

@[expose] public section

/-!
# The certificate automaton accepts only decodable certificates

`decode_of_certRun`: if the parser automaton `certRun` of the acceptor ends in state `0` on the
words `ws`, the flat LRAT stream decoder `LratStream.decode ws` succeeds. Each parser of the
format (`LratStream.lits`, `ids`, `groups`, `step`, `steps`) is matched by a run of the
automaton through the corresponding states; the sink `9` never leaves, and a run that stops in
the middle of a step ends in a nonzero state.

A Silmaril addition.
-/

namespace Silmaril.Proofs.Wasm.Examples.LratAccept

open Silmaril.Wasm.Examples.LratAccept (certStep certRun)
open Silmaril.Logic.SAT.Carrier (LitWord)
open Silmaril.Logic.SAT.Carrier.LratStream

theorem certRun_nil (q : Nat) : certRun q [] = q := rfl

theorem certRun_cons (q : Nat) (x : BitVec 32) (ws : List (BitVec 32)) :
    certRun q (x :: ws) = certRun (certStep q x) ws := rfl

theorem certRun_append (q : Nat) (ws vs : List (BitVec 32)) :
    certRun q (ws ++ vs) = certRun (certRun q ws) vs := by
  simp [certRun, List.foldl_append]

theorem certStep_sink (x : BitVec 32) : certStep 9 x = 9 := rfl

theorem certRun_sink (ws : List (BitVec 32)) : certRun 9 ws = 9 := by
  induction ws with
  | nil => rfl
  | cons x ws ih => rw [certRun_cons, certStep_sink, ih]

theorem posWord_isSome {x : BitVec 32} (h : 0 < x.toInt) : ∃ n, posWord? x = some n :=
  ⟨x.toInt.toNat, by simp [posWord?, h]⟩

/-- **Literals**: from a literal state `a` (zero goes to `b`), a run ending in `0` reads
`lits`. -/
theorem lits_of_run {a b : Nat}
    (ha : ∀ x, certStep a x = if x = 0 then b else if LitWord x then a else 9) (ha0 : a ≠ 0) :
    ∀ ws, certRun a ws = 0 →
      ∃ c rest, lits ws = some (c, rest) ∧ certRun b rest = 0 ∧ rest.length < ws.length
  | [], h => absurd h ha0
  | x :: ws, h => by
    rw [certRun_cons, ha] at h
    by_cases hx : x = 0
    · subst hx
      exact ⟨[], ws, by simp [lits], by simpa using h, by simp⟩
    · by_cases hl : LitWord x = true
      · simp only [hx, hl, ↓reduceIte] at h
        obtain ⟨c, rest, hc, hr, hlen⟩ := lits_of_run ha ha0 ws h
        exact ⟨x.toInt :: c, rest, by simp [lits, hl, hc]; exact hx, hr, by simp; omega⟩
      · simp only [hx, hl, ↓reduceIte, Bool.false_eq_true, certRun_sink] at h
        exact absurd h (by decide)

/-- **Ids**: from an id state `a` (zero goes to `b`), a run ending in `0` reads `ids`. -/
theorem ids_of_run {a b : Nat}
    (ha : ∀ x, certStep a x = if x = 0 then b else if 0 < x.toInt then a else 9) (ha0 : a ≠ 0) :
    ∀ ws, certRun a ws = 0 →
      ∃ is rest, ids ws = some (is, rest) ∧ certRun b rest = 0 ∧ rest.length < ws.length
  | [], h => absurd h ha0
  | x :: ws, h => by
    rw [certRun_cons, ha] at h
    by_cases hx : x = 0
    · subst hx
      exact ⟨[], ws, by simp [ids], by simpa using h, by simp⟩
    · by_cases hp : 0 < x.toInt
      · simp only [hx, hp, ↓reduceIte] at h
        obtain ⟨is, rest, hc, hr, hlen⟩ := ids_of_run ha ha0 ws h
        obtain ⟨n, hn⟩ := posWord_isSome hp
        exact ⟨n :: is, rest, by simp [ids, hn, hc]; exact hx, hr, by simp; omega⟩
      · simp only [hx, hp, ↓reduceIte, certRun_sink] at h
        exact absurd h (by decide)

theorem step7 (x : BitVec 32) :
    certStep 7 x = if x = 0 then 0 else if 0 < x.toInt then 8 else 9 := rfl

/-- **RAT groups**: from state `7`, a run ending in `0` reads `groups`, with enough fuel. -/
theorem groups_of_run : ∀ (ws : List (BitVec 32)) (f : Nat), ws.length ≤ f → certRun 7 ws = 0 →
    ∃ gs rest, groups f ws = some (gs, rest) ∧ certRun 0 rest = 0 ∧ rest.length < ws.length
  | [], _, _, h => absurd h (by decide)
  | x :: ws, f, hf, h => by
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp at hf; omega⟩
    rw [certRun_cons, step7] at h
    by_cases hx : x = 0
    · subst hx
      exact ⟨[], ws, by simp [groups], by simpa using h, by simp⟩
    · by_cases hp : 0 < x.toInt
      · simp only [hx, hp, ↓reduceIte] at h
        obtain ⟨is, r, hi, hr, hlen⟩ := ids_of_run (a := 8) (b := 7) (fun _ => rfl) (by decide) ws h
        have : r.length < ws.length + 1 := by omega
        obtain ⟨gs, rest, hg, hr', hlen'⟩ :=
          groups_of_run r f (by simp at hf; omega) hr
        obtain ⟨n, hn⟩ := posWord_isSome hp
        exact ⟨(n, is) :: gs, rest, by simp [groups, hn, hi, hg]; exact hx, hr', by simp; omega⟩
      · simp only [hx, hp, ↓reduceIte, certRun_sink] at h
        exact absurd h (by decide)
termination_by ws => ws.length

/-- **One step**: from state `0`, a run ending in `0` on a nonempty list reads one `step`. -/
theorem step_of_run (t : BitVec 32) (ws : List (BitVec 32)) (f : Nat) (hf : ws.length ≤ f)
    (h : certRun 0 (t :: ws) = 0) :
    ∃ st rest, step f (t :: ws) = some (st, rest) ∧ certRun 0 rest = 0 ∧
      rest.length < ws.length := by
  rw [certRun_cons] at h
  by_cases h1 : t = 1
  · subst h1
    rw [show certStep 0 1 = 1 by decide] at h
    match ws, h with
    | [], h => exact absurd h (by decide)
    | x :: xs, h =>
      rw [certRun_cons] at h
      by_cases hp : 0 < x.toInt
      · rw [show certStep 1 x = 2 by simp [certStep, hp]] at h
        obtain ⟨c, r, hc, hr, hl⟩ := lits_of_run (a := 2) (b := 3) (fun _ => rfl) (by decide) xs h
        obtain ⟨hs, r', hh, hr', hl'⟩ := ids_of_run (a := 3) (b := 0) (fun _ => rfl) (by decide) r hr
        obtain ⟨n, hn⟩ := posWord_isSome hp
        exact ⟨.add n c hs, r', by simp [step, hn, hc, hh], hr', by simp; omega⟩
      · rw [show certStep 1 x = 9 by simp [certStep, hp], certRun_sink] at h
        exact absurd h (by decide)
  by_cases h2 : t = 2
  · subst h2
    rw [show certStep 0 2 = 4 by decide] at h
    match ws, h with
    | [], h => exact absurd h (by decide)
    | x :: xs, h =>
      obtain ⟨is, r, hi, hr, hl⟩ := ids_of_run (a := 4) (b := 0) (fun _ => rfl) (by decide) _ h
      exact ⟨.del is, r, by simp [step, hi], hr, hl⟩
  by_cases h3 : t = 3
  · subst h3
    rw [show certStep 0 3 = 5 by decide] at h
    match ws, h with
    | [], h => exact absurd h (by decide)
    | x :: xs, h =>
      rw [certRun_cons] at h
      by_cases hp : 0 < x.toInt
      · rw [show certStep 5 x = 6 by simp [certStep, hp]] at h
        obtain ⟨c, r, hc, hr, hl⟩ := lits_of_run (a := 6) (b := 7) (fun _ => rfl) (by decide) xs h
        obtain ⟨gs, r', hg, hr', hl'⟩ := groups_of_run r f (by simp at hf; omega) hr
        obtain ⟨n, hn⟩ := posWord_isSome hp
        exact ⟨.rat n c gs, r', by simp [step, hn, hc, hg], hr', by simp; omega⟩
      · rw [show certStep 5 x = 9 by simp [certStep, hp], certRun_sink] at h
        exact absurd h (by decide)
  rw [show certStep 0 t = 9 from by simp [certStep, show t ≠ 1#32 from h1, show t ≠ 2#32 from h2, show t ≠ 3#32 from h3], certRun_sink] at h
  exact absurd h (by decide)

/-- **Steps**: from state `0`, a run ending in `0` reads `steps`, with enough fuel. -/
theorem steps_of_run : ∀ (ws : List (BitVec 32)) (f : Nat), ws.length ≤ f → certRun 0 ws = 0 →
    ∃ ss, steps f ws = some ss
  | [], f, _, _ => by cases f <;> exact ⟨[], rfl⟩
  | t :: ws, f, hf, h => by
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp at hf; omega⟩
    obtain ⟨st, rest, hs, hr, hl⟩ := step_of_run t ws (t :: ws).length (by simp) h
    obtain ⟨ss, hss⟩ := steps_of_run rest f (by simp at hf; omega) hr
    simp only [List.length_cons] at hs
    exact ⟨st :: ss, by simp [steps, hs, hss]⟩
termination_by ws => ws.length

/-- **A run of the automaton ending in `0` is on a decodable certificate.** -/
theorem decode_of_certRun {ws : List (BitVec 32)} (h : certRun 0 ws = 0) :
    (decode ws).isSome = true := by
  obtain ⟨ss, hss⟩ := steps_of_run ws ws.length le_rfl h
  simp [decode, hss]

/-- The automaton's states are at most `9`. -/
theorem certStep_le (q : Nat) (x : BitVec 32) : certStep q x ≤ 9 := by
  unfold certStep
  split <;> (try split_ifs) <;> omega

theorem certRun_le {q : Nat} (hq : q ≤ 9) (ws : List (BitVec 32)) : certRun q ws ≤ 9 := by
  induction ws generalizing q with
  | nil => exact hq
  | cons x ws ih => rw [certRun_cons]; exact ih (certStep_le q x)

end Silmaril.Proofs.Wasm.Examples.LratAccept

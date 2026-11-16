module

public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Order.Bounds.Basic

/-!
# König's lemma for levelled finite sets (proofs)

Levels `L n` are finite and nonempty, and every element of level `n + 1` has a parent in level
`n` (`R n x y`). Then there is an infinite path `τ`, with `τ n ∈ L n` and `R n (τ n) (τ (n + 1))`
(`konig`).

An element `x` of level `n` *reaches depth `k`* (`Reach L R n k x`) if there is a path of `k`
steps down from it. Every depth is reached from every level (`exists_reach`), by following
parents up from an element `k` levels below. Finitely many candidates, each reaching some
depths and therefore all smaller ones, cannot cover all depths unless one reaches every depth
(`exists_forall_of_finite`). Such *good* elements exist at level `0`, and each has a good
child, so dependent choice gives the path.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.IterUniformFin

universe v

variable {α : Type v}

/-- **Dependent choice** along a sequence of predicates. -/
theorem exists_chain (Q : ℕ → α → Prop) (R : ℕ → α → α → Prop)
    (hs : ∀ n p, Q n p → ∃ p', R n p p' ∧ Q (n + 1) p') {p₀ : α} (h₀ : Q 0 p₀) :
    ∃ σ : ℕ → α, σ 0 = p₀ ∧ ∀ n, Q n (σ n) ∧ R n (σ n) (σ (n + 1)) := by
  let g : (n : ℕ) → {p // Q n p} := fun n =>
    Nat.rec (motive := fun n => {p // Q n p}) ⟨p₀, h₀⟩
      (fun n p => ⟨Classical.choose (hs n p.1 p.2), (Classical.choose_spec (hs n p.1 p.2)).2⟩) n
  exact ⟨fun n => (g n).1, rfl,
    fun n => ⟨(g n).2, (Classical.choose_spec (hs n (g n).1 (g n).2)).1⟩⟩

/-- **Pigeonhole for depths**: if every depth is reached by some element of a finite set, and
reaching a depth implies reaching the one above it, one element reaches every depth. -/
theorem exists_forall_of_finite {T : Set α} (hT : T.Finite) {P : α → ℕ → Prop}
    (hP : ∀ x k, P x (k + 1) → P x k) (hall : ∀ k, ∃ x ∈ T, P x k) : ∃ x ∈ T, ∀ k, P x k := by
  by_contra hn
  push Not at hn
  choose! K hK using hn
  obtain ⟨M, hM⟩ := (hT.image K).bddAbove
  obtain ⟨x, hx, hPx⟩ := hall M
  have hdown : ∀ d n, P x (n + d) → P x n := fun d => by
    induction d with
    | zero => exact fun n h => h
    | succ d ih => exact fun n h => ih n (hP x _ (by rwa [Nat.add_succ] at h))
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (hM ⟨x, hx, rfl⟩)
  exact hK x hx (hdown d _ (hd ▸ hPx))

section Konig

variable (L : ℕ → Set α) (R : ℕ → α → α → Prop)

/-- `x` is in level `n` and starts a path of `k` steps down. -/
def Reach : ℕ → ℕ → α → Prop
  | n, 0, x => x ∈ L n
  | n, k + 1, x => x ∈ L n ∧ ∃ y, R n x y ∧ Reach (n + 1) k y

variable {L R}

theorem Reach.mem {n k : ℕ} {x : α} (h : Reach L R n k x) : x ∈ L n := by
  cases k with
  | zero => exact h
  | succ k => exact h.1

theorem Reach.pred : ∀ {n k : ℕ} {x : α}, Reach L R n (k + 1) x → Reach L R n k x
  | _, 0, _, h => h.1
  | _, _ + 1, _, ⟨hx, y, hR, hy⟩ => ⟨hx, y, hR, Reach.pred hy⟩

/-- Every depth is reached from every level. -/
theorem exists_reach (hne : ∀ n, (L n).Nonempty) (hpar : ∀ n, ∀ y ∈ L (n + 1), ∃ x ∈ L n, R n x y) :
    ∀ k n, ∃ x, Reach L R n k x := by
  intro k
  induction k with
  | zero => exact fun n => hne n
  | succ k ih =>
    intro n
    obtain ⟨y, hy⟩ := ih (n + 1)
    obtain ⟨x, hx, hR⟩ := hpar n y hy.mem
    exact ⟨x, hx, y, hR, hy⟩

/-- **König's lemma**: finite nonempty levels in which every element has a parent carry an
infinite path. -/
theorem konig (hfin : ∀ n, (L n).Finite) (hne : ∀ n, (L n).Nonempty)
    (hpar : ∀ n, ∀ y ∈ L (n + 1), ∃ x ∈ L n, R n x y) :
    ∃ τ : ℕ → α, ∀ n, τ n ∈ L n ∧ R n (τ n) (τ (n + 1)) := by
  have hr := exists_reach hne hpar
  let Good : ℕ → α → Prop := fun n x => ∀ k, Reach L R n k x
  have h0 : ∃ x ∈ L 0, Good 0 x :=
    exists_forall_of_finite (P := fun x k => Reach L R 0 k x) (hfin 0)
      (fun _ _ h => Reach.pred h)
      fun k => (hr k 0).elim fun x hx => ⟨x, hx.mem, hx⟩
  have hstep : ∀ n x, Good n x → ∃ y, R n x y ∧ Good (n + 1) y := by
    intro n x hx
    obtain ⟨y, ⟨-, hR⟩, hy⟩ := exists_forall_of_finite (T := L (n + 1) ∩ {y | R n x y})
      (P := fun y k => Reach L R (n + 1) k y)
      ((hfin (n + 1)).inter_of_left _) (fun _ _ h => Reach.pred h) fun k => by
        obtain ⟨-, y, hR, hy⟩ := hx (k + 1)
        exact ⟨y, ⟨hy.mem, hR⟩, hy⟩
    exact ⟨y, hR, hy⟩
  obtain ⟨x₀, -, hx₀⟩ := h0
  obtain ⟨τ, -, hτ⟩ := exists_chain Good R hstep hx₀
  exact ⟨τ, fun n => ⟨((hτ n).1 0), (hτ n).2⟩⟩

end Konig

end Silmaril.Proofs.Games.Abstract.IterUniformFin

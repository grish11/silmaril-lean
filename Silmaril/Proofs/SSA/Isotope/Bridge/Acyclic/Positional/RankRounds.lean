module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Rank.Defs

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Rank

variable {n : Nat} (targets : Fin n → List (Fin n))

private theorem next_round (k : Nat) (i : Fin n) :
    (rounds targets (k + 1)).get i = ((rounds targets k).get i).orElse (fun _ =>
      if (targets i).all (fun j => ((rounds targets k).get j).isSome) then some k else none) := by
  simp [rounds, Vector.get, Fin.cast]

private theorem next_some {k : Nat} {i : Fin n} {r : Nat}
    (ranked : (rounds targets k).get i = some r) :
    (rounds targets (k + 1)).get i = some r := by
  rw [next_round, ranked]
  rfl

private theorem rank_bound (k : Nat) (i : Fin n) {r : Nat}
    (ranked : (rounds targets k).get i = some r) : r < k := by
  induction k with
  | zero => simp [rounds, Vector.get] at ranked
  | succ k ih =>
    rw [next_round] at ranked
    cases old : (rounds targets k).get i with
    | some s =>
      simp [old] at ranked
      subst r
      exact Nat.lt_succ_of_lt (ih old)
    | none =>
      simp only [old, Option.orElse_none] at ranked
      split at ranked
      · have eq := Option.some.inj ranked
        subst r
        exact Nat.lt_succ_self k
      · contradiction

private theorem edge_ranks (k : Nat) (i j : Fin n) (edge : j ∈ targets i) {r : Nat}
    (ranked : (rounds targets k).get i = some r) :
    ∃ s, (rounds targets k).get j = some s ∧ s < r := by
  induction k with
  | zero => simp [rounds, Vector.get] at ranked
  | succ k ih =>
    rw [next_round] at ranked
    cases old : (rounds targets k).get i with
    | some s =>
      simp [old] at ranked
      subst r
      obtain ⟨v, hj, lt⟩ := ih old
      exact ⟨v, next_some targets hj, lt⟩
    | none =>
      simp only [old, Option.orElse_none] at ranked
      split at ranked
      · rename_i ready
        have eq := Option.some.inj ranked
        subst r
        have hj := List.all_eq_true.mp ready j edge
        cases e : (rounds targets k).get j with
        | none => simp [e] at hj
        | some v => exact ⟨v, next_some targets e, rank_bound targets k j e⟩
      · contradiction

theorem check_sound_proof (ok : check targets = true) {i j : Fin n} (edge : j ∈ targets i) :
    ((rounds targets n).get j).getD 0 < ((rounds targets n).get i).getD 0 := by
  have hi := List.all_eq_true.mp ok i (List.mem_finRange i)
  cases e : (rounds targets n).get i with
  | none => simp [e] at hi
  | some r =>
    obtain ⟨s, hj, lt⟩ := edge_ranks targets n i j edge e
    simpa [e, hj] using lt

private theorem round_complete (rank : Fin n → Nat)
    (decreases : ∀ i j, j ∈ targets i → rank j < rank i)
    (k : Nat) (i : Fin n) (small : rank i < k) : ((rounds targets k).get i).isSome = true := by
  induction k generalizing i with
  | zero => omega
  | succ k ih =>
    rw [next_round]
    cases old : (rounds targets k).get i with
    | some s => rfl
    | none =>
      have ready : (targets i).all (fun j => ((rounds targets k).get j).isSome) = true := by
        apply List.all_eq_true.mpr
        intro j edge
        have h := decreases i j edge
        exact ih j (by omega)
      simp only [Option.orElse_none, ready, ↓reduceIte, Option.isSome_some]

theorem check_complete_proof (rank : Fin n → Nat)
    (decreases : ∀ i j, j ∈ targets i → rank j < rank i) (bounded : ∀ i, rank i < n) :
    check targets = true :=
  List.all_eq_true.mpr fun i _ => round_complete targets rank decreases n i (bounded i)

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Rank

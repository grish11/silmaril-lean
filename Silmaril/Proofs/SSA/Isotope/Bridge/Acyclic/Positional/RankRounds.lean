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

theorem ranked_successor_proof {i j : Fin n} (hi : ((rounds targets n).get i).isSome = true)
    (edge : j ∈ targets i) :
    ((rounds targets n).get j).isSome = true ∧
      ((rounds targets n).get j).getD 0 < ((rounds targets n).get i).getD 0 := by
  cases e : (rounds targets n).get i with
  | none => simp [e] at hi
  | some r =>
    obtain ⟨s, hj, lt⟩ := edge_ranks targets n i j edge e
    simpa [e, hj] using lt

private theorem round_complete (live : Fin n → Prop) (rank : Fin n → Nat)
    (edge : ∀ i j, live i → j ∈ targets i → live j ∧ rank j < rank i)
    (k : Nat) (i : Fin n) (reachable : live i)
    (small : rank i < k) : ((rounds targets k).get i).isSome = true := by
  induction k generalizing i with
  | zero => omega
  | succ k ih =>
    rw [next_round]
    cases old : (rounds targets k).get i with
    | some s => rfl
    | none =>
      have ready : (targets i).all (fun j => ((rounds targets k).get j).isSome) = true := by
        apply List.all_eq_true.mpr
        intro j hj
        obtain ⟨next, decreases⟩ := edge i j reachable hj
        exact ih j next (by omega)
      simp only [Option.orElse_none, ready, ↓reduceIte, Option.isSome_some]

theorem check_complete_proof (rank : Fin n → Nat)
    (decreases : ∀ i j, j ∈ targets i → rank j < rank i) (bounded : ∀ i, rank i < n) :
    check targets = true :=
  List.all_eq_true.mpr fun i _ =>
    round_complete targets (fun _ => True) rank (fun i j _ e => ⟨trivial, decreases i j e⟩)
      n i trivial (bounded i)

theorem checkFrom_iff_proof (entry : List (Fin n)) :
    checkFrom targets entry = true ↔
      ∃ (live : Fin n → Prop) (rank : Fin n → Nat),
        (∀ i ∈ entry, live i) ∧
        (∀ i j, live i → j ∈ targets i → live j ∧ rank j < rank i) ∧
        ∀ i, live i → rank i < n := by
  constructor
  · intro accepted
    refine ⟨fun i => ((rounds targets n).get i).isSome = true,
      fun i => ((rounds targets n).get i).getD 0, List.all_eq_true.mp accepted, ?_, ?_⟩
    · exact fun _ _ hi edge => ranked_successor_proof targets hi edge
    · intro i hi
      cases h : (rounds targets n).get i with
      | none => simp [h] at hi
      | some r => simpa [h] using rank_bound targets n i h
  · rintro ⟨live, rank, roots, edge, bound⟩
    exact List.all_eq_true.mpr fun i hi =>
      round_complete targets live rank edge n i (roots i hi) (bound i (roots i hi))

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Rank

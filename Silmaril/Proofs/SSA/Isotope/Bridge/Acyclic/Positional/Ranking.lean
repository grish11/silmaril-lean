module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Logic.Relation

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ] {L : LCtx τ} {n : Nat}

private theorem Ranking.path_decreases {p : Table Φ L n} (ranking : Ranking p) {i j : Fin n}
    (path : Relation.TransGen p.LocalEdge i j) : ranking.rank j < ranking.rank i := by
  induction path with
  | single edge => exact ranking.decreases _ _ edge
  | tail _ edge ih => exact (ranking.decreases _ _ edge).trans ih

private theorem check_of_noCycle (p : Table Φ L n)
    (acyclic : ∀ i, ¬ Relation.TransGen p.LocalEdge i i) : p.checkAcyclic = true := by
  classical
  let reachable (i : Fin n) := Finset.univ.filter (Relation.TransGen p.LocalEdge i)
  have mem {i j} : j ∈ reachable i ↔ Relation.TransGen p.LocalEdge i j := by
    simp [reachable]
  apply Rank.check_complete p.localTargets (fun i => (reachable i).card)
  · intro i j edge
    have step : Relation.TransGen p.LocalEdge i j := .single edge
    have subset : reachable j ⊆ reachable i := fun _ next => mem.mpr (step.trans (mem.mp next))
    exact Finset.card_lt_card ((Finset.ssubset_iff_of_subset subset).mpr
      ⟨j, mem.mpr step, fun self => acyclic j (mem.mp self)⟩)
  · intro i
    have strict : reachable i ⊂ Finset.univ :=
      (Finset.ssubset_iff_of_subset (Finset.subset_univ _)).mpr
        ⟨i, Finset.mem_univ i, fun self => acyclic i (mem.mp self)⟩
    simpa using Finset.card_lt_card strict

theorem checkAcyclic_iff_noCycle_proof (p : Table Φ L n) :
    p.checkAcyclic = true ↔ ∀ i, ¬ Relation.TransGen p.LocalEdge i i :=
  ⟨fun ok i path => (Nat.lt_irrefl ((p.acyclicRanking ok).rank i))
      ((p.acyclicRanking ok).path_decreases path),
    check_of_noCycle p⟩

theorem checkAcyclic_iff_ranked_proof (p : Table Φ L n) :
    p.checkAcyclic = true ↔ Nonempty (Ranking p) :=
  ⟨fun ok => ⟨p.acyclicRanking ok⟩,
    fun ⟨rank⟩ => check_of_noCycle p (fun _ path => (Nat.lt_irrefl _) (rank.path_decreases path))⟩

theorem toLetCase?_isSome_proof (p : Table Φ L n) {d : Nat} {β : BoundCtx τ d}
    (i : Fin n) (a : Operand Φ β (p.types i)) :
    (p.toLetCase? i a).isSome = p.checkAcyclic := by
  cases h : p.checkAcyclic <;> simp [Table.toLetCase?, h]

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional

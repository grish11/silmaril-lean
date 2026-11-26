module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Logic.Relation

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ] {L : LCtx τ} {n : Nat}

theorem checkAcyclic_iff_ranked_proof (p : Table Φ L n) :
    p.checkAcyclic = true ↔ Nonempty (Ranking p) := by
  refine ⟨fun ok => ⟨p.acyclicRanking ok⟩, ?_⟩
  rintro ⟨ranking⟩
  exact FiniteGraph.kahn_complete p.localTargets (List.finRange n)
    (fun i _ j edge _ => ranking.decreases i j edge)

private theorem Ranking.path_decreases {p : Table Φ L n} (ranking : Ranking p) {i j : Fin n}
    (path : Relation.TransGen p.LocalEdge i j) : ranking.rank j < ranking.rank i := by
  induction path with
  | single edge => exact ranking.decreases _ _ edge
  | tail _ edge ih => exact (ranking.decreases _ _ edge).trans ih

private theorem ranked_of_noCycle (p : Table Φ L n)
    (acyclic : ∀ i, ¬ Relation.TransGen p.LocalEdge i i) : Nonempty (Ranking p) := by
  classical
  let reachable (i : Fin n) := Finset.univ.filter (Relation.TransGen p.LocalEdge i)
  have mem {i j} : j ∈ reachable i ↔ Relation.TransGen p.LocalEdge i j := by
    simp [reachable]
  refine ⟨⟨fun i => (reachable i).card, ?_⟩⟩
  intro i j edge
  have step : Relation.TransGen p.LocalEdge i j := .single edge
  have subset : reachable j ⊆ reachable i := fun _ next => mem.mpr (step.trans (mem.mp next))
  exact Finset.card_lt_card ((Finset.ssubset_iff_of_subset subset).mpr
    ⟨j, mem.mpr step, fun self => acyclic j (mem.mp self)⟩)

theorem checkAcyclic_iff_noCycle_proof (p : Table Φ L n) :
    p.checkAcyclic = true ↔ ∀ i, ¬ Relation.TransGen p.LocalEdge i i := by
  rw [checkAcyclic_iff_ranked_proof]
  exact ⟨fun ⟨rank⟩ i path => (Nat.lt_irrefl _) (rank.path_decreases path), ranked_of_noCycle p⟩

theorem toLetCase?_isSome_proof (p : Table Φ L n) {d : Nat} {β : BoundCtx τ d}
    (i : Fin n) (a : Operand Φ β (p.types i)) :
    (p.toLetCase? i a).isSome = p.checkAcyclic := by
  cases h : p.checkAcyclic <;> simp [Table.toLetCase?, h]

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional

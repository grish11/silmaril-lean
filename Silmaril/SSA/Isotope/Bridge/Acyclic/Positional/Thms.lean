module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Defs
public import Mathlib.Logic.Relation
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Ranking

/-! # Global acyclicity and checked compilation of positional SSA tables -/

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ] {L : LCtx τ} {n : Nat}

/-- The checker accepts precisely the tables that admit a decreasing local rank. -/
theorem Table.checkAcyclic_iff_ranked (p : Table Φ L n) :
    p.checkAcyclic = true ↔ Nonempty (Ranking p) :=
  checkAcyclic_iff_ranked_proof p

/-- The check excludes every nonempty directed cycle on local labels,
including cycles unreachable from the chosen entry. -/
theorem Table.checkAcyclic_iff_noCycle (p : Table Φ L n) :
    p.checkAcyclic = true ↔ ∀ i, ¬ Relation.TransGen p.LocalEdge i i :=
  checkAcyclic_iff_noCycle_proof p

/-- Checked translation succeeds exactly when the whole local table is acyclic. -/
theorem Table.toLetCase?_isSome (p : Table Φ L n) {d : Nat} {β : BoundCtx τ d}
    (i : Fin n) (a : Operand Φ β (p.types i)) :
    (p.toLetCase? i a).isSome = p.checkAcyclic :=
  toLetCase?_isSome_proof p i a

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional

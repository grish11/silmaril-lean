module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Refinement.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.TwoRequest.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Refinement.Comparison
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Refinement.Native

/-! # Exact refinement at a supplied typed entry packet -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Category.FiniteIteration
open Category.FiniteIteration.CFG.Dependent.Native (withExitUB)
open TwoRequest (Exits resultBehaviour result_order)
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
  (sound separate follows_le checked_fits checked_countermodel checked_refines_iff)

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ}

theorem Tree.refines_execute {p q : Tree S} (related : p.Refines q)
    {n : Nat} (prim : Syntax.Primitives Φ n) (s : Fin n) :
    (p.execute prim s).refines (q.execute prim s) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.sound p q related prim s

/-- One state per common reply, plus a final test state, suffices to refute
a failed comparison. The common prefix carries actual typed values. -/
theorem Tree.exists_prefix_countermodel [DecidableEq Φ] {p q : Tree S} (fails : ¬ p.Refines q) :
    ∃ (n : Nat) (probe : Prefix S.replies n), p.Follows probe ∧ q.Follows probe ∧
      ¬ resultBehaviour (p.execute (S.primitives probe.handler) 0) ≤
        resultBehaviour (q.execute (S.primitives probe.handler) 0) := by
  obtain ⟨n, probe, left, right, bad⟩ :=
    Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.separate p q fails
  exact ⟨n, probe, left, right, fun h => bad ((result_order _ _).mp h)⟩

theorem Tree.Follows.le_budget {p : Tree S} {n depth : Nat} {probe : Prefix S.replies n}
    (path : p.Follows probe) (budget : p.Fits depth) : n ≤ depth :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.follows_le path budget

/-- The rank used for extraction bounds the requests on every payload branch. -/
theorem Table.fits_of_extract [DecidableEq Φ] {R : List Syntax.Ty} {g : Table S R}
    {raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits}
    {input : Syntax.Payload (R.get g.entry)} {p : Tree S}
    (found : g.extract? raw input = some p) : p.Fits ((g.ranks.get g.entry).getD 0 + 1) :=
  checked_fits found

section Native

variable [DecidableEq Φ] {R₀ R₁ : List Syntax.Ty}
  {g₀ : Table S R₀} {g₁ : Table S R₁}
  {raw₀ : CFG.Dependent.Native.Typed Φ [R₀.get g₀.entry] Exits}
  {raw₁ : CFG.Dependent.Native.Typed Φ [R₁.get g₁.entry] Exits}
  {input : Syntax.Payload (R₀.get g₀.entry)}
  {p q : Tree S}

/-- A failed comparison is witnessed at the original endpoints using a
common feasible prefix whose length is bounded by both extraction budgets. -/
theorem Table.exists_prefix_countermodel (same : R₀.get g₀.entry = R₁.get g₁.entry)
    (left : g₀.extract? raw₀ input = some p)
    (right : g₁.extract? raw₁ (cast (congrArg Syntax.Payload same) input) = some q)
    (fails : ¬ p.Refines q) :
    ∃ (n : Nat) (probe : Prefix S.replies n),
      n ≤ min ((g₀.ranks.get g₀.entry).getD 0 + 1) ((g₁.ranks.get g₁.entry).getD 0 + 1) ∧
      p.Follows probe ∧ q.Follows probe ∧
      ¬ Shape.denote (withExitUB raw₀ g₀.selected)
          (Syntax.model (S.primitives probe.handler) (g₀.bindings input)) 0 ≤
        Shape.denote (withExitUB raw₁ g₁.selected) (Syntax.model (S.primitives probe.handler)
          (g₁.bindings (cast (congrArg Syntax.Payload same) input))) 0 :=
  checked_countermodel same left right fails

/-- Both checked endpoints start from the same typed packet. The label lists
may differ, so the caller packet is transported along the entry type equality. -/
theorem Table.refines_iff (same : R₀.get g₀.entry = R₁.get g₁.entry)
    (left : g₀.extract? raw₀ input = some p)
    (right : g₁.extract? raw₁ (cast (congrArg Syntax.Payload same) input) = some q) :
    (∀ (n : Nat) (prim : Syntax.Primitives Φ n) (s : Fin n),
      Shape.denote (withExitUB raw₀ g₀.selected) (Syntax.model prim (g₀.bindings input)) s ≤
        Shape.denote (withExitUB raw₁ g₁.selected)
          (Syntax.model prim (g₁.bindings (cast (congrArg Syntax.Payload same) input))) s) ↔
      p.Refines q :=
  checked_refines_iff same left right

end Native

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

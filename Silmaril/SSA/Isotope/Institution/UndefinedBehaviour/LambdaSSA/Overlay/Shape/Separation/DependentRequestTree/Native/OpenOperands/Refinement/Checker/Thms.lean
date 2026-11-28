module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Refinement.Checker.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Refinement.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Refinement.Checker.Correctness

/-! # Correctness of the finite reply comparison -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Category.FiniteIteration
open CFG.Dependent.Native (withExitUB)
open TwoRequest (Exits)
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
  (accepted_iff counterexample_correct native_check_iff native_probe_sound)

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ} [DecidableEq Φ]

/-- Exhaustive typed reply lists suffice to check the logical relation. -/
theorem Tree.compare_accepted_iff (replies : ReplyEnumeration S) (p q : Tree S) :
    (p.compare replies q).accepted = true ↔ p.Refines q :=
  accepted_iff replies p q

/-- The exact prefix selected by comparison can be executed by the existing
deterministic prefix handler. -/
theorem Tree.compare_counterexample {replies : ReplyEnumeration S} {p q : Tree S}
    {n : Nat} {probe : Prefix S.replies n} (checked : p.compare replies q = .counterexample n probe) :
    p.Follows probe ∧ q.Follows probe ∧
      ¬ (p.execute (S.primitives probe.handler) 0).refines (q.execute (S.primitives probe.handler) 0) :=
  counterexample_correct checked

section Native

variable {replies : ReplyEnumeration S} {R₀ R₁ : List Syntax.Ty}
  {g₀ : Table S R₀} {g₁ : Table S R₁}
  {raw₀ : CFG.Dependent.Native.Typed Φ [R₀.get g₀.entry] Exits}
  {raw₁ : CFG.Dependent.Native.Typed Φ [R₁.get g₁.entry] Exits}
  {input : Syntax.Payload (R₀.get g₀.entry)}
  {p q : Tree S}

/-- After successful readback, the Boolean verdict decides the existing
deterministic shaped refinement judgment at the supplied caller packet. -/
theorem Table.checkRefinement_iff (same : R₀.get g₀.entry = R₁.get g₁.entry)
    (left : g₀.extract? raw₀ input = some p)
    (right : g₁.extract? raw₁ (cast (congrArg Syntax.Payload same) input) = some q) :
    g₀.checkRefinement? g₁ replies raw₀ raw₁ same input = some true ↔
      ∀ (n : Nat) (prim : Syntax.Primitives Φ n) (s : Fin n),
        Shape.denote (withExitUB raw₀ g₀.selected) (Syntax.model prim (g₀.bindings input)) s ≤
          Shape.denote (withExitUB raw₁ g₁.selected)
            (Syntax.model prim (g₁.bindings (cast (congrArg Syntax.Payload same) input))) s :=
  native_check_iff same left right

/-- The returned feasible prefix refutes the original native endpoints
within both extraction budgets. The handler uses one additional test state. -/
theorem Table.compare_counterexample (same : R₀.get g₀.entry = R₁.get g₁.entry)
    (left : g₀.extract? raw₀ input = some p)
    (right : g₁.extract? raw₁ (cast (congrArg Syntax.Payload same) input) = some q)
    {n : Nat} {probe : Prefix S.replies n}
    (checked : g₀.compare? g₁ replies raw₀ raw₁ same input = some (.counterexample n probe)) :
    n ≤ min ((g₀.ranks.get g₀.entry).getD 0 + 1) ((g₁.ranks.get g₁.entry).getD 0 + 1) ∧
      p.Follows probe ∧ q.Follows probe ∧
      ¬ Shape.denote (withExitUB raw₀ g₀.selected)
          (Syntax.model (S.primitives probe.handler) (g₀.bindings input)) 0 ≤
        Shape.denote (withExitUB raw₁ g₁.selected) (Syntax.model (S.primitives probe.handler)
          (g₁.bindings (cast (congrArg Syntax.Payload same) input))) 0 :=
  native_probe_sound same left right checked

end Native

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

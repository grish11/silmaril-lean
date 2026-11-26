module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Refinement.Checker.Interface.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Refinement.Checker.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Refinement.Checker.Interface.Correctness

/-! # A complete verdict over an enumerated typed caller interface -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Category.FiniteIteration
open CFG.Dependent.Native (withExitUB)
open TwoRequest (Exits)
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
  (interface_accepts interface_counterexample)

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] [DecidableEq Φ] {S : RequestSignature Φ}
  {R₀ R₁ : List Syntax.Ty} {g₀ : Table S R₀} {g₁ : Table S R₁}
  {raw₀ : CFG.Dependent.Native.Typed Φ [R₀.get g₀.entry] Exits}
  {raw₁ : CFG.Dependent.Native.Typed Φ [R₁.get g₁.entry] Exits}
  {replies : ReplyEnumeration S} {callers : CallerEnumeration (R₀.get g₀.entry)}

/-- An absent verdict reports a failed exact readback or rank check. -/
theorem Table.compareInterface_none_iff (same : R₀.get g₀.entry = R₁.get g₁.entry) :
    g₀.compareInterface? g₁ replies raw₀ raw₁ same callers = none ↔
      g₀.check raw₀ = false ∨ g₁.check raw₁ = false := by
  cases left : g₀.check raw₀ <;> cases right : g₁.check raw₁ <;>
    simp [Table.compareInterface?, left, right]

/-- For checked CFGs, acceptance decides the installed shaped order at all
typed caller packets and all deterministic finite-state primitive models. -/
theorem Table.compareInterface_accepts_iff (same : R₀.get g₀.entry = R₁.get g₁.entry)
    (left : g₀.check raw₀ = true) (right : g₁.check raw₁ = true) :
    g₀.compareInterface? g₁ replies raw₀ raw₁ same callers = some .refines ↔
      ∀ (input : Syntax.Payload (R₀.get g₀.entry)) (n : Nat)
          (prim : Syntax.Primitives Φ n) (s : Fin n),
        Shape.denote (withExitUB raw₀ g₀.selected) (Syntax.model prim (g₀.bindings input)) s ≤
          Shape.denote (withExitUB raw₁ g₁.selected)
            (Syntax.model prim (g₁.bindings (cast (congrArg Syntax.Payload same) input))) s :=
  interface_accepts same left right

/-- The exact returned caller and prefix witness non-refinement at the
original endpoints. The prefix is feasible in both extracted trees and
fits both rank budgets. -/
theorem Table.compareInterface_counterexample (same : R₀.get g₀.entry = R₁.get g₁.entry)
    {w : InterfaceCounterexample S (R₀.get g₀.entry)}
    (checked : g₀.compareInterface? g₁ replies raw₀ raw₁ same callers = some (.counterexample w)) :
    w.input ∈ callers.packets ∧
      ∃ p q, g₀.extract? raw₀ w.input = some p ∧
        g₁.extract? raw₁ (cast (congrArg Syntax.Payload same) w.input) = some q ∧
        w.length ≤ min ((g₀.ranks.get g₀.entry).getD 0 + 1) ((g₁.ranks.get g₁.entry).getD 0 + 1) ∧
        p.Follows w.probe ∧ q.Follows w.probe ∧
        ¬ Shape.denote (withExitUB raw₀ g₀.selected)
            (Syntax.model (S.primitives w.probe.handler) (g₀.bindings w.input)) 0 ≤
          Shape.denote (withExitUB raw₁ g₁.selected) (Syntax.model (S.primitives w.probe.handler)
            (g₁.bindings (cast (congrArg Syntax.Payload same) w.input))) 0 :=
  interface_counterexample same checked

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

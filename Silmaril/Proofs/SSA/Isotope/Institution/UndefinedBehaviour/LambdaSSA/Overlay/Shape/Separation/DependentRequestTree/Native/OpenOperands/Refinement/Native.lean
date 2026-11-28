module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Refinement.Defs
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.TwoRequest.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Refinement.Comparison

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature Prefix)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open CFG.Dependent.Native (withExitUB)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest (Exits result_order)

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ} {R : List Syntax.Ty}

private theorem expand_fits (g : Table S R) (input : Syntax.Payload (R.get g.entry))
    (fuel : Nat) (i : Fin R.length) (ranked : (g.ranks.get i).isSome = true)
    (bound : (g.ranks.get i).getD 0 < fuel) (incoming : Syntax.Payload (R.get i)) :
    (g.expand input fuel i ranked bound incoming).Fits fuel := by
  induction fuel generalizing i with
  | zero => exact (Nat.not_lt_zero _ bound).elim
  | succ fuel ih =>
    rw [Table.expand]
    split
    · trivial
    · rename_i row
      exact (g.ranked_not_diverge ranked row).elim
    · exact fun j a => ih _ _ _ _

private theorem extract_fits (g : Table S R) (ok : g.entryCheck = true)
    (input : Syntax.Payload (R.get g.entry)) :
    (g.extract ok input).Fits ((g.ranks.get g.entry).getD 0 + 1) :=
  expand_fits g input _ g.entry _ _ input

theorem checked_fits [DecidableEq Φ] {R : List Syntax.Ty} {g : Table S R}
    {raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits}
    {input : Syntax.Payload (R.get g.entry)} {p : Tree S}
    (found : g.extract? raw input = some p) : p.Fits ((g.ranks.get g.entry).getD 0 + 1) := by
  unfold Table.extract? at found
  split at found
  · exact (Option.some.inj found) ▸ extract_fits
      g (g.checked_rank ‹g.check raw = true›) input
  · cases found

section Native

variable [DecidableEq Φ] {R₀ R₁ : List Syntax.Ty}
  {g₀ : Table S R₀} {g₁ : Table S R₁}
  {raw₀ : CFG.Dependent.Native.Typed Φ [R₀.get g₀.entry] Exits}
  {raw₁ : CFG.Dependent.Native.Typed Φ [R₁.get g₁.entry] Exits}
  {input : Syntax.Payload (R₀.get g₀.entry)}
  {p q : Tree S}

theorem checked_countermodel (same : R₀.get g₀.entry = R₁.get g₁.entry)
    (left : g₀.extract? raw₀ input = some p)
    (right : g₁.extract? raw₁ (cast (congrArg Syntax.Payload same) input) = some q)
    (fails : ¬ p.Refines q) :
    ∃ (n : Nat) (probe : Prefix S.replies n),
      n ≤ min ((g₀.ranks.get g₀.entry).getD 0 + 1) ((g₁.ranks.get g₁.entry).getD 0 + 1) ∧
      p.Follows probe ∧ q.Follows probe ∧
      ¬ Shape.denote (withExitUB raw₀ g₀.selected)
          (Syntax.model (S.primitives probe.handler) (g₀.bindings input)) 0 ≤
        Shape.denote (withExitUB raw₁ g₁.selected) (Syntax.model (S.primitives probe.handler)
          (g₁.bindings (cast (congrArg Syntax.Payload same) input))) 0 := by
  obtain ⟨n, probe, lp, rp, bad⟩ := separate p q fails
  refine ⟨n, probe, Nat.le_min.mpr ⟨follows_le lp (checked_fits left),
    follows_le rp (checked_fits right)⟩, lp, rp, ?_⟩
  rwa [← g₀.observe_extract left, ← g₁.observe_extract right, result_order]

theorem checked_refines_iff (same : R₀.get g₀.entry = R₁.get g₁.entry)
    (left : g₀.extract? raw₀ input = some p)
    (right : g₁.extract? raw₁ (cast (congrArg Syntax.Payload same) input) = some q) :
    (∀ (n : Nat) (prim : Syntax.Primitives Φ n) (s : Fin n),
      Shape.denote (withExitUB raw₀ g₀.selected) (Syntax.model prim (g₀.bindings input)) s ≤
        Shape.denote (withExitUB raw₁ g₁.selected)
          (Syntax.model prim (g₁.bindings (cast (congrArg Syntax.Payload same) input))) s) ↔
      p.Refines q := by
  constructor
  · intro all
    by_contra bad
    obtain ⟨n, probe, _, _, _, separates⟩ := checked_countermodel same left right bad
    exact separates (all (n + 1) (S.primitives probe.handler) 0)
  · intro related n prim s
    rw [← g₀.observe_extract left prim s, ← g₁.observe_extract right prim s, result_order]
    exact sound p q related prim s

end Native

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

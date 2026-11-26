module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Refinement.Checker.Interface.Defs
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Refinement.Checker.Thms

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest (Exits)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open CFG.Dependent.Native (withExitUB)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] [DecidableEq Φ] {S : RequestSignature Φ}
  {R₀ R₁ : List Syntax.Ty} {g₀ : Table S R₀} {g₁ : Table S R₁}
  {raw₀ : CFG.Dependent.Native.Typed Φ [R₀.get g₀.entry] Exits}
  {raw₁ : CFG.Dependent.Native.Typed Φ [R₁.get g₁.entry] Exits}
  {replies : ReplyEnumeration S} {callers : CallerEnumeration (R₀.get g₀.entry)}

private theorem extract_of_check {R : List Syntax.Ty} {g : Table S R}
    {raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits}
    (ok : g.check raw = true) (input : Syntax.Payload (R.get g.entry)) :
    g.extract? raw input = some (g.extract (g.checked_rank ok) input) := by
  simp [Table.extract?, ok]

theorem interface_accepts (same : R₀.get g₀.entry = R₁.get g₁.entry)
    (left : g₀.check raw₀ = true) (right : g₁.check raw₁ = true) :
    g₀.compareInterface? g₁ replies raw₀ raw₁ same callers = some .refines ↔
      ∀ (input : Syntax.Payload (R₀.get g₀.entry)) (n : Nat)
          (prim : Syntax.Primitives Φ n) (s : Fin n),
        Shape.denote (withExitUB raw₀ g₀.selected) (Syntax.model prim (g₀.bindings input)) s ≤
          Shape.denote (withExitUB raw₁ g₁.selected)
            (Syntax.model prim (g₁.bindings (cast (congrArg Syntax.Payload same) input))) s := by
  let comparison (input : Syntax.Payload (R₀.get g₀.entry)) :=
    (g₀.extract (g₀.checked_rank left) input).compare replies
      (g₁.extract (g₁.checked_rank right) (cast (congrArg Syntax.Payload same) input))
  let trial := fun input => (comparison input).counterexampleAt input
  let found := callers.packets.findSome? trial
  rw [Table.compareInterface?, dite_eq_left left, dite_eq_left right]
  change some (match found with
    | none => InterfaceVerdict.refines
    | some w => InterfaceVerdict.counterexample w) = some .refines ↔ _
  have findsNoFailure : (some (match found with
    | none => InterfaceVerdict.refines
    | some w => InterfaceVerdict.counterexample w) = some .refines) ↔ found = none := by
    cases found <;> simp
  rw [findsNoFailure]
  change callers.packets.findSome? trial = none ↔ _
  rw [List.findSome?_eq_none_iff]
  have pointwise (input : Syntax.Payload (R₀.get g₀.entry)) :
      trial input = none ↔
        ∀ (n : Nat) (prim : Syntax.Primitives Φ n) (s : Fin n),
          Shape.denote (withExitUB raw₀ g₀.selected) (Syntax.model prim (g₀.bindings input)) s ≤
            Shape.denote (withExitUB raw₁ g₁.selected)
              (Syntax.model prim (g₁.bindings (cast (congrArg Syntax.Payload same) input))) s := by
    have accepted : trial input = none ↔ (comparison input).accepted = true := by
      change (comparison input).counterexampleAt input = none ↔ (comparison input).accepted = true
      cases comparison input <;> simp [Verdict.counterexampleAt, Verdict.accepted]
    exact accepted.trans ((Tree.compare_accepted_iff replies _ _).trans
      (Table.refines_iff same (extract_of_check left input)
        (extract_of_check right (cast (congrArg Syntax.Payload same) input))).symm)
  exact ⟨fun all input => (pointwise input).mp (all input (callers.complete input)),
    fun all input _ => (pointwise input).mpr (all input)⟩

theorem interface_counterexample (same : R₀.get g₀.entry = R₁.get g₁.entry)
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
            (g₁.bindings (cast (congrArg Syntax.Payload same) w.input))) 0 := by
  unfold Table.compareInterface? at checked
  split at checked
  · rename_i left
    split at checked
    · rename_i right
      let lower (input : Syntax.Payload (R₀.get g₀.entry)) := g₀.extract (g₀.checked_rank left) input
      let upper (input : Syntax.Payload (R₀.get g₀.entry)) :=
        g₁.extract (g₁.checked_rank right) (cast (congrArg Syntax.Payload same) input)
      let trial := fun input => ((lower input).compare replies (upper input)).counterexampleAt input
      change some (match callers.packets.findSome? trial with
        | none => InterfaceVerdict.refines
        | some w => InterfaceVerdict.counterexample w) = some (.counterexample w) at checked
      have found : callers.packets.findSome? trial = some w := by
        cases look : callers.packets.findSome? trial with
        | none => simp [look] at checked
        | some found => simpa [look] using checked
      obtain ⟨input, listed, hit⟩ := List.exists_of_findSome?_eq_some found
      change ((lower input).compare replies (upper input)).counterexampleAt input = some w at hit
      cases compared : (lower input).compare replies (upper input) with
      | refines => simp [Verdict.counterexampleAt, compared] at hit
      | counterexample n probe =>
        have sameWitness : (⟨input, n, probe⟩ : InterfaceCounterexample S _) = w := by
          simpa only [Verdict.counterexampleAt, compared, Option.some.injEq] using hit
        subst w
        have lp := extract_of_check left input
        have rp := extract_of_check right (cast (congrArg Syntax.Payload same) input)
        have point : g₀.compare? g₁ replies raw₀ raw₁ same input = some (.counterexample n probe) := by
          simpa [Table.compare?, lp, rp] using congrArg some compared
        exact ⟨listed, lower input, upper input, lp, rp, Table.compare_counterexample same lp rp point⟩
    · cases checked
  · cases checked

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

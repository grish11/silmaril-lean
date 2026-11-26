module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Refinement.Checker.Defs
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Refinement.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.TwoRequest.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Refinement.Comparison

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest (Exit Exits result_order)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open CFG.Dependent.Native (withExitUB)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature Prefix)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ} [DecidableEq Φ]

private def Correct (p q : Tree S) : Verdict S → Prop
  | .refines => p.Refines q
  | .counterexample _ probe => p.Follows probe ∧ q.Follows probe ∧
      ¬ (p.execute (S.primitives probe.handler) 0).refines (q.execute (S.primitives probe.handler) 0)

private theorem compare_correct (replies : ReplyEnumeration S) (p q : Tree S) :
    Correct p q (p.compare replies q) := by
  induction p generalizing q with
  | stop a =>
    cases q with
    | stop b =>
      rw [Tree.compare]
      split
      · exact ‹b = .ub ∨ a = b›
      · exact ⟨.stop _ _, .stop _ _, fun h => ‹¬ (b = .ub ∨ a = b)› ((exit_order a b 0).mp h)⟩
    | ask g arg next =>
      refine ⟨.stop _ _, .stop _ _, ?_⟩
      change ¬ ((Tree.stop a).execute (S.primitives (Prefix.stop none).handler) 0).refines
        ((Tree.ask g arg next).execute (S.primitives (Prefix.stop none).handler) 0)
      rw [execute_ask]
      cases a <;> simp [Tree.execute, Prefix.handler, Exit.result, Result.refines]
  | ask f arg arms ih =>
    cases q with
    | stop b =>
      cases b with
      | ub => trivial
      | ret i =>
        refine ⟨.stop _ _, .stop _ _, ?_⟩
        change ¬ ((Tree.ask f arg arms).execute (S.primitives (Prefix.stop none).handler) 0).refines
          ((Tree.stop (.ret i)).execute (S.primitives (Prefix.stop none).handler) 0)
        rw [execute_ask]
        simp [Tree.execute, Prefix.handler, Exit.result, Result.refines]
    | ask g arg' next =>
      rw [Tree.compare]
      split
      · rename_i same
        obtain ⟨keys, values⟩ := Prod.mk.inj same
        subst g
        have sameArg : arg = arg' := Subtype.ext values
        subst arg'
        let test (reply : CFG.Dependent.Packet (S.replies f)) : Option (Verdict S) :=
          match (arms reply.1 reply.2).compare replies (next reply.1 reply.2) with
          | .refines => none
          | .counterexample n probe =>
            some (.counterexample (n + 1) (.step f arg.val reply.1 reply.2 probe))
        change Correct (Tree.ask f arg arms) (Tree.ask f arg next)
          (((replies.packets f).findSome? test).getD .refines)
        cases found : (replies.packets f).findSome? test with
        | none =>
          refine ⟨rfl, rfl, fun i a => ?_⟩
          have passes := (List.findSome?_eq_none_iff.mp found) ⟨i, a⟩ (replies.complete f ⟨i, a⟩)
          have cert := ih i a (next i a)
          cases checked : (arms i a).compare replies (next i a) with
          | refines => rwa [checked] at cert
          | counterexample n probe => simp [test, checked] at passes
        | some verdict =>
          obtain ⟨⟨i, a⟩, _, foundHere⟩ := List.exists_of_findSome?_eq_some found
          have cert := ih i a (next i a)
          cases checked : (arms i a).compare replies (next i a) with
          | refines => simp [test, checked] at foundHere
          | counterexample n probe =>
            simp only [test, checked, Option.some.injEq] at foundHere
            subst verdict
            rw [checked] at cert
            obtain ⟨lp, rp, bad⟩ := cert
            refine ⟨.step lp, .step rp, ?_⟩
            change ¬ ((Tree.ask f arg arms).execute
              (S.primitives (Prefix.step f arg.val i a probe).handler) 0).refines
              ((Tree.ask f arg next).execute (S.primitives (Prefix.step f arg.val i a probe).handler) 0)
            rwa [prefix_step_order]
      · rename_i off
        refine ⟨.stop _ _, .stop _ _, ?_⟩
        have different : ¬ (f = g ∧ arg.val = arg'.val) :=
          fun ⟨key, value⟩ => off (Prod.ext key value)
        change ¬ ((Tree.ask f arg arms).execute
          (S.primitives (Prefix.stop (some (f, arg.val))).handler) 0).refines
          ((Tree.ask g arg' next).execute (S.primitives (Prefix.stop (some (f, arg.val))).handler) 0)
        rw [execute_ask, execute_ask]
        simp [Prefix.handler, different, Result.refines]

theorem accepted_iff (replies : ReplyEnumeration S) (p q : Tree S) :
    (p.compare replies q).accepted = true ↔ p.Refines q := by
  have cert := compare_correct replies p q
  cases checked : p.compare replies q with
  | refines => simpa [checked, Verdict.accepted, Correct] using cert
  | counterexample n probe =>
    rw [checked] at cert
    simp only [Verdict.accepted, Bool.false_eq_true, false_iff]
    exact fun h => cert.2.2 (sound p q h (S.primitives probe.handler) 0)

theorem counterexample_correct {replies : ReplyEnumeration S} {p q : Tree S}
    {n : Nat} {probe : Prefix S.replies n} (checked : p.compare replies q = .counterexample n probe) :
    p.Follows probe ∧ q.Follows probe ∧
      ¬ (p.execute (S.primitives probe.handler) 0).refines (q.execute (S.primitives probe.handler) 0) := by
  have cert := compare_correct replies p q
  rwa [checked] at cert

section Native

variable {replies : ReplyEnumeration S} {R₀ R₁ : List Syntax.Ty}
  {g₀ : Table S R₀} {g₁ : Table S R₁}
  {raw₀ : CFG.Dependent.Native.Typed Φ [R₀.get g₀.entry] Exits}
  {raw₁ : CFG.Dependent.Native.Typed Φ [R₁.get g₁.entry] Exits}
  {input : Syntax.Payload (R₀.get g₀.entry)}
  {p q : Tree S}

theorem native_check_iff (same : R₀.get g₀.entry = R₁.get g₁.entry)
    (left : g₀.extract? raw₀ input = some p)
    (right : g₁.extract? raw₁ (cast (congrArg Syntax.Payload same) input) = some q) :
    g₀.checkRefinement? g₁ replies raw₀ raw₁ same input = some true ↔
      ∀ (n : Nat) (prim : Syntax.Primitives Φ n) (s : Fin n),
        Shape.denote (withExitUB raw₀ g₀.selected) (Syntax.model prim (g₀.bindings input)) s ≤
          Shape.denote (withExitUB raw₁ g₁.selected)
            (Syntax.model prim (g₁.bindings (cast (congrArg Syntax.Payload same) input))) s := by
  rw [Table.refines_iff same left right]
  simp [Table.checkRefinement?, Table.compare?, left, right, accepted_iff]

theorem native_probe_sound (same : R₀.get g₀.entry = R₁.get g₁.entry)
    (left : g₀.extract? raw₀ input = some p)
    (right : g₁.extract? raw₁ (cast (congrArg Syntax.Payload same) input) = some q)
    {n : Nat} {probe : Prefix S.replies n}
    (checked : g₀.compare? g₁ replies raw₀ raw₁ same input = some (.counterexample n probe)) :
    n ≤ min ((g₀.ranks.get g₀.entry).getD 0 + 1) ((g₁.ranks.get g₁.entry).getD 0 + 1) ∧
      p.Follows probe ∧ q.Follows probe ∧
      ¬ Shape.denote (withExitUB raw₀ g₀.selected)
          (Syntax.model (S.primitives probe.handler) (g₀.bindings input)) 0 ≤
        Shape.denote (withExitUB raw₁ g₁.selected) (Syntax.model (S.primitives probe.handler)
          (g₁.bindings (cast (congrArg Syntax.Payload same) input))) 0 := by
  have found : p.compare replies q = .counterexample n probe := by
    simpa [Table.compare?, left, right] using checked
  obtain ⟨lp, rp, bad⟩ := counterexample_correct found
  refine ⟨Nat.le_min.mpr ⟨lp.le_budget (Table.fits_of_extract left),
    rp.le_budget (Table.fits_of_extract right)⟩, lp, rp, ?_⟩
  rwa [← g₀.observe_extract left, ← g₁.observe_extract right, result_order]

end Native

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

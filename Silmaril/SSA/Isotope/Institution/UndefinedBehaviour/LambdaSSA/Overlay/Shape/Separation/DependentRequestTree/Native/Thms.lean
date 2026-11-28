module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.Defs
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.Soundness

/-! # Transporting finite shaped separation to checked native endpoints -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction

open Category.FiniteIteration
open Category.FiniteIteration.CFG.Dependent.Native (withExitUB)
open TwoRequest (Exits)

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] [DecidableEq Φ]
  {S : RequestSignature Φ} {R Q : List Syntax.Ty}
  {raw target : CFG.Dependent.Native.Typed Φ [] Exits}

theorem Table.checked_native {g : Table S R} (ok : g.check raw = true) : raw = g.native := by
  simp only [Table.check, Bool.and_eq_true] at ok
  exact Subtype.ext (CFG.Dependent.Native.sameRegion_eq ok.1)

/-- Each accepted source is the original typed CFG decorated at its ordered
exits. The observation agrees with its extracted tree for all executable
deterministic shaped primitives, including argument-sensitive primitives. -/
theorem Table.observe {g : Table S R} (ok : g.check raw = true) {n : Nat}
    (prim : Syntax.Primitives Φ n) (s : Fin n) :
    Shape.denote ((g.extract (g.checked_rank ok)).region S)
        (Syntax.model prim Syntax.emptyBindings) s =
      Shape.denote (withExitUB raw g.selected) (Syntax.model prim Syntax.emptyBindings) s := by
  calc
    _ = Shape.denote (withExitUB g.native g.selected) (Syntax.model prim Syntax.emptyBindings) s :=
      Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.agrees
        g (g.checked_rank ok) prim s
    _ = _ := congrArg (fun (r : CFG.Dependent.Native.Typed Φ [] Exits) =>
      Shape.denote (withExitUB r g.selected) (Syntax.model prim Syntax.emptyBindings) s)
      (g.checked_native ok).symm

/-- Successful extraction returns a tree for the checked native input. -/
theorem Table.observe_extract {g : Table S R} {tree : Tree S.replies}
    (found : g.extract? raw = some tree) {n : Nat} (prim : Syntax.Primitives Φ n) (s : Fin n) :
    Shape.denote (tree.region S) (Syntax.model prim Syntax.emptyBindings) s =
      Shape.denote (withExitUB raw g.selected) (Syntax.model prim Syntax.emptyBindings) s := by
  unfold Table.extract? at found
  split at found
  · exact (Option.some.inj found) ▸ g.observe ‹g.check raw = true› prim s
  · cases found

/-- A failed tree comparison refutes refinement at the actual typed entries.
The same bounded prefix model is used for both original CFGs. -/
theorem exists_countermodel {g : Table S R} {h : Table S Q}
    (left : g.check raw = true) (right : h.check target = true)
    (fails : ¬ (g.extract (g.checked_rank left)).Refines (h.extract (h.checked_rank right))) :
    ∃ (n : Nat) (probe : Prefix S.replies n),
      n ≤ min (g.extract (g.checked_rank left)).depth (h.extract (h.checked_rank right)).depth ∧
        ¬ Shape.denote (withExitUB raw g.selected) (S.model probe.handler) 0 ≤
          Shape.denote (withExitUB target h.selected) (S.model probe.handler) 0 := by
  obtain ⟨n, probe, bound, bad⟩ := exists_prefix_countermodel (S := S) fails
  refine ⟨n, probe, bound, fun le => bad ?_⟩
  let prim := S.primitives probe.handler
  exact (g.observe left prim 0).trans_le (le.trans_eq (h.observe right prim 0).symm)

/-- The transported order is exact over the deterministic shaped models of
the installed finite primitive API. -/
theorem finite_refines_iff {g : Table S R} {h : Table S Q}
    (left : g.check raw = true) (right : h.check target = true) :
    (∀ (n : Nat) (prim : Syntax.Primitives Φ n) (s : Fin n),
      Shape.denote (withExitUB raw g.selected) (Syntax.model prim Syntax.emptyBindings) s ≤
      Shape.denote (withExitUB target h.selected) (Syntax.model prim Syntax.emptyBindings) s) ↔
      (g.extract (g.checked_rank left)).Refines (h.extract (h.checked_rank right)) := by
  refine ⟨fun all => Classical.byContradiction fun fails => ?_, fun le n prim s => ?_⟩
  · obtain ⟨n, probe, _, bad⟩ := exists_countermodel left right fails
    exact bad (all (n + 1) (S.primitives probe.handler) 0)
  · rw [← g.observe left prim s, ← h.observe right prim s]
    exact shaped_sound (S := S) _ _ le (Syntax.model prim Syntax.emptyBindings) s

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction

module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Defs
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Soundness

/-! # Agreement of open-operand extraction with the original native CFG -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Category.FiniteIteration
open Category.FiniteIteration.CFG.Dependent.Native (withExitUB)
open TwoRequest (Exits resultBehaviour)

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] [DecidableEq Φ]
  {S : RequestSignature Φ} {R : List Syntax.Ty}
  {g : Table S R} {raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits}

theorem Table.checked_reemission (ok : g.checkNative raw = true) : raw = g.native :=
  Subtype.ext (CFG.Dependent.Native.sameRegion_eq ok)

theorem Table.checked_native (ok : g.check raw = true) : raw = g.native := by
  simp only [Table.check, Bool.and_eq_true] at ok
  exact g.checked_reemission ok.1

/-- Execution of the extracted tree retains the complete shaped observation
of the original native endpoint at the supplied typed entry value. -/
theorem Table.observe (ok : g.check raw = true) (input : Syntax.Payload (R.get g.entry))
    {n : Nat} (prim : Syntax.Primitives Φ n) (s : Fin n) :
    resultBehaviour ((g.extract (g.checked_rank ok) input).execute prim s) =
      Shape.denote (withExitUB raw g.selected) (Syntax.model prim (g.bindings input)) s :=
  (Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.agrees
    g (g.checked_rank ok) input prim s).trans (congrArg (fun (r : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits) =>
      Shape.denote (withExitUB r g.selected) (Syntax.model prim (g.bindings input)) s) (g.checked_native ok).symm)

/-- A successful executable extraction carries the same observation
certificate at every initial machine state of the supplied interpreter. -/
theorem Table.observe_extract {input : Syntax.Payload (R.get g.entry)} {tree : Tree S}
    (found : g.extract? raw input = some tree) {n : Nat} (prim : Syntax.Primitives Φ n) (s : Fin n) :
    resultBehaviour (tree.execute prim s) =
      Shape.denote (withExitUB raw g.selected) (Syntax.model prim (g.bindings input)) s := by
  unfold Table.extract? at found
  split at found
  · exact (Option.some.inj found) ▸ g.observe ‹g.check raw = true› input prim s
  · cases found

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

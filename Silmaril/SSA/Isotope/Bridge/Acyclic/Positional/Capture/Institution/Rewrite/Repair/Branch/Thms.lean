module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Branch.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Branch.Normalize

/-! # Normalization of the typed input case -/

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Branch

open Sequence (Sorts)
open Isotope.LetCase.LocallyNameless (AbortEquiv)

/-- The comparison uses the actual typed operands emitted by the captured grammar. -/
theorem ProgramBody.program_rendered (tail : List Sorts) (p : ProgramBody) :
    (p.program tail).toLetCase = p.rendered tail :=
  program_rendered_proof tail p

/-- Replay native constructor case β and pure let β before applying the
opt-in empty rule to the selected ordered effect sequence. -/
theorem Arm.normalize (a : Arm) {n : Nat} (β : BoundCtx Sorts n) :
    AbortEquiv false (Ctx.nil : Ctx Empty Sorts) β
      (a.operand β).1 (a.selected.canonical.operand β).1 Ty.unit :=
  normalize_arm_proof a β

theorem repaired_of_normal (tail : List Sorts) (p q : ProgramBody) (h : p.normal = q.normal) :
    Repaired false (equation tail p q) :=
  repaired_of_normal_proof tail p q h

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Branch

module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.WSet.Examples.Defs

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.WSet.Examples

universe u

noncomputable section

/-- The step has the full dependent W telescope, for a singleton motive. -/
theorem constantStep_typing (A : ZFSet.{u}) (B : ZFSet.{u} → ZFSet.{u}) (z : ZFSet.{u}) :
    constantStep A B z ∈ stepType A B (fun _ => {z}) := by
  apply SetSem.lam_mem_pi
  intro a _
  apply SetSem.lam_mem_pi
  intro f _
  apply SetSem.lam_mem_pi
  intro ih _
  simp

/-- Dependent membership recovers the result on arbitrary well-founded trees. -/
theorem wrec_constant {A t : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}}
    (z : ZFSet.{u}) (ht : t ∈ carrier A B) : wrec A B (constantStep A B z) t = z := by
  simpa only [ZFSet.mem_singleton] using wrec_mem (constantStep_typing A B z) ht

/-- The result applies to a concrete inhabitant, without any theory hypotheses. -/
theorem leaf_wrec :
    wrec SetSem.tt (fun _ => ∅) (constantStep SetSem.tt (fun _ => ∅) (∅ : ZFSet.{u}))
      leaf.val = ∅ :=
  wrec_constant ∅ leaf.property

end
end Silmaril.Logic.TypeTheory.ExtensionalMLTT.WSet.Examples

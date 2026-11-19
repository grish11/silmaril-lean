module

public import Silmaril.Semantics.Region.Abstract.Examples.Defs
public import Silmaril.Semantics.Region.Abstract.Named.Thms
import Silmaril.Proofs.Semantics.Region.LatticeExamples

@[expose] public section
namespace Silmaril.Semantics.Region.Abstract.Examples

theorem left_closed : Closed rules left := Proofs.left_closed

theorem right_closed : Closed rules right := Proofs.right_closed

/-- Union omits the multi-premise consequence even though each model is lawful. -/
theorem union_not_closed : ¬ Closed rules (left ∪ right) := Proofs.union_not_closed

/-- The lawful join supplies precisely the sort of consequence union can miss. -/
theorem composed_in_join :
    atom 2 ∈ ((⟨left, left_closed⟩ : ClosedModel rules) ⊔ ⟨right, right_closed⟩).val :=
  Proofs.composed_in_join left_closed right_closed

/-- Different existential witnesses prevent raw erasure from preserving meets. -/
theorem forget_not_meet :
    forget (fun _ : Atom => ()) (left ∩ right) ≠
      forget (fun _ : Atom => ()) left ∩ forget (fun _ : Atom => ()) right := Proofs.forget_not_meet

/-- Adding nonemptiness to the lawful subtype destroys intersection closure. -/
theorem nonempty_not_meet : left.Nonempty ∧ right.Nonempty ∧ ¬ (left ∩ right).Nonempty :=
  Proofs.nonempty_not_meet

example : CompleteLattice (LawfulRegionModel rules) := inferInstance

end Silmaril.Semantics.Region.Abstract.Examples

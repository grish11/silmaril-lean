module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.BitFragment.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.BitNormalization
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.BitReflection

/-! # Reflection at the original packed case, call and let source -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment

open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery (Exits)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree (inputSlots Difference)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)

/-- Normalize the written source in the common quotient. Its scope and
arm choice come entirely from the syntax. -/
theorem Program.replay (p : Program) :
    Eqv false [Bit] p.region (p.tree.writtenRegion inputSlots) Exits :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.BitFragment.replay p

/-- The entire ordered reply history and typed exit agree with the reflected tree. -/
theorem Program.observations_eq (p : Program) (g : Bool) :
    p.observations g = p.tree.outcomes (fun _ => g) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.BitFragment.observations_eq p g

/-- A decision on the reflected tree key decides equality at the original packed arrows. -/
theorem Program.packed_eq_iff_key (p q : Program) : p.packed = q.packed ↔ p.tree.key = q.tree.key :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.BitFragment.packed_eq_iff_key p q

/-- Reflect the actual acyclic compiler outputs back to the original packed
quotient arrows on this typed grammar. -/
theorem Program.packed_eq_iff_compiled (p q : Program) : p.packed = q.packed ↔ p.CompiledEq q :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.BitFragment.packed_eq_iff_compiled p q

/-- A separating history for the trees is a separating history at the original packed endpoints. -/
theorem Program.separate_some (p q : Program) {w : Difference} (h : p.tree.separate? q.tree = some w) :
    w.history.observation ∈ (if w.fromRight then q else p).observations w.guard ∧
      w.history.observation ∉ (if w.fromRight then p else q).observations w.guard :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.BitFragment.separate_some p q h

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment

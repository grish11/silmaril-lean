module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.Regularity.Thms
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.Derivation.Examples

public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT

/-- A zero-budget context judgment still has an actual one-level carrier formation. -/
theorem bounded_zero_budget_regularity :
    ∃ n, n < 1 ∧ ECtx.JEqB 1 ∅ .nil (.univ n) .unit .unit :=
  (ECtx.JEqB.nil_ok (levels := 0) (H := ∅)).type_formation

/-- The carrier of natural-number formation fits at the next rule budget. -/
theorem bounded_nats_carrier_regularity :
    ∃ n, n < 2 ∧ ECtx.JEqB 2 ∅ .nil (.univ n) (.univ 0) (.univ 0) :=
  bounded_nats.type_formation

/-- Universe formation also raises the carrier's available budget by just one. -/
theorem bounded_univ_carrier_regularity :
    ∃ n, n < 3 ∧ ECtx.JEqB 3 ∅ .nil (.univ n) (.univ 1) (.univ 1) :=
  bounded_univ_zero.type_formation

/-- A nonempty name context supplies actual lookup formation without raising levels. -/
theorem bounded_nats_lookup_regularity :
    ∃ n, n < 1 ∧ ECtx.JEqB 1 ∅ (.cons .nil "x" .nats) (.univ n) .nats .nats :=
  (bounded_nats_context "x").lookup_formation (.here _ _ _)

/-- Nat successor computation retains its uniformly bounded cofinite motives. -/
theorem bounded_nat_successor_regularity :
    ∃ n, n < 2 ∧ ECtx.JEqB 2 ∅ .nil (.univ n) .nats .nats :=
  bounded_nat_successor.type_formation

end Silmaril.Logic.TypeTheory.ExtensionalMLTT

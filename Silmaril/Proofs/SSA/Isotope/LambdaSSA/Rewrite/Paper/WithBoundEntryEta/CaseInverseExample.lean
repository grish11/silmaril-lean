module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Case.Inverse.Example.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Case.Inverse.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Case.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Script.Example.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Script.Example.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.CaseInverseExample

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithBoundEntryEta.CaseReplay
open Paper.WithBoundEntryEta.CaseReplay.InverseExample
open Paper.WithBoundEntryEta.CaseReplay.Example (site specialize)
open Paper.WithBoundEntryEta.Generators.Example (Choice discriminator)
open Paper.WithBoundEntryEta.NestedReplay.Example (outerRows)
open Paper.EntryLetObstruction.Destructure (U P labels)

theorem commonTable : CommonTableAt [Choice] [U] site hoisted := by
  have disc : Tm.HasType [Choice] discriminator Choice := .let₁ (.op .unit) (.var (i := 1) rfl)
  have rows (j : Fin 2) : HasType (labels j :: [Choice]) (outerRows j) [U, P, U] :=
    Fin.cases (.br (ℓ := 1) rfl (.pair (.var rfl) .unit))
      (fun _ => .case (.var (i := 1) rfl) (.br (ℓ := 2) rfl (.var rfl)) (.br (ℓ := 2) rfl .unit)) j
  exact .unaryBody .unit (.here labels (disc.rename (Ren.wk [Choice] U))
    (.br (ℓ := 0) rfl (.var rfl)) (.br (ℓ := 1) rfl (.var rfl))
    (fun j => (rows j).renameVars ((Ren.wk [Choice] U).lift (labels j))))

private theorem forward : hoistAt site original = some hoisted := rfl

theorem backward :
    hoistAt site (original.substVars specialize) = some (hoisted.substVars specialize) ∧
    HasType [Choice] original [U] ∧ Paper.WithBoundEntryEta.Eqv [Choice] hoisted original [U] := by
  have step : hoistAt site (original.substVars specialize) = some (hoisted.substVars specialize) := by
    rw [hoistAt_substVars, forward]
    rfl
  obtain ⟨q, hq, _, ht, eq⟩ := inverse_pullback commonTable specialize step
  have same := hoistAt_injective site hq forward
  subst q
  exact ⟨step, ht, eq⟩

theorem unequalTables_ineligible :
    ¬ CommonTableAt [U, U] [U] .here Paper.WithBoundEntryEta.ScriptReplay.Example.inverseTarget := by
  intro h
  obtain ⟨q, _, hq⟩ := h.predecessor
  refine Paper.WithBoundEntryEta.ScriptReplay.Example.inverse_obstruction.2.2 ⟨q, ?_⟩
  change (hoistAt .here q >>= Paper.WithBoundEntryEta.ScriptReplay.run []) = _
  rw [hq]
  rfl

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.CaseInverseExample

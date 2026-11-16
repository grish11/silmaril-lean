module

public import Silmaril.Project.Shapes.Consequence.Thms
public import Silmaril.Logic.Consequence.Multi.Examples

/-!
# The `sil project` self-test: a multiple-conclusion system

`Silmaril.Consequence.Examples.litMulti` (`Silmaril.Logic.Consequence.Multi.Examples`):
truth-table consequence `Γ ⊢ Δ` between lists of literals over one atom `p`, valid when every
valuation satisfying all of `Γ` satisfies some literal of `Δ`. A `MultiSystem` is a
`System` over lists, so it registers with `silmaril consequence_system` and the standard shapes
as they are; the answers are that module's named judgements:

* the empty succedent `[]` is the chosen `ff` of `derives_bottom`: `p, -p ⊢` holds, `p ⊢` does
  not;
* with the empty antecedent, `⊢ p, -p` (excluded middle) holds and `⊢ p` does not;
* `rightExt litMulti.single` (some single conclusion follows) is sound for `litMulti` but not
  complete: `⊢ p, -p` is the kept counterexample.
-/

namespace ProjectSelfTest.Consequence.Multi

open Silmaril.Consequence Silmaril.Consequence.Examples

@[expose] public section

/-- Some single conclusion of the succedent follows. -/
def litRightExt : MultiSystem (Signed Unit) (Signed Unit) := rightExt litMulti.single

end

end ProjectSelfTest.Consequence.Multi

silmaril consequence_system silmaril.selftest.consequence.multi.lit :=
  Silmaril.Consequence.Examples.litMulti
  (title := "Truth-table consequence between lists of one-atom literals (multiple conclusions)")
silmaril consequence_system silmaril.selftest.consequence.multi.right_ext :=
  ProjectSelfTest.Consequence.Multi.litRightExt
  (title := "Some single conclusion follows (rightExt of the single-conclusion part)")

open ProjectSelfTest.Consequence.Multi Silmaril.Consequence Silmaril.Consequence.Examples
  Silmaril.Project.Shapes.Consequence in
section

silmaril instance silmaril.selftest.consequence.multi.contradiction (expect := THM)
  (title := "p, -p ⊢ (the empty succedent)") := silmaril.shapes.consequence.derives_bottom
  (S := Silmaril.Consequence.Examples.litMulti) (ff := [])
  (Γ := [Silmaril.Consequence.Examples.p, -Silmaril.Consequence.Examples.p])

@[answers "silmaril.selftest.consequence.multi.contradiction" thm]
public theorem contradiction : DerivesBottom litMulti [] [p, -p] := Examples.contradiction

silmaril instance silmaril.selftest.consequence.multi.p_nil (expect := UNS)
  (title := "p ⊢ (fails: p alone is satisfiable)") := silmaril.shapes.consequence.derives_bottom
  (S := Silmaril.Consequence.Examples.litMulti) (ff := []) (Γ := [Silmaril.Consequence.Examples.p])

@[answers "silmaril.selftest.consequence.multi.p_nil" csa]
public theorem p_nil : ¬ DerivesBottom litMulti [] [p] := not_p_nil

silmaril instance silmaril.selftest.consequence.multi.excluded_middle (expect := THM)
  (title := "⊢ p, -p (excluded middle)") := silmaril.shapes.consequence.derives
  (S := Silmaril.Consequence.Examples.litMulti) (Γ := [])
  (φ := [Silmaril.Consequence.Examples.p, -Silmaril.Consequence.Examples.p])

@[answers "silmaril.selftest.consequence.multi.excluded_middle" thm]
public theorem excluded_middle : Derives litMulti [] [p, -p] := excludedMiddle

silmaril instance silmaril.selftest.consequence.multi.nil_p (expect := UNS)
  (title := "⊢ p (fails: p is not a tautology)") := silmaril.shapes.consequence.derives
  (S := Silmaril.Consequence.Examples.litMulti) (Γ := []) (φ := [Silmaril.Consequence.Examples.p])

@[answers "silmaril.selftest.consequence.multi.nil_p" csa]
public theorem nil_p : ¬ Derives litMulti [] [p] := not_nil_p

silmaril instance silmaril.selftest.consequence.multi.right_ext_sound (expect := THM)
  (title := "Some single conclusion following is sound for litMulti") :=
  silmaril.shapes.consequence.sound_at
  (S := ProjectSelfTest.Consequence.Multi.litRightExt) (T := Silmaril.Consequence.Examples.litMulti)

@[answers "silmaril.selftest.consequence.multi.right_ext_sound" thm]
public theorem right_ext_sound : ∀ Γ Δ, SoundAt litRightExt litMulti Γ Δ := by
  rintro Γ Δ ⟨d, hd, h⟩ m hm
  obtain ⟨d', hd', hs⟩ := h m hm
  exact ⟨d', by simp only [List.mem_singleton] at hd'; exact hd' ▸ hd, hs⟩

silmaril instance silmaril.selftest.consequence.multi.right_ext_complete (expect := CSA)
  (title := "Some single conclusion following is complete for litMulti (fails: ⊢ p, -p)") :=
  silmaril.shapes.consequence.complete_at
  (S := ProjectSelfTest.Consequence.Multi.litRightExt) (T := Silmaril.Consequence.Examples.litMulti)

@[answers "silmaril.selftest.consequence.multi.right_ext_complete" csa]
public theorem right_ext_complete : ∃ Γ Δ, ¬ CompleteAt litRightExt litMulti Γ Δ :=
  ⟨[], [p, -p], fun h => not_rightExt_excludedMiddle (h excludedMiddle)⟩

end

silmaril group silmaril.selftest.consequence.multi
  (title := "Consequence systems: multiple conclusions (one-atom literals)")
  (children := [silmaril.selftest.consequence.multi.contradiction,
    silmaril.selftest.consequence.multi.p_nil, silmaril.selftest.consequence.multi.excluded_middle,
    silmaril.selftest.consequence.multi.nil_p, silmaril.selftest.consequence.multi.right_ext_sound,
    silmaril.selftest.consequence.multi.right_ext_complete])

module

public import Silmaril.Logic.Egglog.Core.Graph.Examples.Defs

@[expose] public section

namespace Silmaril.Logic.Egglog.Core.Graph.Examples

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples
open Core.Examples

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem selected_lookup (s : Bool) :
    ((sentence lookupQuery).map (signatureMap (selectSort s))).Holds (model twoSortModel) := by
  apply ((reindex (selectSort s)).sat twoSortModel (sentence lookupQuery)).mpr
  apply (sentence_holds _ lookupQuery).mpr
  exact ⟨Fin.elim0, fun _ h => by cases List.mem_singleton.mp h; exact ⟨rfl, rfl⟩⟩

theorem collapse_identifies_sorts : collapseSorts.sorts false = collapseSorts.sorts true := rfl

theorem select_collapse (s : Bool) : selectSort s ≫ collapseSorts = 𝟙 Core.Examples.signature := rfl

theorem composed_translation (s : Bool) :
    ((sentence lookupQuery).map (signatureMap (selectSort s))).map (signatureMap collapseSorts) =
      sentence lookupQuery := by
  change ((sentence lookupQuery).map (signatures.map (selectSort s))).map
    (signatures.map collapseSorts) = sentence lookupQuery
  rw [← FOL.Sentence.map_comp, ← signatures.map_comp, select_collapse, signatures.map_id]
  exact FOL.Sentence.map_id _

theorem original_lookup : (sentence lookupQuery).Holds (model populatedModel) :=
  (sentence_holds _ lookupQuery).mpr
    ⟨Fin.elim0, fun _ h => by cases List.mem_singleton.mp h; exact ⟨rfl, rfl⟩⟩

theorem shifted_lookup_false :
    ¬ ((sentence lookupQuery).map (signatureMap shiftNumerals)).Holds (model populatedModel) := by
  rw [← sentence_map, sentence_holds]
  rintro ⟨ρ, h⟩
  have impossible := h _ (List.mem_singleton_self _)
  exact Nat.noConfusion impossible.1

theorem functional_valid (M : Model Core.Examples.signature) : functionalSentence.Holds (model M) := by
  rw [functionalSentence, EQtoFOL.holds_closeAll]
  intro ρ h
  exact h.2 (M.functional TableSymbol.next (fun _ => ρ 0) (ρ 1) (ρ 2) h.1.1 h.1.2)

theorem unrestricted_fol_countermodel : ¬ functionalSentence.Holds nonfunctionalModel := by
  rw [functionalSentence, EQtoFOL.holds_closeAll]
  change ¬ ∀ ρ : Fin 3 → Nat, ¬ ((True ∧ True) ∧ ¬ ρ 1 = ρ 2)
  intro h
  let ρ : Fin 3 → Nat := Fin.cases 0 (Fin.cases 0 (fun _ => 1))
  exact h ρ ⟨⟨True.intro, True.intro⟩, Nat.zero_ne_one⟩

/-- The graph institution has full Boolean FOL sentences, so it can express
inconsistency even though the positive normalized core cannot negate a query. -/
theorem graph_contradiction :
    ¬ ∃ M : Model Core.Examples.signature,
      (functionalSentence.Holds (model M) ∧
        (⟨functionalSentence.ctx, .not functionalSentence.formula⟩ :
          FOL.Sentence (signature Core.Examples.signature)).Holds (model M)) := by
  rintro ⟨M, hp, hn⟩
  exact hn hp

end Silmaril.Logic.Egglog.Core.Graph.Examples

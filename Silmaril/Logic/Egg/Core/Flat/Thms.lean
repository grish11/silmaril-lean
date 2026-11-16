module

public import Silmaril.Logic.Egg.Core.Flat.Defs
public import Silmaril.Logic.Egg.Core.Thms

@[expose] public section
namespace Silmaril.Logic.Egg.Core.Flat
open Silmaril.Logic.Institution.Examples

/-- The checked producer trace yields the original generic explanation judgment. -/
theorem Replay.certificate {rs a b proofText rulesText startText endText}
    (r : Replay rs a b proofText rulesText startText endText) :
    Explanation (ruleSet rs) ∅ a b := r.trace.certificate

/-- Validity in every algebra of the complete bound rule table, rather than a
solver verdict or equality of merely generated endpoints. -/
theorem Replay.sound {rs a b proofText rulesText startText endText}
    (r : Replay rs a b proofText rulesText startText endText)
    (M : Model signature) (hM : ∀ rule ∈ ruleSet rs, rule.Holds M) :
    a.eval M Fin.elim0 = b.eval M Fin.elim0 :=
  explanation_sound M Fin.elim0 hM (by intro e he; exact False.elim he) r.certificate

end Silmaril.Logic.Egg.Core.Flat

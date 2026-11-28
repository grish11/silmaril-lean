module

public import Silmaril.Calculi.PERConstraints.Interval.Institution.Defs
public import Silmaril.Logic.Institution.Generalized.Thms

@[expose] public section

namespace Silmaril.Calculi.PERConstraints

open CategoryTheory Silmaril.Logic.Institution Silmaril.Formats

variable {α β : Type}

theorem intervalEvidence_positive_iff (bounds : Bounds α) (admissible : PER α → Prop)
    (sentence : CNF α) :
    (intervalEvidence bounds admissible sentence).positive ↔
      bounds.Certain admissible (fun model => sentence.Holds model) := Iff.rfl

theorem intervalEvidence_negative_iff (bounds : Bounds α) (admissible : PER α → Prop)
    (sentence : CNF α) :
    (intervalEvidence bounds admissible sentence).negative ↔
      bounds.Refuted admissible (fun model => sentence.Holds model) := Iff.rfl

theorem intervalEvidence_negative_iff_not_possible (bounds : Bounds α)
    (admissible : PER α → Prop) (sentence : CNF α) :
    (intervalEvidence bounds admissible sentence).negative ↔
      ¬ bounds.Possible admissible (fun model => sentence.Holds model) :=
  Bounds.refuted_iff_not_possible

/-- Singleton bounds recover ordinary satisfaction and its negation. -/
theorem intervalLax_eval_exact {S : Syntax} (model : Model S) (sentence : CNF S.Term) :
    intervalLax.eval S (Discrete.mk (Bounds.exact model)) sentence =
      ⟨(room S).Sat (Discrete.mk model) sentence, ¬ (room S).Sat (Discrete.mk model) sentence⟩ := by
  apply Generalized.Evidence.ext
  · exact propext (Bounds.satisfaction_exact model sentence).1
  · exact propext ((Bounds.refuted_exact model).trans true_imp_iff)

/-- Satisfaction commutes on individual PERs, so covering completions give equal evidence. -/
theorem intervalEvidence_rename_of_coverage (bounds : Bounds β) (f : α → β)
    {sourceAdmissible : PER α → Prop} {targetAdmissible : PER β → Prop}
    (maps : Set.MapsTo (fun model => model.pull f) (bounds.completions targetAdmissible)
      ((bounds.pull f).completions sourceAdmissible))
    (covers : Set.SurjOn (fun model => model.pull f) (bounds.completions targetAdmissible)
      ((bounds.pull f).completions sourceAdmissible)) (sentence : CNF α) :
    intervalEvidence bounds targetAdmissible (sentence.map f) =
      intervalEvidence (bounds.pull f) sourceAdmissible sentence :=
  Generalized.Evidence.ofCompletions_eq_of_image_eq (fun model => model.pull f)
    (Bounds.completion_image_eq_of_coverage maps covers) _ _
    (fun model _ => CNF.holds_map model f sentence)

/-- Injective term maps cover the unrestricted interval completion family. -/
theorem intervalLax_eval_map_of_injective {S T : Syntax} (f : S ⟶ T)
    (injective : Function.Injective f.term) (bounds : Bounds T.Term) (sentence : CNF S.Term) :
    intervalLax.eval T (Discrete.mk bounds) (intervalLax.Sen.map f sentence) =
      intervalLax.eval S (Discrete.mk (Bounds.reduct f bounds)) sentence :=
  intervalEvidence_rename_of_coverage bounds f.term
    (bounds.pull_mapsTo f.term (fun _ h => h)) (bounds.pull_surjOn_of_injective injective) sentence

end Silmaril.Calculi.PERConstraints

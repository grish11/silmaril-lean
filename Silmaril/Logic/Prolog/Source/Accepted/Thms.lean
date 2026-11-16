module

public import Silmaril.Logic.Prolog.Source.Accepted.Defs
public import Silmaril.Logic.Prolog.Source.Compilation.Thms

@[expose] public section
namespace Silmaril.Logic.Prolog.Source
open Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples

/-- Every positive source theory is satisfiable; this does not claim that
operational Prolog search terminates or computes its answers. -/
theorem source_sat (V : Vocabulary) (H : Set (AcceptedSentence V)) :
    ∃ M : FOL.Structure V.signature, ∀ s ∈ H, s.Holds M := by
  refine ⟨Definite.totalModel V.signature, ?_⟩
  intro s _
  exact (s.encode_holds _).mp (Definite.totalModel_holds s.resolved.encode)

/-- Exact consequence transport across text acceptance and independent scoped
interpretation, with the original public model category. -/
theorem source_entails_iff (V : Vocabulary) (H : Set (AcceptedSentence V))
    (s : AcceptedSentence V) :
    (sourceRoom V).Entails H s ↔
      (Definite.room V.signature).Entails
        ((fun t : AcceptedSentence V => t.resolved.encode) '' H) s.resolved.encode :=
  by
    constructor
    · intro h M hH
      apply (s.encode_holds M).mpr
      apply h M
      intro t ht
      exact (t.encode_holds M).mp (hH _ ⟨t, ht, rfl⟩)
    · intro h M hH
      apply (s.encode_holds M).mp
      apply h M
      rintro _ ⟨t, ht, rfl⟩
      exact (t.encode_holds M).mpr (hH t ht)

end Silmaril.Logic.Prolog.Source

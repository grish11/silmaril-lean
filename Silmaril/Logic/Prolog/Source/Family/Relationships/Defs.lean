module

public import Silmaril.Logic.Prolog.Source.Family.Thms
public import Silmaril.Logic.Prolog.Horn.Definite
public import Silmaril.Logic.Prolog.Horn.Egglog

@[expose] public section
namespace Silmaril.Logic.Prolog.Source.Families
open Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples

/-- Positive accepted source also targets the actual constructor/relation Core,
without custom tables or an appeal to unrestricted graph formulas. -/
def toEgglogCore : Inst.CoHom inst Egglog.Core.inst :=
  toDefinite.comp Egglog.Core.fromProlog

theorem toEgglogCore_modelExpansive : toEgglogCore.ModelExpansive :=
  fun _ M => ⟨Egglog.Core.Prolog.expansion M, rfl⟩

def egglogCore {V : Vocabulary} (s : Family V) :
    Egglog.Core.Sentence (Egglog.Core.Prolog.signature V.signature) :=
  Egglog.Core.Prolog.sentence s.encode

theorem egglogCore_holds {V : Vocabulary}
    (M : Egglog.Core.Model (Egglog.Core.Prolog.signature V.signature)) (s : Family V) :
    (egglogCore s).Holds M ↔ s.Holds M.toFOL :=
  (Egglog.Core.Prolog.holds M s.encode).trans (s.encode_holds M.toFOL)

theorem entails_iff_egglogCore (V : Vocabulary) (H : Set (Family V)) (s : Family V) :
    (room V).Entails H s ↔
      (Egglog.Core.room (Egglog.Core.Prolog.signature V.signature)).Entails
        (egglogCore '' H) (egglogCore s) :=
  toEgglogCore.entails_iff toEgglogCore_modelExpansive V H s

theorem sat_iff_egglogCore {V : Vocabulary} (H : Set (Family V)) :
    Sat H ↔ ∃ M : Egglog.Core.Model (Egglog.Core.Prolog.signature V.signature),
      ∀ φ ∈ egglogCore '' H, φ.Holds M := by
  constructor
  · rintro ⟨M, h⟩
    refine ⟨Egglog.Core.Prolog.expansion M, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    exact (egglogCore_holds _ s).mpr (h s hs)
  · rintro ⟨M, h⟩
    exact ⟨M.toFOL, fun s hs => (egglogCore_holds M s).mp (h _ ⟨s, hs, rfl⟩)⟩

theorem unsat_iff_egglogCore {V : Vocabulary} (H : Set (Family V)) :
    Unsat H ↔ ¬ ∃ M : Egglog.Core.Model (Egglog.Core.Prolog.signature V.signature),
      ∀ φ ∈ egglogCore '' H, φ.Holds M := not_congr (sat_iff_egglogCore H)

/-- Real composed comparisons with the existing Horn and full egglog graph APIs. -/
def toHorn : Inst.CoHom inst Horn.inst := toDefinite.comp Horn.fromDefinite

def toEgglogGraph : Inst.CoHom inst Egglog.Core.Graph.inst :=
  toHorn.comp Horn.toEgglogGraph

theorem toHorn_modelExpansive : toHorn.ModelExpansive := fun _ M => ⟨M, rfl⟩

theorem toEgglogGraph_modelExpansive : toEgglogGraph.ModelExpansive :=
  fun _ M => ⟨Egglog.Core.Prolog.expansion M, rfl⟩

def horn {V : Vocabulary} (s : Family V) : Horn.Sentence V.signature :=
  Horn.Inclusion.sentence s.encode

def egglogGraph {V : Vocabulary} (s : Family V) :
    FOL.Sentence (Horn.GraphTranslation.signature V.signature |> Egglog.Core.Graph.signature) :=
  Horn.GraphTranslation.sentence (horn s)

theorem horn_holds {V : Vocabulary} (M : FOL.Structure V.signature) (s : Family V) :
    (horn s).Holds M ↔ s.Holds M :=
  (Horn.Inclusion.holds M s.encode).trans (s.encode_holds M)

theorem egglogGraph_holds {V : Vocabulary}
    (M : Egglog.Core.Model (Horn.GraphTranslation.signature V.signature)) (s : Family V) :
    (egglogGraph s).Holds (Egglog.Core.Graph.model M) ↔ s.Holds M.toFOL :=
  (Horn.GraphTranslation.holds M (horn s)).trans (horn_holds M.toFOL s)

theorem entails_iff_horn (V : Vocabulary) (H : Set (Family V)) (s : Family V) :
    (room V).Entails H s ↔ (Horn.room V.signature).Entails (horn '' H) (horn s) :=
  toHorn.entails_iff toHorn_modelExpansive V H s

theorem entails_iff_egglogGraph (V : Vocabulary) (H : Set (Family V)) (s : Family V) :
    (room V).Entails H s ↔
      (Egglog.Core.Graph.room (Horn.GraphTranslation.signature V.signature)).Entails
        (egglogGraph '' H) (egglogGraph s) :=
  toEgglogGraph.entails_iff toEgglogGraph_modelExpansive V H s

theorem sat_iff_egglogGraph {V : Vocabulary} (H : Set (Family V)) :
    Sat H ↔ ∃ M : Egglog.Core.Model (Horn.GraphTranslation.signature V.signature),
      ∀ φ ∈ egglogGraph '' H, φ.Holds (Egglog.Core.Graph.model M) := by
  constructor
  · rintro ⟨M, h⟩
    refine ⟨Egglog.Core.Prolog.expansion M, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    exact (egglogGraph_holds _ s).mpr (h s hs)
  · rintro ⟨M, h⟩
    exact ⟨M.toFOL, fun s hs => (egglogGraph_holds M s).mp (h _ ⟨s, hs, rfl⟩)⟩

theorem unsat_iff_egglogGraph {V : Vocabulary} (H : Set (Family V)) :
    Unsat H ↔ ¬ ∃ M : Egglog.Core.Model (Horn.GraphTranslation.signature V.signature),
      ∀ φ ∈ egglogGraph '' H, φ.Holds (Egglog.Core.Graph.model M) :=
  not_congr (sat_iff_egglogGraph H)

end Silmaril.Logic.Prolog.Source.Families

module

public import Silmaril.Logic.Egglog.Source.Named.Supplied.Institution.Defs

@[expose] public section
namespace Silmaril.Logic.Egglog.Source.Named.Supplied
open CategoryTheory Silmaril.Logic.Institution

def TheoryHolds {S : SuppliedSignature} (M : Core.Model S.ambient) (H : Set (SuppliedSentence S)) : Prop :=
  ∀ sentence ∈ H, sentence.Holds M

def Sat {S : SuppliedSignature} (H : Set (SuppliedSentence S)) : Prop := ∃ M, TheoryHolds M H

def Unsat {S : SuppliedSignature} (H : Set (SuppliedSentence S)) : Prop := ¬ Sat H

/-- All original receipts share one actual ambient model, for arbitrary sets. -/
theorem theory_holds_iff_core {S : SuppliedSignature} (M : Core.Model S.ambient)
    (H : Set (SuppliedSentence S)) :
    TheoryHolds M H ↔ ∀ sentence ∈ SuppliedSentence.decode '' H, sentence.Holds M := by
  constructor
  · rintro holds _ ⟨sentence, member, rfl⟩
    exact (sentence.decode_holds M).mpr (holds sentence member)
  · intro holds sentence member
    exact (sentence.decode_holds M).mp (holds _ ⟨sentence, member, rfl⟩)

theorem sat_iff_core {S : SuppliedSignature} (H : Set (SuppliedSentence S)) :
    Sat H ↔ ∃ M : Core.Model S.ambient, ∀ sentence ∈ SuppliedSentence.decode '' H, sentence.Holds M :=
  exists_congr (fun M => theory_holds_iff_core M H)

theorem unsat_iff_core {S : SuppliedSignature} (H : Set (SuppliedSentence S)) :
    Unsat H ↔ ¬ ∃ M : Core.Model S.ambient, ∀ sentence ∈ SuppliedSentence.decode '' H, sentence.Holds M :=
  not_congr (sat_iff_core H)

theorem entails_iff_core (S : SuppliedSignature) (H : Set (SuppliedSentence S))
    (sentence : SuppliedSentence S) :
    (room S).Entails H sentence ↔
      (Core.room S.ambient).Entails (SuppliedSentence.decode '' H) sentence.decode :=
  toCore.entails_iff toCore_modelExpansive S H sentence

def graph {S : SuppliedSignature} (sentence : SuppliedSentence S) :=
  Core.Graph.sentence sentence.decode

theorem graph_holds {S : SuppliedSignature} (M : Core.Model S.ambient) (sentence : SuppliedSentence S) :
    (graph sentence).Holds (Core.Graph.model M) ↔ sentence.Holds M :=
  (Core.Graph.sentence_holds M sentence.decode).trans (sentence.decode_holds M)

theorem theory_holds_iff_graph {S : SuppliedSignature} (M : Core.Model S.ambient)
    (H : Set (SuppliedSentence S)) :
    TheoryHolds M H ↔ ∀ sentence ∈ graph '' H, sentence.Holds (Core.Graph.model M) := by
  constructor
  · rintro holds _ ⟨sentence, member, rfl⟩
    exact (graph_holds M sentence).mpr (holds sentence member)
  · intro holds sentence member
    exact (graph_holds M sentence).mp (holds _ ⟨sentence, member, rfl⟩)

theorem sat_iff_graph {S : SuppliedSignature} (H : Set (SuppliedSentence S)) :
    Sat H ↔ ∃ M : Core.Model S.ambient,
      ∀ sentence ∈ graph '' H, sentence.Holds (Core.Graph.model M) :=
  exists_congr (fun M => theory_holds_iff_graph M H)

theorem unsat_iff_graph {S : SuppliedSignature} (H : Set (SuppliedSentence S)) :
    Unsat H ↔ ¬ ∃ M : Core.Model S.ambient,
      ∀ sentence ∈ graph '' H, sentence.Holds (Core.Graph.model M) :=
  not_congr (sat_iff_graph H)

theorem entails_iff_graph (S : SuppliedSignature) (H : Set (SuppliedSentence S))
    (sentence : SuppliedSentence S) :
    (room S).Entails H sentence ↔
      (Core.Graph.room S.ambient).Entails (graph '' H) (graph sentence) :=
  toGraph.entails_iff toGraph_modelExpansive S H sentence

theorem theory_holds_map {S T : SuppliedSignature} (f : S ⟶ T) (M : Core.Model T.ambient)
    (H : Set (SuppliedSentence S)) :
    TheoryHolds M (SuppliedSentence.map f '' H) ↔
      TheoryHolds ((Core.Model.reduct f.ambient).obj M) H := by
  constructor
  · intro holds sentence member
    exact (SuppliedSentence.holds_map f M sentence).mp (holds _ ⟨sentence, member, rfl⟩)
  · rintro holds _ ⟨sentence, member, rfl⟩
    exact (SuppliedSentence.holds_map f M sentence).mpr (holds sentence member)

/-- Positive normalized Core has a singleton model of every arbitrary theory.
Exact UNSAT comparisons do not manufacture inconsistent positive source examples. -/
theorem sat_every_theory {S : SuppliedSignature} (H : Set (SuppliedSentence S)) : Sat H :=
  (sat_iff_core H).mpr (Core.Positive.sat_every_theory _)


end Silmaril.Logic.Egglog.Source.Named.Supplied

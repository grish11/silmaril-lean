module

public import Silmaril.Logic.Egglog.Source.Named.Supplied.Direct.Defs

@[expose] public section
namespace Silmaril.Logic.Egglog.Source.Named.Supplied.Direct
open CategoryTheory Silmaril.Logic.Institution

def TheoryHolds {S : SuppliedSignature} (M : Core.Model S.ambient) (H : Set (Sentence S)) : Prop :=
  ∀ sentence ∈ H, Holds M sentence

def Sat {S : SuppliedSignature} (H : Set (Sentence S)) : Prop := ∃ M, TheoryHolds M H

def Unsat {S : SuppliedSignature} (H : Set (Sentence S)) : Prop := ¬ Sat H

theorem theory_holds_iff_core {S : SuppliedSignature} (M : Core.Model S.ambient)
    (H : Set (Sentence S)) :
    TheoryHolds M H ↔ ∀ sentence ∈ decode '' H, sentence.Holds M := by
  constructor
  · rintro holds _ ⟨sentence, member, rfl⟩
    exact (decode_holds M sentence).mpr (holds sentence member)
  · intro holds sentence member
    exact (decode_holds M sentence).mp (holds _ ⟨sentence, member, rfl⟩)

theorem sat_iff_core {S : SuppliedSignature} (H : Set (Sentence S)) :
    Sat H ↔ ∃ M : Core.Model S.ambient, ∀ sentence ∈ decode '' H, sentence.Holds M :=
  exists_congr (fun M => theory_holds_iff_core M H)

theorem unsat_iff_core {S : SuppliedSignature} (H : Set (Sentence S)) :
    Unsat H ↔ ¬ ∃ M : Core.Model S.ambient, ∀ sentence ∈ decode '' H, sentence.Holds M :=
  not_congr (sat_iff_core H)

theorem entails_iff_core (S : SuppliedSignature) (H : Set (Sentence S)) (sentence : Sentence S) :
    (room S).Entails H sentence ↔ (Core.room S.ambient).Entails (decode '' H) (decode sentence) :=
  toCore.entails_iff toCore_modelExpansive S H sentence

def graph {S : SuppliedSignature} (sentence : Sentence S) := Core.Graph.sentence (decode sentence)

theorem graph_holds {S : SuppliedSignature} (M : Core.Model S.ambient) (sentence : Sentence S) :
    (graph sentence).Holds (Core.Graph.model M) ↔ Holds M sentence :=
  (Core.Graph.sentence_holds M (decode sentence)).trans (decode_holds M sentence)

theorem theory_holds_iff_graph {S : SuppliedSignature} (M : Core.Model S.ambient)
    (H : Set (Sentence S)) :
    TheoryHolds M H ↔ ∀ sentence ∈ graph '' H, sentence.Holds (Core.Graph.model M) := by
  constructor
  · rintro holds _ ⟨sentence, member, rfl⟩
    exact (graph_holds M sentence).mpr (holds sentence member)
  · intro holds sentence member
    exact (graph_holds M sentence).mp (holds _ ⟨sentence, member, rfl⟩)

theorem sat_iff_graph {S : SuppliedSignature} (H : Set (Sentence S)) :
    Sat H ↔ ∃ M : Core.Model S.ambient,
      ∀ sentence ∈ graph '' H, sentence.Holds (Core.Graph.model M) :=
  exists_congr (fun M => theory_holds_iff_graph M H)

theorem unsat_iff_graph {S : SuppliedSignature} (H : Set (Sentence S)) :
    Unsat H ↔ ¬ ∃ M : Core.Model S.ambient,
      ∀ sentence ∈ graph '' H, sentence.Holds (Core.Graph.model M) := not_congr (sat_iff_graph H)

theorem entails_iff_graph (S : SuppliedSignature) (H : Set (Sentence S)) (sentence : Sentence S) :
    (room S).Entails H sentence ↔ (Core.Graph.room S.ambient).Entails (graph '' H) (graph sentence) :=
  toGraph.entails_iff toGraph_modelExpansive S H sentence

theorem theory_holds_map {S T : SuppliedSignature} (f : S ⟶ T) (M : Core.Model T.ambient)
    (H : Set (Sentence S)) :
    TheoryHolds M (map f '' H) ↔ TheoryHolds ((Core.Model.reduct f.ambient).obj M) H := by
  constructor
  · intro holds sentence member
    exact (holds_map f M sentence).mp (holds _ ⟨sentence, member, rfl⟩)
  · rintro holds _ ⟨sentence, member, rfl⟩
    exact (holds_map f M sentence).mpr (holds sentence member)

theorem sat_every_theory {S : SuppliedSignature} (H : Set (Sentence S)) : Sat H :=
  (sat_iff_core H).mpr (Core.Positive.sat_every_theory _)

end Silmaril.Logic.Egglog.Source.Named.Supplied.Direct

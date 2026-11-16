module

public import Silmaril.Logic.Egglog.Source.Named.Family.Defs
public import Silmaril.Logic.Egglog.Core.Graph.Thms
public import Silmaril.Logic.Egglog.Core.Positive.Thms

@[expose] public section
namespace Silmaril.Logic.Egglog.Source.Named.Families
open CategoryTheory Silmaril.Logic.Institution

theorem toCore_modelExpansive : toCore.ModelExpansive := fun _ M => ⟨M, rfl⟩

def toGraph : Inst.CoHom inst Core.Graph.inst := toCore.comp Core.Graph.fromCore

theorem toGraph_modelExpansive : toGraph.ModelExpansive :=
  fun _ M => ⟨M, rfl⟩

def TheoryHolds {S : Core.Signature} (M : Core.Model S) (H : Set (FamilySentence S)) : Prop :=
  ∀ sentence ∈ H, sentence.Holds M

def Sat {S : Core.Signature} (H : Set (FamilySentence S)) : Prop := ∃ M, TheoryHolds M H

def Unsat {S : Core.Signature} (H : Set (FamilySentence S)) : Prop := ¬ Sat H

/-- All local declaration units share one ambient model, for arbitrary sets. -/
theorem theory_holds_iff_core {S : Core.Signature} (M : Core.Model S)
    (H : Set (FamilySentence S)) :
    TheoryHolds M H ↔ ∀ sentence ∈ FamilySentence.decode '' H, sentence.Holds M := by
  constructor
  · rintro holds _ ⟨sentence, member, rfl⟩
    exact (sentence.decode_holds M).mpr (holds sentence member)
  · intro holds sentence member
    exact (sentence.decode_holds M).mp (holds _ ⟨sentence, member, rfl⟩)

theorem sat_iff_core {S : Core.Signature} (H : Set (FamilySentence S)) :
    Sat H ↔ ∃ M : Core.Model S, ∀ sentence ∈ FamilySentence.decode '' H, sentence.Holds M :=
  exists_congr (fun M => theory_holds_iff_core M H)

theorem unsat_iff_core {S : Core.Signature} (H : Set (FamilySentence S)) :
    Unsat H ↔ ¬ ∃ M : Core.Model S, ∀ sentence ∈ FamilySentence.decode '' H, sentence.Holds M :=
  not_congr (sat_iff_core H)

theorem entails_iff_core (S : Core.Signature) (H : Set (FamilySentence S))
    (sentence : FamilySentence S) :
    (room S).Entails H sentence ↔
      (Core.room S).Entails (FamilySentence.decode '' H) sentence.decode :=
  toCore.entails_iff toCore_modelExpansive S H sentence

def graph {S : Core.Signature} (sentence : FamilySentence S) :=
  Core.Graph.sentence sentence.decode

theorem graph_holds {S : Core.Signature} (M : Core.Model S) (sentence : FamilySentence S) :
    (graph sentence).Holds (Core.Graph.model M) ↔ sentence.Holds M :=
  (Core.Graph.sentence_holds M sentence.decode).trans (sentence.decode_holds M)

theorem theory_holds_iff_graph {S : Core.Signature} (M : Core.Model S)
    (H : Set (FamilySentence S)) :
    TheoryHolds M H ↔ ∀ sentence ∈ graph '' H, sentence.Holds (Core.Graph.model M) := by
  constructor
  · rintro holds _ ⟨sentence, member, rfl⟩
    exact (graph_holds M sentence).mpr (holds sentence member)
  · intro holds sentence member
    exact (graph_holds M sentence).mp (holds _ ⟨sentence, member, rfl⟩)

theorem sat_iff_graph {S : Core.Signature} (H : Set (FamilySentence S)) :
    Sat H ↔ ∃ M : Core.Model S,
      ∀ sentence ∈ graph '' H, sentence.Holds (Core.Graph.model M) :=
  exists_congr (fun M => theory_holds_iff_graph M H)

theorem unsat_iff_graph {S : Core.Signature} (H : Set (FamilySentence S)) :
    Unsat H ↔ ¬ ∃ M : Core.Model S,
      ∀ sentence ∈ graph '' H, sentence.Holds (Core.Graph.model M) :=
  not_congr (sat_iff_graph H)

theorem entails_iff_graph (S : Core.Signature) (H : Set (FamilySentence S))
    (sentence : FamilySentence S) :
    (room S).Entails H sentence ↔
      (Core.Graph.room S).Entails (graph '' H) (graph sentence) :=
  toGraph.entails_iff toGraph_modelExpansive S H sentence

theorem theory_holds_map {S T : Core.Signature} (f : S ⟶ T) (M : Core.Model T)
    (H : Set (FamilySentence S)) :
    TheoryHolds M (FamilySentence.map f '' H) ↔
      TheoryHolds ((Core.Model.reduct f).obj M) H := by
  constructor
  · intro holds sentence member
    exact (FamilySentence.holds_map f M sentence).mp (holds _ ⟨sentence, member, rfl⟩)
  · rintro holds _ ⟨sentence, member, rfl⟩
    exact (FamilySentence.holds_map f M sentence).mpr (holds sentence member)

/-- Positive normalized Core has a singleton model of every arbitrary theory.
Exact UNSAT comparisons do not manufacture inconsistent positive source examples. -/
theorem sat_every_theory {S : Core.Signature} (H : Set (FamilySentence S)) : Sat H :=
  (sat_iff_core H).mpr (Core.Positive.sat_every_theory _)

end Silmaril.Logic.Egglog.Source.Named.Families

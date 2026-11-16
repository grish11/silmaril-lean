module

public import Silmaril.Logic.Prolog.Horn.Thms
public import Silmaril.Logic.Egglog.Core.Graph.Defs
public import Silmaril.Logic.Egglog.Core.Prolog

@[expose] public section

namespace Silmaril.Logic.Prolog.Horn

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace GraphTranslation

abbrev signature := Egglog.Core.Prolog.signature

def embedding (S : Signature) : S ⟶ Egglog.Core.Graph.signature (signature S) where
  sorts := id
  ops := id
  rels := fun p => .predicate p

def sentence {S : Signature} (s : Sentence S) :
    FOL.Sentence (Egglog.Core.Graph.signature (signature S)) :=
  s.encode.map (embedding S)

theorem holds {S : Signature} (M : Egglog.Core.Model (signature S)) (s : Sentence S) :
    (sentence s).Holds (Egglog.Core.Graph.model M) ↔ s.Holds M.toFOL := by
  rw [sentence, FOL.Sentence.holds_map]
  exact s.encode_holds M.toFOL

theorem embedding_natural {S T : Signature} (f : S ⟶ T) :
    f ≫ embedding T = embedding S ≫
      Egglog.Core.Graph.signatureMap (Egglog.Core.Prolog.signatures.map f) := rfl

theorem sentence_map {S T : Signature} (f : S ⟶ T) (s : Sentence S) :
    sentence (s.map f) = (sentence s).map
      (Egglog.Core.Graph.signatureMap (Egglog.Core.Prolog.signatures.map f)) := by
  rw [sentence, Sentence.encode_map, ← FOL.Sentence.map_comp,
    embedding_natural, FOL.Sentence.map_comp]
  rfl

end GraphTranslation

/-- Constraints target full graph formulas. The positive normalized Core fragment
cannot express arbitrary false heads with unrestricted model expansion. -/
def toEgglogGraph : Inst.CoHom inst Egglog.Core.Graph.inst where
  Φ := Egglog.Core.Prolog.signatures
  ρ :=
    { app := fun S => ⟨GraphTranslation.sentence,
        Egglog.Core.Prolog.models S, GraphTranslation.holds⟩
      naturality := by
        intro S T f
        exact Room.hom_ext (funext (GraphTranslation.sentence_map f)) rfl }

theorem toEgglogGraph_modelExpansive : toEgglogGraph.ModelExpansive :=
  fun _ M => ⟨Egglog.Core.Prolog.expansion M, rfl⟩

/-- Exact theory truth under the actual all-homomorphism model decoder. -/
theorem theory_holds_iff_egglogGraph {S : Signature}
    (M : Egglog.Core.Model (GraphTranslation.signature S)) (H : Set (Sentence S)) :
    TheoryHolds M.toFOL H ↔
      ∀ φ ∈ GraphTranslation.sentence '' H, φ.Holds (Egglog.Core.Graph.model M) := by
  constructor
  · rintro h φ ⟨s, hs, rfl⟩
    exact (GraphTranslation.holds M s).mpr (h s hs)
  · intro h s hs
    exact (GraphTranslation.holds M s).mp (h _ ⟨s, hs, rfl⟩)

theorem sat_iff_egglogGraph {S : Signature} (H : Set (Sentence S)) :
    Sat H ↔ ∃ M : Egglog.Core.Model (GraphTranslation.signature S),
      ∀ φ ∈ GraphTranslation.sentence '' H, φ.Holds (Egglog.Core.Graph.model M) := by
  constructor
  · rintro ⟨M, h⟩
    exact ⟨Egglog.Core.Prolog.expansion M,
      (theory_holds_iff_egglogGraph (Egglog.Core.Prolog.expansion M) H).mp h⟩
  · rintro ⟨M, h⟩
    exact ⟨M.toFOL, (theory_holds_iff_egglogGraph M H).mpr h⟩

theorem unsat_iff_egglogGraph {S : Signature} (H : Set (Sentence S)) :
    Unsat H ↔ ¬ ∃ M : Egglog.Core.Model (GraphTranslation.signature S),
      ∀ φ ∈ GraphTranslation.sentence '' H, φ.Holds (Egglog.Core.Graph.model M) :=
  not_congr (sat_iff_egglogGraph H)

theorem entails_iff_egglogGraph (S : Signature) (H : Set (Sentence S)) (s : Sentence S) :
    (room S).Entails H s ↔
      (Egglog.Core.Graph.room (GraphTranslation.signature S)).Entails
        (GraphTranslation.sentence '' H) (GraphTranslation.sentence s) :=
  toEgglogGraph.entails_iff toEgglogGraph_modelExpansive S H s

end Silmaril.Logic.Prolog.Horn

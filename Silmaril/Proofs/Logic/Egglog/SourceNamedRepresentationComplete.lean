module

public import Silmaril.Logic.Egglog.Source.Named.Representation.Local.Thms
public import Silmaril.Logic.Egglog.Source.Named.Family.Thms
public import Silmaril.Logic.Egglog.Source.Named.Representation.Support.Thms
public import Silmaril.Logic.Egglog.Source.Named.Representation.Naming.Thms

@[expose] public section
namespace Silmaril.Logic.Egglog.Source.Named
open CategoryTheory

/-- Internal assembly lemma: a retraction of the concrete finite coding maps
composes the exact local actual-byte theorem with the actual ambient inclusion.
The concrete retraction is proved by `FiniteSupport.Footprint.encode_decode`;
no global naming assumption is supplied. -/
theorem representation_of_finiteCoding {S : Core.Signature}
    (support : FiniteSupport.Footprint S) (closed : support.Closed)
    (retract : support.encode closed ≫ support.decode closed = 𝟙 support.signature)
    (sentence : Core.Sentence support.signature) :
    ∃ (unit : AcceptedUnit) (symbols : unit.declarations.signature ⟶ S),
      unit.resolved.map symbols = sentence.map support.inclusion := by
  obtain ⟨unit, symbols, compiled⟩ :=
    localMappedRepresentation (support.declarations closed) (sentence.map (support.encode closed))
  refine ⟨unit, symbols ≫ support.decode closed ≫ support.inclusion, ?_⟩
  calc
    unit.resolved.map (symbols ≫ support.decode closed ≫ support.inclusion) =
        ((unit.resolved.map symbols).map (support.decode closed)).map support.inclusion := by
      simp only [Core.Sentence.map_comp]
    _ = ((sentence.map (support.encode closed)).map (support.decode closed)).map
        support.inclusion := by rw [compiled]
    _ = (sentence.map (support.encode closed ≫ support.decode closed)).map support.inclusion := by
      rw [Core.Sentence.map_comp]
    _ = sentence.map support.inclusion := by rw [retract, Core.Sentence.map_id]

/-- Every sentence of every arbitrary ambient Core signature has finite
checked named support and actual complete accepted bytes whose mapped compilation
is exactly the original sentence. No global naming view is supplied. -/
theorem finiteSupportRepresentation_task : Task.finiteSupportRepresentation := by
  intro S sentence
  let support := FiniteSupport.sentence sentence
  let closed := FiniteSupport.sentence_closed sentence
  let localSentence := FiniteSupport.liftSentence support sentence
    (FiniteSupport.sentence_supports sentence)
  obtain ⟨unit, symbols, compiled⟩ := representation_of_finiteCoding support closed
    (support.encode_decode closed) localSentence
  exact ⟨unit, symbols, compiled.trans
    (FiniteSupport.liftSentence_map support sentence (FiniteSupport.sentence_supports sentence))⟩

/-- The declaration-file branch of the actual family institution covers every
ambient Core sentence, with no supplied global naming view. -/
theorem FamilySentence.decode_surjective (S : Core.Signature) :
    Function.Surjective (@FamilySentence.decode S) := by
  intro sentence
  obtain ⟨unit, symbols, compiled⟩ := finiteSupportRepresentation_task S sentence
  exact ⟨⟨.declared unit, symbols⟩, compiled⟩

end Silmaril.Logic.Egglog.Source.Named

module

public import Silmaril.Logic.Egglog.Source.Named.Supplied.Institution.Defs

@[expose] public section
namespace Silmaril.Logic.Egglog.Source.Named.Supplied.Direct
open CategoryTheory Silmaril.Logic.Institution

abbrev Sentence (S : SuppliedSignature) := AcceptedSentence S.names.declarations

def family (S : SuppliedSignature) (sentence : Sentence S) : FamilySentence S.ambient :=
  ⟨.supplied _ sentence, S.names.symbols⟩

def Holds {S : SuppliedSignature} (M : Core.Model S.ambient) (sentence : Sentence S) : Prop :=
  (family S sentence).Holds M

def decode {S : SuppliedSignature} (sentence : Sentence S) : Core.Sentence S.ambient :=
  sentence.resolved.map S.names.symbols

def map {S T : SuppliedSignature} (f : S ⟶ T) (sentence : Sentence S) : Sentence T :=
  sentence.map f.vocabulary

theorem map_id (S : SuppliedSignature) (sentence : Sentence S) : map (𝟙 S) sentence = sentence :=
  AcceptedSentence.map_id sentence

theorem map_comp {S T U : SuppliedSignature} (f : S ⟶ T) (g : T ⟶ U) (sentence : Sentence S) :
    map (f ≫ g) sentence = map g (map f sentence) :=
  AcceptedSentence.map_comp f.vocabulary g.vocabulary sentence

theorem decode_holds {S : SuppliedSignature} (M : Core.Model S.ambient) (sentence : Sentence S) :
    (decode sentence).Holds M ↔ Holds M sentence := (family S sentence).decode_holds M

theorem decode_map {S T : SuppliedSignature} (f : S ⟶ T) (sentence : Sentence S) :
    decode (map f sentence) = (decode sentence).map f.ambient := by
  change (sentence.resolved.map f.vocabulary.symbols).map T.names.symbols = _
  rw [← Core.Sentence.map_comp, f.commutes, Core.Sentence.map_comp]
  rfl

theorem holds_map {S T : SuppliedSignature} (f : S ⟶ T) (M : Core.Model T.ambient)
    (sentence : Sentence S) : Holds M (map f sentence) ↔
      Holds ((Core.Model.reduct f.ambient).obj M) sentence := by
  rw [← decode_holds, decode_map, Core.Sentence.holds_map, decode_holds]

/-- Direct accepted bodies, with every ordinary ambient model and model hom. -/
def room (S : SuppliedSignature) : Room.{0,0,1} :=
  ⟨Sentence S, Cat.of (Core.Model S.ambient), fun M sentence => Holds M sentence⟩

def corridor {S T : SuppliedSignature} (f : S ⟶ T) : room S ⟶ room T :=
  ⟨map f, Core.Model.reduct f.ambient, holds_map f⟩

def institution : SuppliedSignature ⥤ Room.{0,0,1} where
  obj := room
  map := corridor
  map_id S := Room.hom_ext (funext (map_id S)) rfl
  map_comp f g := Room.hom_ext (funext (map_comp f g)) rfl

def inst : Inst.{1,0,0,0,1} := ⟨SuppliedSignature, institution⟩

def toCore : Inst.CoHom inst Core.inst where
  Φ := Supplied.ambient
  ρ :=
    { app _ := ⟨decode, 𝟭 _, decode_holds⟩
      naturality := by
        intro S T f
        exact Room.hom_ext (funext (decode_map f)) rfl }

theorem toCore_modelExpansive : toCore.ModelExpansive := fun _ M => ⟨M, rfl⟩

def toGraph : Inst.CoHom inst Core.Graph.inst := toCore.comp Core.Graph.fromCore

theorem toGraph_modelExpansive : toGraph.ModelExpansive := fun _ M => ⟨M, rfl⟩

/-- The exact original-body embedding into families is available per room. The
strict institution comparison is through Core because direct transport changes
which supplied declarations accompany the unchanged original body receipt. -/
def familyCorridor (S : SuppliedSignature) : room S ⟶ Families.room S.ambient :=
  ⟨family S, 𝟭 _, fun _ _ => Iff.rfl⟩

/-- Identity adoption retains the exact original direct body receipt. -/
def adopt (S : SuppliedSignature) (sentence : Sentence S) : SuppliedSentence S :=
  SuppliedSentence.ofAccepted S sentence

/-- Materializing support uses the original bytes and the actual proved target
resolver equation, rather than writing a replacement canonical body. -/
def materialize {S : SuppliedSignature} (sentence : SuppliedSentence S) : Sentence S :=
  sentence.receipt.body.map sentence.support

theorem materialize_bytes {S : SuppliedSignature} (sentence : SuppliedSentence S) :
    (materialize sentence).bytes = sentence.receipt.bytes := rfl

theorem materialize_raw {S : SuppliedSignature} (sentence : SuppliedSentence S) :
    (materialize sentence).raw = sentence.receipt.raw := rfl

theorem materialize_adopt (S : SuppliedSignature) (sentence : Sentence S) :
    materialize (adopt S sentence) = sentence := AcceptedSentence.map_id sentence

theorem materialize_decode {S : SuppliedSignature} (sentence : SuppliedSentence S) :
    decode (materialize sentence) = sentence.decode :=
  (Core.Sentence.map_comp sentence.support.symbols S.names.symbols sentence.receipt.resolved).symm

theorem materialize_holds {S : SuppliedSignature} (M : Core.Model S.ambient)
    (sentence : SuppliedSentence S) : Holds M (materialize sentence) ↔ sentence.Holds M := by
  rw [← decode_holds, materialize_decode, sentence.decode_holds]

theorem materialize_map {S T : SuppliedSignature} (f : S ⟶ T) (sentence : SuppliedSentence S) :
    materialize (sentence.map f) = map f (materialize sentence) :=
  AcceptedSentence.map_comp sentence.support f.vocabulary sentence.receipt.body

end Silmaril.Logic.Egglog.Source.Named.Supplied.Direct

namespace Silmaril.Logic.Egglog.Source.Named.Supplied
open CategoryTheory Silmaril.Logic.Institution

/-- Natural materialization into the direct accepted-body institution preserves
original bytes and uses every actual ambient model and model hom unchanged. -/
def toDirect : Inst.CoHom inst Direct.inst where
  Φ := 𝟭 _
  ρ :=
    { app _ := ⟨Direct.materialize, 𝟭 _, Direct.materialize_holds⟩
      naturality := by
        intro S T f
        exact Room.hom_ext (funext (Direct.materialize_map f)) rfl }

theorem toDirect_modelExpansive : toDirect.ModelExpansive := fun _ M => ⟨M, rfl⟩
end Silmaril.Logic.Egglog.Source.Named.Supplied

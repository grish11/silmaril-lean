module

public import Silmaril.Logic.Egglog.Source.Named.Supplied.Thms

@[expose] public section
namespace Silmaril.Logic.Egglog.Source.Named
open CategoryTheory Silmaril.Logic.Institution

/-- An original body receipt, independent of later supplied vocabulary extension. -/
structure SuppliedReceipt where
  declarations : Declarations
  body : AcceptedSentence declarations

namespace SuppliedReceipt

def bytes (receipt : SuppliedReceipt) : List UInt8 := receipt.body.bytes
def raw (receipt : SuppliedReceipt) : RawSentence := receipt.body.raw
def resolved (receipt : SuppliedReceipt) : Core.Sentence receipt.declarations.signature :=
  receipt.body.resolved
theorem resolve_eq (receipt : SuppliedReceipt) :
    resolveSentence? receipt.declarations receipt.raw = some receipt.resolved := receipt.body.resolve_eq
def localReceipt (receipt : SuppliedReceipt) : LocalReceipt := .supplied receipt.declarations receipt.body
end SuppliedReceipt

/-- Exact original supplied-body receipts with actual spelling-preserving support
in a supplied vocabulary. Direct admission uses identity support. -/
structure SuppliedSentence (S : SuppliedSignature) where
  receipt : SuppliedReceipt
  support : receipt.declarations ⟶ S.names.declarations

namespace SuppliedSentence
variable {S T U : SuppliedSignature}

def ofAccepted (S : SuppliedSignature) (sentence : AcceptedSentence S.names.declarations) :
    SuppliedSentence S := ⟨⟨_, sentence⟩, 𝟙 _⟩

def family (sentence : SuppliedSentence S) : FamilySentence S.ambient :=
  ⟨sentence.receipt.localReceipt, sentence.support.symbols ≫ S.names.symbols⟩

def Holds (M : Core.Model S.ambient) (sentence : SuppliedSentence S) : Prop :=
  sentence.family.Holds M

def decode (sentence : SuppliedSentence S) : Core.Sentence S.ambient := sentence.family.decode

def map (f : S ⟶ T) (sentence : SuppliedSentence S) : SuppliedSentence T :=
  ⟨sentence.receipt, sentence.support ≫ f.vocabulary⟩

@[simp] theorem map_receipt (f : S ⟶ T) (sentence : SuppliedSentence S) :
    (sentence.map f).receipt = sentence.receipt := rfl

@[simp] theorem map_bytes (f : S ⟶ T) (sentence : SuppliedSentence S) :
    (sentence.map f).receipt.bytes = sentence.receipt.bytes := rfl

@[simp] theorem map_id (sentence : SuppliedSentence S) : sentence.map (𝟙 S) = sentence := by
  cases sentence with
  | mk receipt support =>
      change SuppliedSentence.mk receipt (support ≫ 𝟙 _) = _
      rw [Category.comp_id]

@[simp] theorem map_comp (f : S ⟶ T) (g : T ⟶ U) (sentence : SuppliedSentence S) :
    sentence.map (f ≫ g) = (sentence.map f).map g := by
  change SuppliedSentence.mk sentence.receipt (sentence.support ≫ (f.vocabulary ≫ g.vocabulary)) =
    SuppliedSentence.mk sentence.receipt ((sentence.support ≫ f.vocabulary) ≫ g.vocabulary)
  exact congrArg (SuppliedSentence.mk sentence.receipt)
    (Category.assoc sentence.support f.vocabulary g.vocabulary).symm

/-- The family corridor keeps the exact receipt, including original source bytes. -/
theorem family_map (f : S ⟶ T) (sentence : SuppliedSentence S) :
    (sentence.map f).family = sentence.family.map f.ambient := by
  have symbols : (sentence.support.symbols ≫ f.vocabulary.symbols) ≫ T.names.symbols =
      (sentence.support.symbols ≫ S.names.symbols) ≫ f.ambient := by
    rw [Category.assoc, f.commutes, ← Category.assoc]
  exact congrArg (fun symbols : sentence.receipt.declarations.signature ⟶ T.ambient =>
    FamilySentence.mk sentence.receipt.localReceipt symbols) symbols

theorem decode_map (f : S ⟶ T) (sentence : SuppliedSentence S) :
    (sentence.map f).decode = sentence.decode.map f.ambient := by
  exact (congrArg FamilySentence.decode (family_map f sentence)).trans
    (FamilySentence.decode_map f.ambient sentence.family)

theorem decode_holds (M : Core.Model S.ambient) (sentence : SuppliedSentence S) :
    sentence.decode.Holds M ↔ sentence.Holds M := sentence.family.decode_holds M

theorem holds_map (f : S ⟶ T) (M : Core.Model T.ambient) (sentence : SuppliedSentence S) :
    (sentence.map f).Holds M ↔ sentence.Holds ((Core.Model.reduct f.ambient).obj M) := by
  change (sentence.map f).family.Holds M ↔ sentence.family.Holds _
  rw [family_map]
  exact FamilySentence.holds_map f.ambient M sentence.family

/-- The unchanged original raw sentence also resolves in the supplied vocabulary;
its target compilation follows from proved resolver naturality. -/
theorem resolves (sentence : SuppliedSentence S) :
    resolveSentence? S.names.declarations sentence.receipt.raw =
      some (sentence.receipt.resolved.map sentence.support.symbols) :=
  sentence.support.resolveSentence_map _ _ sentence.receipt.resolve_eq
end SuppliedSentence

namespace Supplied

def ambient : SuppliedSignature ⥤ Core.Signature where
  obj S := S.ambient
  map f := f.ambient

def room (S : SuppliedSignature) : Room.{0,0,1} :=
  ⟨SuppliedSentence S, Cat.of (Core.Model S.ambient), fun M sentence => sentence.Holds M⟩

def corridor {S T : SuppliedSignature} (f : S ⟶ T) : room S ⟶ room T :=
  ⟨SuppliedSentence.map f, Core.Model.reduct f.ambient, SuppliedSentence.holds_map f⟩

def institution : SuppliedSignature ⥤ Room.{0,0,1} where
  obj := room
  map := corridor
  map_id _ := Room.hom_ext (funext SuppliedSentence.map_id) rfl
  map_comp f g := Room.hom_ext (funext (SuppliedSentence.map_comp f g)) rfl

def inst : Inst.{1,0,0,0,1} := ⟨SuppliedSignature, institution⟩

/-- Exact receipt-preserving comparison into the dynamic family institution. -/
def toFamilies : Inst.CoHom inst Families.inst where
  Φ := ambient
  ρ :=
    { app _ := ⟨SuppliedSentence.family, 𝟭 _, fun _ _ => Iff.rfl⟩
      naturality := by
        intro S T f
        exact Room.hom_ext (funext (SuppliedSentence.family_map f)) rfl }

def toCore : Inst.CoHom inst Core.inst := toFamilies.comp Families.toCore

theorem toCore_modelExpansive : toCore.ModelExpansive := fun _ M => ⟨M, rfl⟩

def toGraph : Inst.CoHom inst Core.Graph.inst := toCore.comp Core.Graph.fromCore

theorem toGraph_modelExpansive : toGraph.ModelExpansive := fun _ M => ⟨M, rfl⟩
end Supplied
end Silmaril.Logic.Egglog.Source.Named

module

public import Silmaril.Logic.Egglog.Source.Named.Accepted.Thms

@[expose] public section
namespace Silmaril.Logic.Egglog.Source.Named
open CategoryTheory Silmaril.Logic.Institution

/-- The original receipt is either a complete declared file or a body checked
against supplied declarations. Neither mode synthesizes replacement bytes. -/
inductive LocalReceipt where
  | declared (unit : AcceptedUnit)
  | supplied (declarations : Declarations) (sentence : AcceptedSentence declarations)

namespace LocalReceipt

def declarations : LocalReceipt → Declarations
  | .declared unit => unit.declarations
  | .supplied D _ => D

def bytes : LocalReceipt → List UInt8
  | .declared unit => unit.bytes
  | .supplied _ sentence => sentence.bytes

def raw : LocalReceipt → RawSentence
  | .declared unit => unit.raw
  | .supplied _ sentence => sentence.raw

def resolved (receipt : LocalReceipt) : Core.Sentence receipt.declarations.signature :=
  match receipt with
  | .declared unit => unit.resolved
  | .supplied _ sentence => sentence.resolved

theorem resolve_eq (receipt : LocalReceipt) :
    resolveSentence? receipt.declarations receipt.raw = some receipt.resolved := by
  cases receipt with
  | declared unit => exact unit.resolve_eq
  | supplied D sentence => exact sentence.resolve_eq
end LocalReceipt

/-- Each sentence keeps its exact original checked receipt and an actual
interpretation in one shared arbitrary ambient signature. -/
structure FamilySentence (S : Core.Signature) where
  receipt : LocalReceipt
  symbols : receipt.declarations.signature ⟶ S

namespace FamilySentence
variable {S T U : Core.Signature}

def Holds (M : Core.Model S) (sentence : FamilySentence S) : Prop :=
  sentence.receipt.raw.Holds ((Core.Model.reduct sentence.symbols).obj M)

def map (f : S ⟶ T) (sentence : FamilySentence S) : FamilySentence T :=
  ⟨sentence.receipt, sentence.symbols ≫ f⟩

@[simp] theorem map_id (sentence : FamilySentence S) : sentence.map (𝟙 S) = sentence := by
  cases sentence
  rfl

@[simp] theorem map_comp (f : S ⟶ T) (g : T ⟶ U) (sentence : FamilySentence S) :
    sentence.map (f ≫ g) = (sentence.map f).map g := rfl

theorem holds_map (f : S ⟶ T) (M : Core.Model T) (sentence : FamilySentence S) :
    (sentence.map f).Holds M ↔ sentence.Holds ((Core.Model.reduct f).obj M) := Iff.rfl

def decode (sentence : FamilySentence S) : Core.Sentence S :=
  sentence.receipt.resolved.map sentence.symbols

/-- Exact comparison with independent named truth; full resolver adequacy is
proved for all existing Core constructors and complete explicit contexts. -/
theorem decode_holds (M : Core.Model S)
    (sentence : FamilySentence S) : sentence.decode.Holds M ↔ sentence.Holds M :=
  (Core.Sentence.holds_map sentence.symbols M sentence.receipt.resolved).trans
    (resolveSentence_holds_iff sentence.receipt.declarations sentence.receipt.raw
      sentence.receipt.resolved sentence.receipt.resolve_eq _).symm

theorem decode_map (f : S ⟶ T) (sentence : FamilySentence S) :
    (sentence.map f).decode = sentence.decode.map f :=
  Core.Sentence.map_comp sentence.symbols f sentence.receipt.resolved
end FamilySentence

namespace Families
/-- All ordinary Core model homomorphisms remain in every room. -/
def room (S : Core.Signature) : Room.{0,0,1} :=
  ⟨FamilySentence S, Cat.of (Core.Model S), fun M sentence => sentence.Holds M⟩

def corridor {S T : Core.Signature} (f : S ⟶ T) : room S ⟶ room T :=
  ⟨FamilySentence.map f, Core.Model.reduct f, FamilySentence.holds_map f⟩

def institution : Core.Signature ⥤ Room.{0,0,1} where
  obj := room
  map := corridor
  map_id _ := Room.hom_ext (funext FamilySentence.map_id) rfl
  map_comp f g := Room.hom_ext (funext (FamilySentence.map_comp f g)) rfl

def inst : Inst.{1,0,0,0,1} := ⟨Core.Signature, institution⟩

/-- Unconditional exact comparison using the proved independent satisfaction theorem. -/
def toCore : Inst.CoHom inst Core.inst where
  Φ := 𝟭 _
  ρ :=
    { app _ := ⟨FamilySentence.decode, 𝟭 _, FamilySentence.decode_holds⟩
      naturality := by
        intro S T f
        exact Room.hom_ext (funext (FamilySentence.decode_map f)) rfl }
end Families
end Silmaril.Logic.Egglog.Source.Named

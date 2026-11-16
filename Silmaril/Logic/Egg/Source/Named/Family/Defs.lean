module

public import Silmaril.Logic.Egg.Source.Named.Accepted.Defs
public import Silmaril.Logic.Institution.SetSentences.Defs

@[expose] public section
namespace Silmaril.Logic.Egg.Source.Named
open CategoryTheory Silmaril.Logic.Institution

inductive LocalReceipt where
  | inferred (program : AcceptedInferredProgram)
  | supplied (declarations : Declarations) (program : AcceptedProgram declarations)

namespace LocalReceipt

def declarations : LocalReceipt → Declarations
  | .inferred p => p.declarations
  | .supplied D _ => D

def program (r : LocalReceipt) : AcceptedProgram r.declarations :=
  match r with
  | .inferred p => p.program
  | .supplied _ p => p
end LocalReceipt

/-- One source sentence is a whole file interpreted in one arbitrary ambient
algebra. Every rule and every file in a theory shares that same algebra. -/
structure FamilySentence (S : Core.Signature) where
  receipt : LocalReceipt
  symbols : receipt.declarations.signature ⟶ S

namespace FamilySentence
variable {S T U : Core.Signature}

def Holds (M : Core.Model S) (p : FamilySentence S) : Prop :=
  p.receipt.program.Holds ((Silmaril.Logic.Institution.Examples.EQ.Algebra.reduct p.symbols).obj M)

def map (f : S ⟶ T) (p : FamilySentence S) : FamilySentence T :=
  ⟨p.receipt, p.symbols ≫ f⟩

@[simp] theorem map_id (p : FamilySentence S) : p.map (𝟙 S) = p := by
  cases p
  rfl

@[simp] theorem map_comp (f : S ⟶ T) (g : T ⟶ U) (p : FamilySentence S) :
    p.map (f ≫ g) = (p.map f).map g := rfl

theorem holds_map (f : S ⟶ T) (M : Core.Model T) (p : FamilySentence S) :
    (p.map f).Holds M ↔ p.Holds
      ((Silmaril.Logic.Institution.Examples.EQ.Algebra.reduct f).obj M) := Iff.rfl

/-- The ordered list is retained in the receipt; conjunction semantics uses its
set of rules. Whole files are not misrepresented by one selected rule. -/
def decode (p : FamilySentence S) : Set (Core.Rule S) :=
  {r | ∃ original ∈ p.receipt.program.resolved, original.map p.symbols = r}

theorem decode_holds (M : Core.Model S) (p : FamilySentence S) :
    (∀ r ∈ p.decode, r.Holds M) ↔ p.Holds M := by
  rw [Holds, AcceptedProgram.resolved_holds]
  constructor
  · intro h r hr
    exact (Core.Rule.holds_map p.symbols M r).mp (h _ ⟨r, hr, rfl⟩)
  · intro h r hr
    obtain ⟨original, member, rfl⟩ := hr
    exact (Core.Rule.holds_map p.symbols M original).mpr (h original member)

theorem decode_map (f : S ⟶ T) (p : FamilySentence S) :
    (p.map f).decode = Core.Rule.map f '' p.decode := by
  ext r
  constructor
  · rintro ⟨original, member, equal⟩
    exact ⟨original.map p.symbols, ⟨original, member, rfl⟩,
      (Core.Rule.map_comp p.symbols f original).symm.trans equal⟩
  · rintro ⟨previous, ⟨original, member, rfl⟩, equal⟩
    exact ⟨original, member, (Core.Rule.map_comp p.symbols f original).trans equal⟩
end FamilySentence

namespace Families

def room (S : Core.Signature) : Room.{0,0,1} :=
  ⟨FamilySentence S, Cat.of (Core.Model S), fun M p => p.Holds M⟩

def corridor {S T : Core.Signature} (f : S ⟶ T) : room S ⟶ room T :=
  ⟨FamilySentence.map f, Silmaril.Logic.Institution.Examples.EQ.Algebra.reduct f,
    FamilySentence.holds_map f⟩

def institution : Core.Signature ⥤ Room.{0,0,1} where
  obj := room
  map := corridor
  map_id _ := Room.hom_ext (funext FamilySentence.map_id) rfl
  map_comp f g := Room.hom_ext (funext (FamilySentence.map_comp f g)) rfl

def inst : Inst.{1,0,0,0,1} := ⟨Core.Signature, institution⟩

/-- Exact source comparison to conjunctions, retaining all actual model arrows. -/
def toCore : Inst.CoHom inst (Silmaril.Logic.Institution.SetSentences.inst Core.inst) where
  Φ := 𝟭 _
  ρ :=
    { app _ := ⟨FamilySentence.decode, 𝟭 _, FamilySentence.decode_holds⟩
      naturality := by
        intro S T f
        exact Room.hom_ext (funext (FamilySentence.decode_map f)) rfl }
theorem toCore_modelExpansive : toCore.ModelExpansive := fun _ M => ⟨M, rfl⟩

end Families
end Silmaril.Logic.Egg.Source.Named

module

public import Silmaril.Logic.Egg.Source.Named.Supplied.Thms

@[expose] public section
namespace Silmaril.Logic.Egg.Source.Named
open CategoryTheory Silmaril.Logic.Institution

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AcceptedProgram

@[ext] theorem ext {D : Declarations} (p q : AcceptedProgram D)
    (bytes : p.bytes = q.bytes) (raw : p.raw = q.raw) (resolved : p.resolved = q.resolved) : p = q := by
  cases p
  cases q
  cases bytes
  cases raw
  cases resolved
  rfl

def map {D E : Declarations} (f : DeclarationHom D E) (p : AcceptedProgram D) :
    AcceptedProgram E where
  bytes := p.bytes
  raw := p.raw
  read_eq := p.read_eq
  resolved := p.resolved.map (Core.Rule.map f.symbols.toHom)
  resolve_eq := DeclarationHom.resolveProgram_map f p.raw p.resolved p.resolve_eq

@[simp] theorem map_bytes {D E : Declarations} (f : DeclarationHom D E)
    (p : AcceptedProgram D) : (p.map f).bytes = p.bytes := rfl

@[simp] theorem map_raw {D E : Declarations} (f : DeclarationHom D E)
    (p : AcceptedProgram D) : (p.map f).raw = p.raw := rfl

theorem map_id {D : Declarations} (p : AcceptedProgram D) :
    p.map (DeclarationHom.identity D) = p := by
  have identity : p.resolved.map (Core.Rule.map (𝟙 D.signature)) = p.resolved := by
    have hm : (Core.Rule.map (𝟙 D.signature) : Core.Rule D.signature → _) = id :=
      funext Core.Rule.map_id
    rw [hm, List.map_id]
  exact ext _ _ rfl rfl identity

theorem map_comp {D E F : Declarations} (f : DeclarationHom D E) (g : DeclarationHom E F)
    (p : AcceptedProgram D) :
    p.map (DeclarationHom.compose f g) = (p.map f).map g := by
  have composition : p.resolved.map (Core.Rule.map
      ((f.symbols.toHom : D.signature ⟶ E.signature) ≫ (g.symbols.toHom : E.signature ⟶ F.signature))) =
      (p.resolved.map (Core.Rule.map f.symbols.toHom)).map (Core.Rule.map g.symbols.toHom) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro r _
    exact Core.Rule.map_comp f.symbols.toHom g.symbols.toHom r
  exact ext _ _ rfl rfl composition
end AcceptedProgram

namespace Supplied

def ambient : SuppliedSignature ⥤ Core.Signature where
  obj S := S.ambient
  map f := f.ambient
  map_id _ := rfl
  map_comp _ _ := rfl

namespace Direct
abbrev Sentence (S : SuppliedSignature) := AcceptedProgram S.declarations

def family (S : SuppliedSignature) (p : Sentence S) : FamilySentence S.ambient :=
  ⟨.supplied S.declarations p, S.symbols⟩

def Holds {S : SuppliedSignature} (M : Core.Model S.ambient) (p : Sentence S) : Prop :=
  (family S p).Holds M

def decode {S : SuppliedSignature} (p : Sentence S) : Set (Core.Rule S.ambient) :=
  (family S p).decode

def map {S T : SuppliedSignature} (f : S ⟶ T) (p : Sentence S) : Sentence T :=
  p.map f.vocabulary

theorem map_id (S : SuppliedSignature) (p : Sentence S) : map (𝟙 S) p = p :=
  AcceptedProgram.map_id p

theorem map_comp {S T U : SuppliedSignature} (f : S ⟶ T) (g : T ⟶ U) (p : Sentence S) :
    map (f ≫ g) p = map g (map f p) := AcceptedProgram.map_comp f.vocabulary g.vocabulary p

theorem decode_holds {S : SuppliedSignature} (M : Core.Model S.ambient) (p : Sentence S) :
    (∀ r ∈ decode p, r.Holds M) ↔ Holds M p := (family S p).decode_holds M

theorem decode_map {S T : SuppliedSignature} (f : S ⟶ T) (p : Sentence S) :
    decode (map f p) = Core.Rule.map f.ambient '' decode p := by
  change {r | ∃ original ∈ p.resolved.map (Core.Rule.map f.vocabulary.symbols.toHom),
    original.map T.symbols = r} =
    Core.Rule.map f.ambient '' {r | ∃ original ∈ p.resolved, original.map S.symbols = r}
  ext r
  constructor
  · rintro ⟨middle, member, equal⟩
    obtain ⟨original, originalMember, middleEq⟩ := List.mem_map.mp member
    subst middle
    refine ⟨original.map S.symbols, ⟨original, originalMember, rfl⟩, ?_⟩
    rw [← Core.Rule.map_comp, ← f.commutes, Core.Rule.map_comp]
    exact equal
  · rintro ⟨middle, ⟨original, member, originalEq⟩, equal⟩
    subst middle
    refine ⟨original.map f.vocabulary.symbols.toHom, List.mem_map.mpr ⟨original, member, rfl⟩, ?_⟩
    rw [← Core.Rule.map_comp, f.commutes, Core.Rule.map_comp]
    exact equal

theorem holds_map {S T : SuppliedSignature} (f : S ⟶ T) (M : Core.Model T.ambient)
    (p : Sentence S) : Holds M (map f p) ↔ Holds
      ((Silmaril.Logic.Institution.Examples.EQ.Algebra.reduct f.ambient).obj M) p := by
  rw [← decode_holds, ← decode_holds, decode_map]
  constructor
  · intro h r hr
    exact (Core.Rule.holds_map f.ambient M r).mp (h _ ⟨r, hr, rfl⟩)
  · intro h r hr
    obtain ⟨original, member, rfl⟩ := hr
    exact (Core.Rule.holds_map f.ambient M original).mpr (h original member)

/-- Direct accepted complete files, with every ordinary ambient algebra hom. -/
def room (S : SuppliedSignature) : Room.{0,0,1} :=
  ⟨Sentence S, Cat.of (Core.Model S.ambient), fun M p => Holds M p⟩

def corridor {S T : SuppliedSignature} (f : S ⟶ T) : room S ⟶ room T :=
  ⟨map f, Silmaril.Logic.Institution.Examples.EQ.Algebra.reduct f.ambient, holds_map f⟩

def institution : SuppliedSignature ⥤ Room.{0,0,1} where
  obj := room
  map := corridor
  map_id S := Room.hom_ext (funext (map_id S)) rfl
  map_comp f g := Room.hom_ext (funext (map_comp f g)) rfl

def inst : Inst.{1,0,0,0,1} := ⟨SuppliedSignature, institution⟩

def toCore : Inst.CoHom inst (Silmaril.Logic.Institution.SetSentences.inst Core.inst) where
  Φ := ambient
  ρ :=
    { app _ := ⟨decode, 𝟭 _, decode_holds⟩
      naturality := by
        intro S T f
        exact Room.hom_ext (funext (decode_map f)) rfl }

theorem toCore_modelExpansive : toCore.ModelExpansive := fun _ M => ⟨M, rfl⟩

/-- This original-receipt comparison is per room. It is not claimed strictly
natural, since supplied transport changes the declaration receipt record. -/
def familyCorridor (S : SuppliedSignature) : room S ⟶ Families.room S.ambient :=
  ⟨family S, 𝟭 _, fun _ _ => Iff.rfl⟩
end Direct
end Supplied
end Silmaril.Logic.Egg.Source.Named

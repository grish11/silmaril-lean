module

public import Silmaril.Proofs.Logic.FirstOrderLFP.Renaming

@[expose] public section
namespace Silmaril.Logic.FirstOrderLFP
open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Examples

theorem Sentence.map_id {S : Signature} (p : Sentence S) : p.map (𝟙 S) = p := by
  obtain ⟨P, Γ, p⟩ := p
  exact congrArg (Sentence.mk P Γ) p.map_id

theorem Sentence.map_comp {S T U : Signature} (f : S ⟶ T) (g : T ⟶ U)
    (p : Sentence S) : p.map (f ≫ g) = (p.map f).map g := by
  obtain ⟨P, Γ, p⟩ := p
  exact congrArg (Sentence.mk _ _) (p.map_comp f g)

theorem sat_map {S T : Signature} (f : S ⟶ T) (M : Model T) (p : Sentence S) :
    Sat M (p.map f) ↔ Sat ((reduct f).obj M) p := by
  unfold Sat Sentence.map
  rw [Formula.denote_map]
  rfl

def institution : Signature ⥤ Room.{0, 0, 1} where
  obj S := ⟨Sentence S, Cat.of (Model S), Sat⟩
  map f := ⟨Sentence.map f, reduct f, sat_map f⟩
  map_id _S := Room.hom_ext (funext Sentence.map_id) rfl
  map_comp f g := Room.hom_ext (funext (Sentence.map_comp f g)) rfl

/-- The institution as a bundled `Inst`: its signatures and room functor `institution`, named so
that records and comorphisms can refer to it. -/
def inst := (⟨Signature, institution⟩ : Silmaril.Logic.Institution.Inst)

/-- The public FOL formula is included without changing any term or binder. -/
def encodeFOL {S : Signature} (p : FOL.Sentence S) : Sentence S :=
  ⟨fun i => ⟨0, fun _ => p.ctx i⟩, p.ctx, .base p.formula⟩

/-- Models retain the actual public FOL structure, with equality as their arrows. -/
def forgetFOL (S : Signature) : Model S ⥤ FOL.Structure S where
  obj := Model.toStructure
  map h := eqToHom (congrArg Model.toStructure h.down)
  map_id _ := rfl
  map_comp f g := by cases f.down; cases g.down; rfl

def folCorridor (S : Signature) : FOL.institution.obj S ⟶ institution.obj S where
  sen := encodeFOL
  mod := forgetFOL S
  sat := fun _ _ => Iff.rfl

def folNatural : FOL.institution ⟶ (𝟭 Signature) ⋙ institution where
  app := folCorridor
  naturality := by
    intro S T f
    apply Room.hom_ext (funext fun p => by cases p; rfl)
    refine Functor.ext (fun _ => rfl) ?_
    intro M N h
    cases h.down
    rfl

/-- A genuine institution comorphism from the pinned public many-sorted FOL. -/
def folToLFP : Inst.CoHom FOL.inst ⟨Signature, institution⟩ := ⟨𝟭 Signature, folNatural⟩

theorem folToLFP_modelExpansive : folToLFP.ModelExpansive :=
  fun _ M => ⟨⟨M⟩, rfl⟩

/-- Exact preservation and reflection of satisfiability for an included FOL sentence. -/
theorem fol_sat_iff {S : Signature} (p : FOL.Sentence S) :
    (∃ M : FOL.Structure S, p.Holds M) ↔ ∃ M : Model S, Sat M (encodeFOL p) := by
  constructor
  · rintro ⟨M, h⟩
    exact ⟨⟨M⟩, h⟩
  · rintro ⟨M, h⟩
    exact ⟨M.toStructure, h⟩

/-- Unsatisfiability is preserved and reflected by the same inclusion. -/
theorem fol_unsat_iff {S : Signature} (p : FOL.Sentence S) :
    (¬ ∃ M : FOL.Structure S, p.Holds M) ↔ ¬ ∃ M : Model S, Sat M (encodeFOL p) :=
  not_congr (fol_sat_iff p)

theorem fol_entails_iff (S : Signature) (H : Set (FOL.Sentence S)) (p : FOL.Sentence S) :
    (FOL.institution.obj S).Entails H p ↔
      (institution.obj S).Entails (encodeFOL '' H) (encodeFOL p) :=
  folToLFP.entails_iff folToLFP_modelExpansive S H p

end Silmaril.Logic.FirstOrderLFP

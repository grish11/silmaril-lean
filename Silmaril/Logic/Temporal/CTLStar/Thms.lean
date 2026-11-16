module

public import Silmaril.Proofs.Logic.Temporal.CTLStar.Bridges
public import Silmaril.Proofs.Logic.Temporal.CTLStar.Isomorphisms
public import Silmaril.Proofs.Logic.Temporal.CTLStar.PathSemantics
public import Silmaril.Proofs.Logic.Temporal.CTLStar.Infinite
public import Mathlib.CategoryTheory.Core

@[expose] public section
namespace Silmaril.Logic.Temporal.CTLStar
open CategoryTheory Silmaril.Logic.Institution

/-- Full CTL* syntax with the discrete category needed for the existing CTL reduct. -/
def institution : Signature ⥤ Room where
  obj S := ⟨StateFormula S, Cat.of (Model S), Sat⟩
  map f := ⟨StateFormula.map f, CTL.modelReduct f, fun M p => p.holds_map f M M.toModal.point⟩
  map_id _ := Room.hom_ext (funext StateFormula.map_id) rfl
  map_comp f g := Room.hom_ext (funext (StateFormula.map_comp f g)) rfl

/-- `institution` as a bundled `Inst`, named so that records and comorphisms can refer to it. -/
def inst := (⟨Signature, institution⟩ : Silmaril.Logic.Institution.Inst)

def ctlNatural : CTL.institution ⟶ (𝟭 Signature) ⋙ institution where
  app S := ⟨encodeCTL, 𝟭 _, fun M p => encodeCTL_holds M p M.toModal.point⟩
  naturality := by
    intro S T f
    exact Room.hom_ext (funext (encodeCTL_map f)) rfl

def ctlToCTLStar : Inst.CoHom ⟨Signature, CTL.institution⟩ ⟨Signature, institution⟩ :=
  ⟨𝟭 _, ctlNatural⟩

theorem ctlToCTLStar_modelExpansive : ctlToCTLStar.ModelExpansive :=
  fun _ M => ⟨M, rfl⟩

theorem ctl_entails_iff (S : Signature) (H : Set (CTL.Formula S)) (p : CTL.Formula S) :
    (CTL.institution.obj S).Entails H p ↔
      (institution.obj S).Entails (encodeCTL '' H) (encodeCTL p) :=
  ctlToCTLStar.entails_iff ctlToCTLStar_modelExpansive S H p

/-- Actual isomorphisms of pointed Kripke models, including state permutations. -/
abbrev RichModel (S : Signature) := Core (Modal.Model S)

def richInstitution : Signature ⥤ Room where
  obj S := ⟨StateFormula S, Cat.of (RichModel S), fun M p => Sat ⟨M.of⟩ p⟩
  map f := ⟨StateFormula.map f, (Modal.reduct f).core,
    fun M p => p.holds_map f ⟨M.of⟩ M.of.point⟩
  map_id _ := Room.hom_ext (funext StateFormula.map_id) rfl
  map_comp f g := Room.hom_ext (funext (StateFormula.map_comp f g)) rfl

/-- `richInstitution` as a bundled `Inst`, named so that records and comorphisms can refer to it. -/
def richInst := (⟨Signature, richInstitution⟩ : Silmaril.Logic.Institution.Inst)

/-- Objects agree, but the rich category admits nonidentity frame isomorphisms. -/
def discreteToRich (S : Signature) : Model S ⥤ RichModel S where
  obj M := ⟨M.toModal⟩
  map h := ⟨eqToIso (congrArg CTL.Model.toModal h.down)⟩
  map_id _ := rfl
  map_comp f g := by cases f.down; cases g.down; rfl

def richDiscreteNatural : richInstitution ⟶ (𝟭 Signature) ⋙ institution where
  app S := ⟨id, discreteToRich S, fun _ _ => Iff.rfl⟩
  naturality := by
    intro S T f
    refine Room.hom_ext ?_ ?_
    · rfl
    refine Functor.ext (fun _ => rfl) ?_
    intro M N h
    cases h.down
    rfl

/-- The honest arrow is rich -> discrete: model reduction goes discrete -> rich. -/
def richToDiscrete : Inst.CoHom ⟨Signature, richInstitution⟩ ⟨Signature, institution⟩ :=
  ⟨𝟭 _, richDiscreteNatural⟩

theorem richToDiscrete_modelExpansive : richToDiscrete.ModelExpansive := by
  intro S M
  exact ⟨⟨M.of⟩, by cases M; rfl⟩

theorem rich_entails_iff (S : Signature) (H : Set (StateFormula S)) (p : StateFormula S) :
    (richInstitution.obj S).Entails H p ↔ (institution.obj S).Entails H p := by
  constructor
  · intro h M hM
    exact h ⟨M.toModal⟩ hM
  · intro h M hM
    exact h ⟨M.of⟩ hM

theorem ctl_satisfiable_iff (S : Signature) (H : Set (CTL.Formula S)) :
    (∃ M : CTL.Model S, ∀ p ∈ H, CTL.Sat M p) ↔
      ∃ M : Model S, ∀ q ∈ encodeCTL '' H, Sat M q := by
  constructor
  · rintro ⟨M, h⟩
    refine ⟨M, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    exact (encodeCTL_holds M p M.toModal.point).mpr (h p hp)
  · rintro ⟨M, h⟩
    exact ⟨M, fun p hp => (encodeCTL_holds M p M.toModal.point).mp
      (h _ ⟨p, hp, rfl⟩)⟩

theorem ctl_unsatisfiable_iff (S : Signature) (H : Set (CTL.Formula S)) :
    (¬ ∃ M : CTL.Model S, ∀ p ∈ H, CTL.Sat M p) ↔
      ¬ ∃ M : Model S, ∀ q ∈ encodeCTL '' H, Sat M q :=
  not_congr (ctl_satisfiable_iff S H)

theorem rich_satisfiable_iff (S : Signature) (H : Set (StateFormula S)) :
    (∃ M : RichModel S, ∀ p ∈ H, Sat ⟨M.of⟩ p) ↔
      ∃ M : Model S, ∀ p ∈ H, Sat M p := by
  constructor
  · rintro ⟨M, h⟩
    exact ⟨⟨M.of⟩, h⟩
  · rintro ⟨M, h⟩
    exact ⟨⟨M.toModal⟩, h⟩

theorem rich_unsatisfiable_iff (S : Signature) (H : Set (StateFormula S)) :
    (¬ ∃ M : RichModel S, ∀ p ∈ H, Sat ⟨M.of⟩ p) ↔
      ¬ ∃ M : Model S, ∀ p ∈ H, Sat M p :=
  not_congr (rich_satisfiable_iff S H)

/-- Every rich model arrow preserves and reflects full CTL* satisfaction. -/
theorem rich_hom_sat {S : Signature} {M N : RichModel S} (e : M ⟶ N)
    (p : StateFormula S) : Sat ⟨M.of⟩ p ↔ Sat ⟨N.of⟩ p :=
  p.sat_iso (FrameIso.ofModalIso e.iso)

end Silmaril.Logic.Temporal.CTLStar

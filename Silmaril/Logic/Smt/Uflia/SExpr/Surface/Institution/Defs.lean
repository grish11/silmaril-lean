module

public import Silmaril.Logic.Smt.Uflia.SExpr.Surface.Defs
public import Silmaril.Logic.Smt.Uflia.Script.Defs

/-! Genuinely direct source satisfaction for accepted assertions and scripts.
Sentences retain executable acceptance evidence, but satisfaction uses only the
independent source relation in one coherent global model. Existing institutions
remain unchanged. Signature maps here are equality transports only. -/

@[expose] public section

namespace Silmaril.Logic.Smt.Uflia.SExpr.Surface.Direct

open CategoryTheory Silmaril.Inst Silmaril.Logic.Institution

/-- Independent source satisfaction for a structured accepted assertion list. -/
def ConcreteHolds (sentence : Packaged.ConcreteSentence) (M : Packaged.GlobalModel) : Prop :=
  ∀ a ∈ sentence.assertions, Holds sentence.checked.environment M a.expression

/-- Independent source satisfaction of the assertions retained by an accepted script. -/
def ScriptHolds (script : Uflia.Script.Accepted) (M : Packaged.GlobalModel) : Prop :=
  ConcreteHolds script.sentence M

/-- Direct accepted source assertions, with coherent typed-name models. -/
noncomputable def plain : Plain (Disc Environment) where
  Sen E := Assertion E
  map σ a := σ.down ▸ a
  map_id _ _ := rfl
  map_comp σ τ a := by
    rcases σ with ⟨h⟩
    cases h
    rcases τ with ⟨h⟩
    cases h
    rfl
  Mod _ := Packaged.GlobalModel
  reduct _ := id
  reduct_id _ _ := rfl
  reduct_comp _ _ _ := rfl
  Sat {E} M a := Holds E M a.expression
  sat_map σ M a := by
    rcases σ with ⟨h⟩
    cases h
    rfl

noncomputable abbrev institution := plain.toInst
noncomputable abbrev room (E : Environment) := plain.room E

/-- Restrict the signature objects to declaration prefixes accepted by the frontend. -/
noncomputable def declarationFunctor : Disc DeclarationPrefix ⥤ Room :=
  Disc.functor DeclarationPrefix.environment ⋙ plain.functor

noncomputable abbrev declarationInstitution := Institution.ofFunctor declarationFunctor
noncomputable abbrev declarationRoom (checked : DeclarationPrefix) := declarationFunctor.obj checked

/-- Whole structured sentences carry declarations, while their satisfaction stays direct. -/
noncomputable def concretePlain : Plain (Disc Unit) where
  Sen _ := Packaged.ConcreteSentence
  map _ := id
  map_id _ _ := rfl
  map_comp _ _ _ := rfl
  Mod _ := Packaged.GlobalModel
  reduct _ := id
  reduct_id _ _ := rfl
  reduct_comp _ _ _ := rfl
  Sat M sentence := ConcreteHolds sentence M
  sat_map _ _ _ := Iff.rfl

noncomputable abbrev concreteInstitution := concretePlain.toInst
noncomputable abbrev concreteRoom := concretePlain.room ()

/-- Accepted single-query scripts with independent source satisfaction. -/
noncomputable def scriptPlain : Plain (Disc Unit) where
  Sen _ := Uflia.Script.Accepted
  map _ := id
  map_id _ _ := rfl
  map_comp _ _ _ := rfl
  Mod _ := Packaged.GlobalModel
  reduct _ := id
  reduct_id _ _ := rfl
  reduct_comp _ _ _ := rfl
  Sat M script := ScriptHolds script M
  sat_map _ _ _ := Iff.rfl

noncomputable abbrev scriptInstitution := scriptPlain.toInst
noncomputable abbrev scriptRoom := scriptPlain.room ()

end Silmaril.Logic.Smt.Uflia.SExpr.Surface.Direct

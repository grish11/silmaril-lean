module

public import Silmaril.Calculi.PERConstraints.Interval.Thms
public import Silmaril.Calculi.PERConstraints.Thms
public import Silmaril.Logic.Institution.Generalized.Defs

@[expose] public section

/-! # Generalized institution of PER interval constraints -/

namespace Silmaril.Calculi.PERConstraints

open CategoryTheory Opposite Silmaril.Logic.Institution Silmaril.Formats

/-- Discrete bounds models reduced by pulling back both endpoints. -/
def boundsModelFunctor : Syntaxᵒᵖ ⥤ Cat.{0,0} :=
  (show Syntaxᵒᵖ ⥤ Type from
    { obj := fun S => Bounds S.unop.Term
      map := fun f => TypeCat.ofHom (Bounds.reduct f.unop)
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl }) ⋙ typeToCat

/-- Shared universal completion evidence for a CNF query on a PER interval. -/
def intervalEvidence {α : Type} (bounds : Bounds α) (admissible : PER α → Prop)
    (sentence : CNF α) : Generalized.Evidence :=
  Generalized.Evidence.ofCompletions (bounds.completions admissible) (fun model => sentence.Holds model)

/-- A pullback-stable admissibility predicate gives a lax evaluation on PER bounds. -/
def intervalLaxWith (admissible : (S : Syntax) → Model S → Prop)
    (preserves : ∀ {S T : Syntax} (f : S ⟶ T) (model : Model T),
      admissible T model → admissible S (reduct f model)) :
    Generalized.LaxInstitution Syntax Generalized.Evidence where
  Sen := sentenceFunctor institution
  Mod := boundsModelFunctor
  eval S M F := intervalEvidence (Discrete.as M) (admissible S) F
  le_eval_map f M F := Bounds.flags_map ((Discrete.as M).pull_mapsTo f.term (preserves f)) F

/-- The unrestricted interval profile allows every PER between the endpoints. -/
def intervalLax : Generalized.LaxInstitution Syntax Generalized.Evidence :=
  intervalLaxWith (fun _ _ => True) (fun _ _ h => h)

end Silmaril.Calculi.PERConstraints

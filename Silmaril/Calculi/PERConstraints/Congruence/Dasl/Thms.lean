module

public import Silmaril.Calculi.PERConstraints.Congruence.Dasl.Defs
public import Silmaril.Calculi.PERConstraints.Congruence.Thms

namespace Silmaril.Calculi.PERConstraints.Congruence

open CategoryTheory Silmaril.Formats.Dasl

private def refsOnly {Ref : Type} : Tree.Shape Ref Empty → Prop
  | .leaf (.ref _) => True
  | _ => False

private def collapseRefs : daslSignature (@refsOnly Bool) ⟶ daslSignature (@refsOnly Unit) :=
  daslMap (fun _ => ()) id fun shape => by
    cases shape <;> first | exact id | rename_i terminal; cases terminal <;> exact id

example (model : Model (daslSignature (@refsOnly Unit))) :
    (reduct collapseRefs model).val.rel (.ref false) (.ref true) :=
  model.property (.leaf (.ref ())) (left := Empty.elim) (right := Empty.elim)
    trivial trivial (fun pos => pos.elim)

end Silmaril.Calculi.PERConstraints.Congruence

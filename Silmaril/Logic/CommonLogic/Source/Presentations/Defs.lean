module

public import Silmaril.Logic.CommonLogic.Source.CLIF.Thms
public import Silmaril.Logic.CommonLogic.FiniteListFOL.Translation.Thms

@[expose] public section
namespace Silmaril.Logic.CommonLogic.Source.Presentations
open CategoryTheory Silmaril.Logic.Institution

/-- The actual existing full-Core finite-list FOL comparison, after source
elaboration. The target retains arbitrary admitted FOL sentences and all model
arrows; no fixture-specific signature or equality-only room is substituted. -/
noncomputable def fixed {S : Core.Signature} (names : Names S) :
    CLIF.room names ⟶ FiniteListFOL.room S :=
  CLIF.toCore names ≫ FiniteListFOL.comparison S

end Silmaril.Logic.CommonLogic.Source.Presentations

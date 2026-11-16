module

public import Silmaril.Logic.Matching.SortMaps.Thms
public import Silmaril.Logic.Matching.GeneralFixedPoint.Institution

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.SortMaps.Hom
open CategoryTheory
variable {A B : Signature}

/-- Reindex all sorts in the full Boolean syntax, retaining the actual μ/ν
binders. Admission is transported separately, not assumed by this operation. -/
def generalPattern (f : A ⟶ B) {r k : Nat} {P : Fin r → A.sorts}
    {Γ : Fin k → A.sorts} {s : A.sorts}
    (p : GeneralFixedPoint.Pattern A.symbols P Γ s) :
    GeneralFixedPoint.Pattern B.symbols (f.sorts ∘ P) (f.sorts ∘ Γ) (f.sorts s) := by
  induction p with
  | base p => exact .base (pattern f p)
  | setvar i => exact .setvar i
  | app op _ ih => exact .app (f.operations op) ih
  | neg _ ih => exact .neg ih
  | conj _ _ hp hq => exact .conj hp hq
  | ex bound _ ih => exact .ex (f.sorts bound) ((map_cons f bound _) ▸ ih)
  | mu _ ih => exact .mu ih
  | nu _ ih => exact .nu ih

end Silmaril.Logic.Matching.SortMaps.Hom

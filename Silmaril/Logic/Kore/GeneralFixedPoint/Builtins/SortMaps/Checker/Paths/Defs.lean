module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Checker.Receipts.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Surface
open CategoryTheory Silmaril.Logic.Institution

/-- Validation is preserved at every intermediate package of a structural path. -/
theorem Path.literalProfiles_forward {A B : Package} (path : Path A B) :
    literalProfiles A = true → literalProfiles B = true := by
  induction path with
  | nil => exact id
  | cons f tail ih => exact fun valid => ih (f.literalProfiles_forward valid)

/-- Map a receipt step by step. The empty path preserves the actual receipt. -/
def SourceSentence.mapPath {A B : Package} (path : Path A B) :
    literalProfiles A = true → SourceSentence A → SourceSentence B :=
  match path with
  | .nil _ => fun _ p => p
  | .cons f tail => fun valid p =>
      mapPath tail (f.literalProfiles_forward valid) (p.mapStep f valid)

end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Surface

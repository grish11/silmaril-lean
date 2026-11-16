module

public import Silmaril.Logic.Separation.Parameterized.Matching.Defs
public import Silmaril.Logic.Separation.Parameterized.FirstOrder.Transport.Thms
public import Silmaril.Logic.Matching.GuardedLFP.Institution

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Logic.Separation.Parameterized.Matching
open CategoryTheory Silmaril.Logic.Institution.Examples

private theorem rawModel_ext {S : Type} {A : Algebraic.ManySorted.Signature S}
    (M N : Silmaril.Logic.Matching.FirstOrder.Model A) (hc : M.carrier = N.carrier)
    (ho : ∀ n inputs output (op : A.operations n inputs output),
      HEq (@M.operation n inputs output op) (@N.operation n inputs output op)) : M = N := by
  cases M with
  | mk mc mn mo =>
    cases N with
    | mk nc nn no =>
      cases hc
      have he : @mo = @no := by
        funext n inputs output op
        exact eq_of_heq (ho n inputs output op)
      cases he
      rfl

/-- Actual raw matching reduct of the canonical padded expansion. -/
theorem expansion_reduct {S T : FOL.Signature} (f : S ⟶ T) (M : FOL.Structure T) :
    Silmaril.Logic.Matching.SortMaps.Hom.reduct (Silmaril.Logic.Matching.GuardedLFP.signatureMap f)
      (Silmaril.Logic.Matching.GuardedLFP.rawExpansion M) =
    Silmaril.Logic.Matching.GuardedLFP.rawExpansion ((FOL.Structure.reduct f).obj M) := by
  apply rawModel_ext
  · funext s
    cases s with
    | base s => cases s <;> rfl
    | tuple p => rfl
  · intro n inputs output op
    cases op with
    | base o => cases o <;> rfl
    | pack p => rfl
    | project p i => rfl
    | active p => rfl
    | defined p => rfl
    | liftTruth p => rfl

end Silmaril.Logic.Separation.Parameterized.Matching

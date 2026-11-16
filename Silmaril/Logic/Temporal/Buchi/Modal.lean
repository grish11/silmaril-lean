module

public import Silmaril.Logic.Temporal.Buchi.Thms
public import Silmaril.Logic.ModalMu.Thms

@[expose] public section
namespace Silmaril.Logic.Temporal.Buchi
open CategoryTheory

/-- Actual closed modal μ syntax; variable0 is Y, variable1 is the captured Z. -/
def infinitelyOften {S : ModalMu.Signature} (a : S.Action) (p : S.Atom) : ModalMu.Formula S 0 :=
  .nu (.mu (.disj (.conj (.pos p) (.diamond a (.var 1))) (.diamond a (.var 0))))

/-- Exact equality with the independently defined nested set fixed point. -/
theorem infinitelyOften_denote {S : ModalMu.Signature} (M : ModalMu.Model S)
    (a : S.Action) (p : S.Atom) :
    (infinitelyOften a p).denote M ModalMu.emptyEnv = (outer (M.step a) (M.valuation p)).gfp := by
  rfl

/-- The native formula expresses one actual infinite path visiting p arbitrarily
late, on every pointed model, including nonserial and infinitely branching ones. -/
theorem infinitelyOften_iff {S : ModalMu.Signature} (M : ModalMu.Model S)
    (a : S.Action) (p : S.Atom) (w : M.World) :
    w ∈ (infinitelyOften a p).denote M ModalMu.emptyEnv ↔ Accepts (M.step a) (M.valuation p) w := by
  rw [infinitelyOften_denote]
  exact (accepts_iff_gfp _ _ _).symm

/-- Arbitrary action/atom signature maps preserve the actual formula. -/
theorem infinitelyOften_map {S T : ModalMu.Signature} (f : S ⟶ T)
    (a : S.Action) (p : S.Atom) :
    (infinitelyOften a p).map f = infinitelyOften (f.action a) (f.atom p) := rfl

end Silmaril.Logic.Temporal.Buchi

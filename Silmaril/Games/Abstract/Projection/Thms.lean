module

public import Silmaril.Games.Abstract.Projection.Defs
public import Silmaril.Games.Abstract.Module.Thms
import Silmaril.Proofs.Games.Abstract.Projection.Basic

/-!
# Projections: theorems

* `close_preserves`: closing open modules preserves trap ≈ divergence
  equivalence (from `Shape.close_congr`).
* `close_not_reflects`: it does not reflect it. A self-recursive function and
  an empty one are different open modules with the same closure, so the
  closed module forgets how a function failed to produce behaviours.

The Wasm instances are in `Silmaril.Wasm.Abstract.Projection`.
-/

public section

namespace Silmaril.Games.Abstract

universe u

/-- Closing preserves trap ≈ divergence equivalence of open modules. -/
theorem close_preserves (sh : Shape.{u}) :
    PreservesMod (X := OpenModule sh) (fun m m' => Shape.OpenCollapseEquiv m.mod m'.mod) :=
  Silmaril.Proofs.Games.Abstract.Projection.close_preserves sh

/-- Closing does not reflect trap ≈ divergence equivalence of open modules. -/
theorem exists_close_not_reflects :
    ∃ sh : Shape.{0},
      ¬ ReflectsMod (X := OpenModule sh) (fun m m' => Shape.OpenCollapseEquiv m.mod m'.mod) :=
  ⟨_, Silmaril.Proofs.Games.Abstract.Projection.close_not_reflects⟩

end Silmaril.Games.Abstract

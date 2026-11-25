module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Defs

/-! # Binding computations before branching -/

public section

universe u

namespace Silmaril.Isotope.LambdaSSA.Region

/-- Evaluate each branch argument once in a let whose body forwards the bound
variable. All CFG arities and label indices remain the same. -/
@[expose] def bindBranchArguments {Φ : Type u} : Region Φ → Region Φ
  | .br ℓ a => .let₁ a (.br ℓ (.var 0))
  | .let₁ a r => .let₁ a r.bindBranchArguments
  | .let₂ a r => .let₂ a r.bindBranchArguments
  | .case a l r => .case a l.bindBranchArguments r.bindBranchArguments
  | .cfg e n blocks => .cfg e.bindBranchArguments n (fun i => (blocks i).bindBranchArguments)

end Silmaril.Isotope.LambdaSSA.Region

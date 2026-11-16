module

public import Silmaril.Proofs.Logic.Algebraic.InitialMatching.Institution

/-!
# Constructor initiality compiled to native matching: the institutions, named

`source` (single-sort equational logic with a selected constructor) and `target` (native matching
logic with structural constructor generation) are room functors over `Signature`; `sourceInst` and
`targetInst` bundle them, so that `toMatching : Inst.CoHom ⟨Signature, source⟩ ⟨Signature, target⟩`
can be registered with named endpoints. Names only: the definitions are the bundles `toMatching`
already uses.
-/

@[expose] public section

namespace Silmaril.Logic.Algebraic.Initial.Matching

/-- The source institution of `toMatching`, bundled. -/
def sourceInst := (⟨Signature, source⟩ : Silmaril.Logic.Institution.Inst)

/-- The target institution of `toMatching`, bundled. -/
noncomputable def targetInst := (⟨Signature, target⟩ : Silmaril.Logic.Institution.Inst)

end Silmaril.Logic.Algebraic.Initial.Matching

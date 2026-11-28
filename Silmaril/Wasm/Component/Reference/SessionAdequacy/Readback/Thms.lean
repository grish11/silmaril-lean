module

public import Silmaril.Wasm.Component.Reference.SessionAdequacy.Defs
import Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy.RefSess
import Silmaril.Proofs.Wasm.Component.Reference.SpecToIR

public section

namespace Silmaril.Wasm.Component.Reference

/-- The numeric Core instance of an import-free module is unique. -/
theorem NumModule.inst_unique {m : NumModule} {I J : Silmaril.Wasm.Game.ScalarInstance}
    (hI : m.IsInst I) (hJ : m.IsInst J) : I = J :=
  Silmaril.Proofs.Wasm.Component.Reference.NumModule.IsInst.unique hI hJ

/-- Encoding session outcomes as reference values is injective. -/
theorem refOuts_injective : Function.Injective refOuts :=
  fun _ _ => Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy.refOuts_inj

end Silmaril.Wasm.Component.Reference

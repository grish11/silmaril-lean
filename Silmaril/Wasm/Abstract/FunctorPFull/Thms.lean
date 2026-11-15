module

public import Silmaril.Wasm.Abstract.ExposePStruct.Thms
public import Silmaril.Wasm.Abstract.FullObs.Thms

/-!
# The canonical denotation and the full observation

The full observation `FullObs.toFull` (finished behaviours and productive runs, the H2 owner's
generic observation pair) commutes with the structure of the canonical F5 denotation
`ExposePStruct.denL`/`denT` (exact for `CallXP.EvalOXP`): sequencing is `FullFun.seq` into the
exit-aware continuation `contP`, a loop is `FullFun.iter` of its iteration body. One rewrite each
with `ExposePStruct.denL_append`/`denT_loop` and `FullObs.toFull_comp`/`toFull_iter`.

This is about `denL` only. Results about the **native H2 closures** (`wasmEvFunD`, `wasmEvInfN`,
over `HostClosing.wasmHOpen`) transfer to `denL` only through the proved bridges
(`FunctorP.denListXP_native` on direct-call, exception-free code, and the closure-level
coincidence on direct stores), not by identification.
-/

public section

namespace Silmaril.Wasm.Abstract.FunctorPFull

open Silmaril.Wasm Silmaril.Wasm.Abstract.ExposePStruct Silmaril.Wasm.Abstract.FullObs
open Silmaril.Games.Abstract

variable {H : Type}

/-- **Sequencing**: the full observation of concatenated code is the sequencing of the first
part's observation with that of the exit-aware continuation into the second. -/
theorem toFull_denL_append (es₁ es₂ : List Binaryen.BExpr) :
    toFull (denL (H := H) (es₁ ++ es₂)) = FullFun.seq (toFull (denL es₁)) (toFull (contP (denL es₂))) := by
  rw [denL_append]; exact toFull_comp _ _

/-- **Iteration**: the full observation of a loop is the iteration of its iteration body's. -/
theorem toFull_denT_loop (bt : BlockType) (body : List Binaryen.BExpr) :
    toFull (denT (H := H) (.loop bt body)) = FullFun.iter (toFull (loopStepP bt (denL body))) := by
  rw [denT_loop]; exact toFull_iter _

/-- **Identity**: the empty code is observed as `idP`. -/
theorem toFull_denL_nil : toFull (denL (H := H) []) = toFull (idP (H := H)) := by
  rw [denL_nil]

end Silmaril.Wasm.Abstract.FunctorPFull

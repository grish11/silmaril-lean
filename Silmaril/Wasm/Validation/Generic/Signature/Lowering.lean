module

public import Silmaril.Wasm.SSA.OutOfSSA.Defs
public import Silmaril.Wasm.SSA.Bridge.Defs
public import Silmaril.Wasm.Binaryen.Lower

@[expose] public section

namespace Silmaril.Wasm.Generic.Signature

open Silmaril.Isotope.LambdaSSA

/-- Run the existing integer Wasm dialect's out-of-SSA and Binaryen lowerings.
The signature is the one emitted in the Core type group, not a second copy
supplied by the body. Validation is separate from successful translation. -/
def lowerRegion? (index : TypeIdx) (sig : FuncType) (code : Region Wasm.SSA.Prim) :
    Option (List ValType × Wasm.Expr) := do
  let params ← sig.params.mapM Wasm.SSA.ofValType?
  let result ← match sig.results with
    | [] => some none
    | [type] => some <$> Wasm.SSA.ofValType? type
    | _ => none
  let fragment ← Wasm.SSA.decompileFunc ⟨params, result, code⟩
  let binaryen ← Wasm.SSA.toBFunc? index fragment
  return (binaryen.locals, Binaryen.BExpr.lowerList binaryen.body)

end Silmaril.Wasm.Generic.Signature

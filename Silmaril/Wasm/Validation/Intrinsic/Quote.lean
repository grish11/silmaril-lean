module

public import Silmaril.Wasm.Validation.Intrinsic.Defs
public import Silmaril.Prelude.Bytes.Elab.Defs
public meta import Lean.Elab.Command
public meta import Lean.Elab.Term

/-! Publish explicit intrinsic terms and optionally check erasure to a separately supplied
raw term. The intrinsic constructors are checked by Lean, without reading a binary. -/

public meta section

namespace Silmaril.Wasm.Validation.Intrinsic

open Lean Elab Command

/-- Publish a reducible, context-indexed module assembled from intrinsic constructors. -/
macro "wasm_intrinsic " name:ident " : " interface:term " := " value:term : command =>
  `(@[expose] public def $name : Silmaril.Wasm.Validation.Intrinsic.Module $interface := $value)

/-- Prove `typed.erase = raw` from the actual Lean terms. This is not a source decode theorem. -/
elab "wasm_prove_erasure " name:ident " : " typed:term " => " raw:term : command => do
  let ns ← getCurrNamespace
  let (statement, proof) ← liftTermElabM do
    let typed ← Term.elabTerm typed none
    let raw ← Term.elabTermEnsuringType raw (mkConst ``Wasm.Module)
    let erased ← Meta.mkAppM ``Module.erase #[typed]
    Term.synthesizeSyntheticMVarsNoPostponing
    let statement ← instantiateMVars (← Meta.mkEq erased raw)
    let proof ← Meta.mkEqRefl (← instantiateMVars raw)
    return (statement, proof)
  liftCoreM <| KBytes.Elab.addThm (ns ++ name.getId) statement proof

end Silmaril.Wasm.Validation.Intrinsic

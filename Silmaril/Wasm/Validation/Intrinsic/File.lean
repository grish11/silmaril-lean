module

public import Silmaril.Wasm.Validation.Intrinsic.Reify
public meta import Silmaril.Wasm.Validation.Intrinsic.Reify
public meta import Silmaril.Wasm.Binary.Quote.Defs
public meta import Silmaril.Wasm.Binary.Core.Decode
public meta import Silmaril.Prelude.Bytes.Elab.Defs
public meta import Lean.Elab.Command

public meta section

namespace Silmaril.Wasm.Validation.Intrinsic

open Lean Elab Command Reify

private def defineIntrinsicFile (witness : TSyntax `ident) (file : TSyntax `str)
    (raw : TSyntax `ident) (source : Option Syntax) : CommandElabM Unit := do
  let namespace_ ← getCurrNamespace
  let rawName := namespace_ ++ raw.getId
  let witnessName := namespace_ ++ witness.getId
  let sourceName := source.map (fun name => namespace_ ++ name.getId)
  if rawName == witnessName || sourceName == some rawName || sourceName == some witnessName then
    throwError "wasm_intrinsic_file: witness, raw and source names must be distinct"
  liftCoreM <| withRef file do
    let bytes ← KBytes.Elab.readRelative file.getString
    let decoded ← match Binary.Core.Decode.decodeModule bytes with
      | .ok decoded => pure decoded
      | .error error => throwError "wasm_intrinsic_file: malformed Core binary: {error}"
    unless (reify? decoded).isSome do
      if (validate? decoded).isSome then
        throwError "wasm_intrinsic_file: well-typed Core module outside the supported intrinsic fragment"
      else
        throwError "wasm_intrinsic_file: ill-typed Core module (Core validator rejected it)"
    KBytes.Elab.addDefn rawName (mkConst ``Wasm.Module) (Binary.Quote.quoteModule decoded) false
    let rawExpr := mkConst rawName
    let success := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
    KBytes.Elab.addDefn witnessName (mkApp (mkConst ``Reified) rawExpr)
      (mkApp2 (mkConst ``checked) rawExpr success) false
    if let some sourceName := sourceName then
      let chunk := KBytes.Elab.chunkSize
      KBytes.Elab.defineKBytes sourceName chunk bytes.size (KBytes.Elab.chunksOf bytes chunk) false

/-- Emit a raw module term and a kernel-checked intrinsic witness. Paths are relative to
 the current Lean file. Neither declaration contains a source decoding computation. -/
elab "wasm_intrinsic_file " witness:ident &" from " file:str &" with_raw " raw:ident : command =>
  defineIntrinsicFile witness file raw none

/-- Also publish independent packed source bytes, without proving byte decode agreement. -/
elab "wasm_intrinsic_file " witness:ident &" from " file:str &" with_raw " raw:ident
    &" with_source " source:ident : command =>
  defineIntrinsicFile witness file raw (some source)

end Silmaril.Wasm.Validation.Intrinsic

module

import SqliteWasm.ImportTyping

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation SqliteWasm

example {decoded : Module} {mt : CModuleType}
    (bytes : Binary.Core.decode? originalBytes.toByteArray = some decoded)
    (valid : ModuleOk decoded mt) :
    List.Forall₂ (ExternAddrOk reactorTypedImports) reactorImportAddrs mt.imports := by
  have pinned : decoded = sqlite := Option.some.inj (bytes.symm.trans originalDecode)
  subst decoded
  exact reactorTypedAddressCompatibility valid

#print axioms reactorTypedAddressCompatibility

module

import SqliteWasm.CorePreparation

open Silmaril.Wasm Silmaril.Wasm.Execution.Core SqliteWasm

example {decoded : Module} (bytes : Binary.Core.decode? originalBytes.toByteArray = some decoded) :
    ∃ c, prepare? evalConst? reactorTypedImports decoded reactorImportAddrs = some (c, none) ∧
      c.frame.module.funcs[25]? = some 25 := by
  have pinned : decoded = sqlite := Option.some.inj (bytes.symm.trans originalDecode)
  rw [pinned]
  exact reactorPrepared

example : (prepare? evalConst? reactorTypedImports sqlite reactorImportAddrs).map
    (fun p => (p.1.frame.module.funcs[25]?, p.2)) = some (some 25, none) :=
  reactorPreparedInitializerSlot

#print axioms reactorSegmentBounds
#print axioms reactorPreparedInitializerSlot
#print axioms reactorPrepared

module

import SqliteWasm.InitializerStartup

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open SqliteWasm

example : (Binary.Core.decode? originalBytes.toByteArray).map Module.start = some none :=
  originalStartAbsent

example :
    (Binary.Core.decode? originalBytes.toByteArray).map (fun m =>
      (m.imports.all (fun i => match i.type with | .func _ => true | _ => false),
        m.globals[1]?.map Global.init,
        m.memories.map fun memory => (memory.address, memory.limits.min.val))) =
      some (true, some [.intConst .i32 0], [(.i32, 2)]) :=
  originalSetupDeclarations

example := @initializerReturns
example := @initializerReturnsAfterAllocation
example := @initializerTrapsOnNonzero

example := initializerFlagStaysMarked

#print axioms originalSetupDeclarations
#print axioms initializerSignature
#print axioms initializerReturns
#print axioms initializerReturnsAfterAllocation
#print axioms initializerTrapsOnNonzero
#print axioms initializerFlagStaysMarked

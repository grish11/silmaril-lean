module

import SqliteWasm.StartupBindings

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation (Expand)
open SqliteWasm
open SqliteWasmArtifact (definedFunction?)

example {H : Type} {s allocated : Store H} {mi : ModuleInst}
    {decoded : Module} {imports : List ExternAddr} {globals : List Val}
    {tables : List Ref} {elements : List (List Ref)}
    (decode : Binary.Core.decode? originalBytes.toByteArray = some decoded)
    (alloc : allocModule? s decoded imports globals tables elements = some (allocated, mi))
    (imported : (ExternAddr.funcs imports).length = 23) :
    ∃ address fi,
      mi.exports.find? (·.name == "_initialize") = some ⟨"_initialize", .func address⟩ ∧
      mi.funcs[25]? = some address ∧ allocated.funcs[address]? = some fi ∧ fi.module = mi ∧
      fi.code = .wasm ((definedFunction? sqlite 25).get rfl) ∧ Expand fi.type (.func .nil .nil) := by
  have pinned : decoded = sqlite := Option.some.inj (decode.symm.trans originalDecode)
  subst decoded
  exact allocatedInitializeExport alloc imported

example := @allocatedStartupBindings

#print axioms allocatedStartupBindings
#print axioms allocatedInitializeExport

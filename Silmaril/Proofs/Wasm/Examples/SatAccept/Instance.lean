module

public import Silmaril.Wasm.Examples.SatAccept.Defs
public import Silmaril.Wasm.Verify.Kernel.Defs
public import Silmaril.Wasm.Game.SpecInst.Defs
public import Silmaril.Wasm.Game.Accept.Export.Defs

/-!
# The SAT acceptor: the instance

Kernel-evaluated facts about the instance of `prog` (as for
`Silmaril.Proofs.Wasm.Examples.MemberCheck`): it validates, it is allocated without a start
function, it has three functions with the code of `prog`, one memory and one global (the heap
pointer, an `i32` initialised to `heapBase`, at global address `1`), and it exports `memory`, `cabi_realloc`,
`check-stream` and `check-nested`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Examples.SatAccept

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Game
open Silmaril.Wasm.Game.Accept
open Silmaril.Wasm.Examples.SatAccept

abbrev mt0 := specMT
abbrev prep := specPrep
abbrev inst := specInst

set_option maxRecDepth 100000

theorem t_valid : (validate? prog).isSome = true := by decide +kernel
theorem t_prep : (prepare? evalConst? (importStore (CExternType.funcs mt0.imports)) prog
    (importAddrs mt0)).isSome = true := by decide +kernel
theorem t_start : prep.2 = none := by decide +kernel
theorem t_code : prep.1.code.isEmpty = true := by decide +kernel
theorem t_nf : prep.1.store.funcs.length = 3 := by decide +kernel
theorem t_fcode : prep.1.store.funcs.map FuncInst.code =
    [.wasm prog.funcs[0], .wasm prog.funcs[1], .wasm prog.funcs[2]] := rfl
theorem t_ty : prep.1.store.funcs.map (fun fi => FnType.ofDefType? fi.type) =
    [some fnType4, some fnType4, some fnType4] := by decide +kernel
theorem t_fmems : prep.1.store.funcs.map (fun fi => fi.module.mems) = [[0], [0], [0]] := by
  decide +kernel
theorem t_fglobals : prep.1.store.funcs.map (fun fi => fi.module.globals) = [[1], [1], [1]] := by
  decide +kernel
theorem t_frame_mems : prep.1.frame.module.mems = [0] := by decide +kernel
theorem t_frame_globals : prep.1.frame.module.globals = [1] := by decide +kernel
theorem t_export_memory : prep.1.frame.module.exports.map (·.name) =
    ["memory", "cabi_realloc", "check-stream", "check-nested"] := by decide +kernel
theorem t_export_realloc : exportFunc? prep.1.frame.module "cabi_realloc" = some 0 := by
  decide +kernel
theorem t_export_stream : exportFunc? prep.1.frame.module "check-stream" = some 1 := by
  decide +kernel
theorem t_export_nested : exportFunc? prep.1.frame.module "check-nested" = some 2 := by
  decide +kernel
theorem t_addrs : exportFuncAddrs prep.1.frame.module = [0, 1, 2] := by decide +kernel
theorem t_nmems : prep.1.store.mems.length = 1 := by decide +kernel
/-- The store's globals: the heap pointer is at address `1` (address `0` is the global of the
auxiliary instance that evaluates the constant expressions), both `heapBase`. -/
theorem t_globals : prep.1.store.globals.map (·.value) =
    [.i32 (BitVec.ofNat 32 heapBase), .i32 (BitVec.ofNat 32 heapBase)] := by
  decide +kernel
theorem t_imports : mt0.imports = [] := by decide +kernel

end Silmaril.Proofs.Wasm.Examples.SatAccept

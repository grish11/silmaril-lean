module

public import Silmaril.Sim.GlibcBridge.Bytes.Defs

/-!
# The import call as Wasm code (header)

The method `extCode0` of an import call (argument globals, `call ext.call`, `rax :=` result,
scratch registers `:= nd.undef`) and the host relation `extHost C mem` (`ext.call` answers as
the contract `C` admits, `nd.undef` anything). `Silmaril.Proofs.Sim.GlibcBridge.Steps.ext_steps`:
its Wasm small-step run reaches `extStore0`, the store `BRun`'s `ext` step uses.
-/

@[expose] public section

namespace Silmaril.Sim.GlibcBridge

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.X86 (Reg Word)
open Silmaril.Process (Memory)
open Silmaril.Sim.X86.G
open Silmaril.Sim.WasiBridge

/-! ## The import call in Wasm -/

/-- The host functions of the import call: `ext.call` and `nd.undef`. -/
inductive ExtTag where
  | ext | undef

/-- **The import as a Wasm host relation**: `ext.call` answers `v` for arguments `args` when the
contract `C` admits a call with some observables and result `v`; `nd.undef` answers anything;
neither changes the store. -/
def extHost (C : ImportC) (mem : Memory) : HostSemantics ExtTag := fun h s vs o =>
  match h with
  | .ext => ∃ args obs v, vs = args.map Val.i64 ∧ C mem args obs (some v) ∧
      o = .returned s (.values [Val.i64 v])
  | .undef => ∃ w : Word, o = .returned s (.values [Val.i64 w])

/-- Clobbering a scratch register: `r := nd.undef(r)`. -/
def clobberCode (ux : FuncIdx) (q : Reg) : List Instr :=
  [.intConst .i32 (BitVec.ofNat 32 q.toBitVec.toNat), .call ux, gset (.reg q)]

/-- **The import call's method** (before the driver's `ret`): the argument registers,
`call ext.call`, `rax :=` its result, every scratch register `:= nd.undef`. -/
def extCode0 (ex ux : FuncIdx) (regs : List Reg) : List Instr :=
  regs.map (fun r => gget (.reg r)) ++ [.call ex, gset (.reg .rax)] ++
    scratch.flatMap (clobberCode ux)

end Silmaril.Sim.GlibcBridge

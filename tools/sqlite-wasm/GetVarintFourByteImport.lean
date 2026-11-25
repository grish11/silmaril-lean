module

import SqliteWasm.GetVarintOneByte
import SqliteWasm.GetVarintTwoByte
import SqliteWasm.GetVarintThreeByte
import SqliteWasm.GetVarintFourByte
import Silmaril.Wasm.Verify.Kernel.Defs
import Silmaril.Wasm.Execution.Core.Instantiation

namespace SqliteWasm

open Silmaril.Formats.Sqlite
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Validation (DefType Expand)
open Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Verify.Kernel
open SqliteWasmArtifact

set_option maxRecDepth 65536

private def reader : Func := (definedFunction? sqlite 434).get rfl

private def runtimeType : DefType :=
  let group := (sqlite.types[reader.type.toNat]?).get rfl
  ((allocTypes [group])[0]?).get rfl

private def callee : FuncInst Unit := ⟨runtimeType, { mems := [1] }, .wasm reader⟩

private def caller : Frame :=
  { module := { funcs := List.replicate 435 0, mems := [0] }
    locals := [some (.i32 42)] }

private def input (first second third fourth : UInt8) : MemInst :=
  ⟨⟨.i32, ⟨0, none⟩⟩, ⟨#[0x5a, 0x5b, 9, 9, first, second, third, fourth, 9, 9, 0xa5]⟩⟩

private def output (lo next high top : UInt8) : MemInst :=
  { input 0 0 0 0 with bytes := ⟨#[0x5a, 0x5b, lo, next, high, top, 0, 0, 0, 0, 0xa5]⟩ }

private def initial (first second third fourth : UInt8) : Store Unit :=
  { funcs := [callee], mems := [input 0 0 0 0, input first second third fourth] }

example : sourceFunction? original 434 = some reader :=
  originalGetVarintFunction.trans rfl

private theorem check (P : Profile) (host : HostSemantics Unit) (first second third fourth : UInt8)
    (continues : 128 ≤ first.toNat) (continuesAgain : 128 ≤ second.toNat)
    (continuesThird : 128 ≤ third.toNat) (ends : fourth.toNat < 128) :
    let value := ((first.toNat % 128 * 128 + second.toNat % 128) * 128 + third.toNat % 128) * 128 + fourth.toNat
    let bytes := Memory.writeSlice (input first second third fourth).bytes 2 (Memory.encodeLE 8 value)
    Varint.read? (File.View.ofBytes ⟨(input first second third fourth).bytes⟩) 4 =
        some (UInt64.ofNat value, 8) ∧
    Steps P host
      ⟨initial first second third fourth, caller, vals [.i32 4, .i32 2] ++ [.plain (.call ⟨434⟩)]⟩
      ⟨(initial first second third fourth).setMem 1
        { input first second third fourth with bytes := bytes }, caller, [constI32 4]⟩ := by
  exact getVarint_fourByte (s := initial first second third fourth) (caller := caller) (fn := reader)
    (instanceAddr := 0) (fi := callee) (src := 4) (dst := 2) (first := first) (second := second) (third := third) (fourth := fourth)
    (memoryAddr := 1) (mem := input first second third fourth)
    rfl rfl rfl rfl (Expand.iff.mpr rfl) rfl rfl rfl rfl rfl continues continuesAgain continuesThird ends (by change 10 ≤ 11; decide)


example (P : Profile) (host : HostSemantics Unit) :
    Steps P host ⟨initial 0x80 0x80 0x80 0, caller, vals [.i32 4, .i32 2] ++ [.plain (.call ⟨434⟩)]⟩
      ⟨(initial 0x80 0x80 0x80 0).setMem 1 (output 0 0 0 0), caller, [constI32 4]⟩ :=
  (check P host 0x80 0x80 0x80 0 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)).2

example (P : Profile) (host : HostSemantics Unit) :
    Steps P host ⟨initial 0x81 0x80 0x80 0, caller, vals [.i32 4, .i32 2] ++ [.plain (.call ⟨434⟩)]⟩
      ⟨(initial 0x81 0x80 0x80 0).setMem 1 (output 0 0 0x20 0), caller, [constI32 4]⟩ :=
  (check P host 0x81 0x80 0x80 0 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)).2

example (P : Profile) (host : HostSemantics Unit) :
    Steps P host ⟨initial 0xff 0xff 0xff 0x7f, caller, vals [.i32 4, .i32 2] ++ [.plain (.call ⟨434⟩)]⟩
      ⟨(initial 0xff 0xff 0xff 0x7f).setMem 1 (output 0xff 0xff 0xff 0x0f), caller, [constI32 4]⟩ :=
  (check P host 0xff 0xff 0xff 0x7f (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)).2

-- Run the actual slot-434 call, with the high continuation bits set and the source inside the output.
example :
    runIK neverFail 128
      ⟨initial 0xff 0xff 0xff 0x7f, caller, vals [.i32 4, .i32 2] ++ [.plain (.call ⟨434⟩)]⟩ =
      (⟨(initial 0xff 0xff 0xff 0x7f).setMem 1 (output 0xff 0xff 0xff 0x0f),
        caller, [constI32 4]⟩, true) := by
  kernel_rfl

private def shortMemory : MemInst :=
  { input 0 0 0 0 with bytes := ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0x80, 0x80, 0x80]⟩ }
private def shortStore : Store Unit := { funcs := [callee], mems := [input 0 0 0 0, shortMemory] }

-- The destination fits. The input has three continuation bytes and no terminal byte.
example : shortMemory.bytes[11]? = none ∧ 2 + 8 ≤ shortMemory.bytes.size ∧
    Varint.read? (File.View.ofBytes ⟨shortMemory.bytes⟩) 8 = none :=
  ⟨rfl, by decide +kernel, by kernel_rfl⟩

example :
    runIK neverFail 128 ⟨shortStore, caller, vals [.i32 8, .i32 2] ++ [.plain (.call ⟨434⟩)]⟩ =
      (⟨shortStore, caller, [.trap]⟩, true) := by
  kernel_rfl

end SqliteWasm

module

import SqliteWasm.GetVarintOneByte
import SqliteWasm.GetVarintTwoByte
import SqliteWasm.GetVarintThreeByte
import SqliteWasm.GetVarintFourByte
import SqliteWasm.GetVarintFiveByte
import SqliteWasm.GetVarintSixByte
import SqliteWasm.GetVarintSevenByte
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

private def input (first second third fourth fifth sixth seventh : UInt8) : MemInst :=
  ⟨⟨.i32, ⟨0, none⟩⟩, ⟨#[0x5a, 0x5b, 9, first, second, third, fourth, fifth, sixth, seventh, 0xa5]⟩⟩

private def output (d0 d1 d2 d3 d4 d5 d6 : UInt8) : MemInst :=
  { input 0 0 0 0 0 0 0 with bytes := ⟨#[0x5a, 0x5b, d0, d1, d2, d3, d4, d5, d6, 0, 0xa5]⟩ }

private def initial (first second third fourth fifth sixth seventh : UInt8) : Store Unit :=
  { funcs := [callee], mems := [input 0 0 0 0 0 0 0, input first second third fourth fifth sixth seventh] }

example : sourceFunction? original 434 = some reader :=
  originalGetVarintFunction.trans rfl

-- Check the promoted theorem in an ordinary import at the upper canonical endpoint.
example (P : Profile) (host : HostSemantics Unit) :
    Varint.read? (File.View.ofBytes ⟨(input 0xff 0xff 0xff 0xff 0xff 0xff 0x7f).bytes⟩) 3 =
      some (562949953421311, 10) ∧
    Steps P host
      ⟨initial 0xff 0xff 0xff 0xff 0xff 0xff 0x7f, caller, vals [.i32 3, .i32 2] ++ [.plain (.call ⟨434⟩)]⟩
      ⟨(initial 0xff 0xff 0xff 0xff 0xff 0xff 0x7f).setMem 1 (output 0xff 0xff 0xff 0xff 0xff 0xff 1),
        caller, [constI32 7]⟩ := by
  exact getVarint_sevenByte (s := initial 0xff 0xff 0xff 0xff 0xff 0xff 0x7f)
    (caller := caller) (src := 3) (dst := 2) (instanceAddr := 0) (fi := callee) (fn := reader)
    (first := 0xff) (second := 0xff) (third := 0xff) (fourth := 0xff) (fifth := 0xff)
    (sixth := 0xff) (seventh := 0x7f) (memoryAddr := 1) (mem := input 0xff 0xff 0xff 0xff 0xff 0xff 0x7f)
    rfl rfl rfl rfl (Expand.iff.mpr rfl) rfl rfl rfl rfl rfl rfl rfl rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by change 10 ≤ 11; decide)

-- The input at 3--9 is entirely inside the destination at 2--9.
private def replay (start : Store Unit) (result : MemInst) : Prop :=
  runIK neverFail 160
    ⟨start, caller, vals [.i32 3, .i32 2] ++ [.plain (.call ⟨434⟩)]⟩ =
      (⟨start.setMem 1 result, caller, [constI32 7]⟩, true)

example : replay (initial 0x80 0x80 0x80 0x80 0x80 0x80 0) (output 0 0 0 0 0 0 0) := by
  unfold replay
  kernel_rfl

example : replay (initial 0x81 0x80 0x80 0x80 0x80 0x80 0) (output 0 0 0 0 0 4 0) := by
  unfold replay
  kernel_rfl

example : replay (initial 0xff 0xff 0xff 0xff 0xff 0xff 0x7f) (output 0xff 0xff 0xff 0xff 0xff 0xff 1) := by
  unfold replay
  kernel_rfl

end SqliteWasm

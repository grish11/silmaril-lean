module

import SqliteWasm.GetVarintOneByte
import SqliteWasm.GetVarintTwoByte
import SqliteWasm.GetVarintThreeByte
import SqliteWasm.GetVarintFourByte
import SqliteWasm.GetVarintFiveByte
import SqliteWasm.GetVarintSixByte
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

private def input (first second third fourth fifth sixth : UInt8) : MemInst :=
  ⟨⟨.i32, ⟨0, none⟩⟩, ⟨#[0x5a, 0x5b, 9, 9, first, second, third, fourth, fifth, sixth, 0xa5]⟩⟩

private def output (d0 d1 d2 d3 d4 d5 : UInt8) : MemInst :=
  { input 0 0 0 0 0 0 with bytes := ⟨#[0x5a, 0x5b, d0, d1, d2, d3, d4, d5, 0, 0, 0xa5]⟩ }

private def initial (first second third fourth fifth sixth : UInt8) : Store Unit :=
  { funcs := [callee], mems := [input 0 0 0 0 0 0, input first second third fourth fifth sixth] }

example : sourceFunction? original 434 = some reader :=
  originalGetVarintFunction.trans rfl

private theorem check (P : Profile) (host : HostSemantics Unit) (first second third fourth fifth sixth : UInt8)
    (continues : 128 ≤ first.toNat) (continuesAgain : 128 ≤ second.toNat)
    (continuesThird : 128 ≤ third.toNat) (continuesFourth : 128 ≤ fourth.toNat) (continuesFifth : 128 ≤ fifth.toNat)
    (ends : sixth.toNat < 128) :
    let value := ((((first.toNat % 128 * 128 + second.toNat % 128) * 128 + third.toNat % 128) * 128 +
      fourth.toNat % 128) * 128 + fifth.toNat % 128) * 128 + sixth.toNat
    let bytes := Memory.writeSlice (input first second third fourth fifth sixth).bytes 2 (Memory.encodeLE 8 value)
    Varint.read? (File.View.ofBytes ⟨(input first second third fourth fifth sixth).bytes⟩) 4 =
        some (UInt64.ofNat value, 10) ∧
    Steps P host
      ⟨initial first second third fourth fifth sixth, caller, vals [.i32 4, .i32 2] ++ [.plain (.call ⟨434⟩)]⟩
      ⟨(initial first second third fourth fifth sixth).setMem 1
        { input first second third fourth fifth sixth with bytes := bytes }, caller, [constI32 6]⟩ := by
  exact getVarint_sixByte (s := initial first second third fourth fifth sixth) (caller := caller) (fn := reader)
    (instanceAddr := 0) (fi := callee) (src := 4) (dst := 2)
    (first := first) (second := second) (third := third) (fourth := fourth) (fifth := fifth) (sixth := sixth)
    (memoryAddr := 1) (mem := input first second third fourth fifth sixth)
    rfl rfl rfl rfl (Expand.iff.mpr rfl) rfl rfl rfl rfl rfl rfl rfl
    continues continuesAgain continuesThird continuesFourth continuesFifth ends (by change 10 ≤ 11; decide)

example (P : Profile) (host : HostSemantics Unit) :
    Steps P host ⟨initial 0x80 0x80 0x80 0x80 0x80 0, caller, vals [.i32 4, .i32 2] ++ [.plain (.call ⟨434⟩)]⟩
      ⟨(initial 0x80 0x80 0x80 0x80 0x80 0).setMem 1 (output 0 0 0 0 0 0),
        caller, [constI32 6]⟩ :=
  (check P host 0x80 0x80 0x80 0x80 0x80 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)).2

example (P : Profile) (host : HostSemantics Unit) :
    Steps P host ⟨initial 0x81 0x80 0x80 0x80 0x80 0, caller, vals [.i32 4, .i32 2] ++ [.plain (.call ⟨434⟩)]⟩
      ⟨(initial 0x81 0x80 0x80 0x80 0x80 0).setMem 1 (output 0 0 0 0 0x08 0),
        caller, [constI32 6]⟩ :=
  (check P host 0x81 0x80 0x80 0x80 0x80 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)).2

example (P : Profile) (host : HostSemantics Unit) :
    Steps P host ⟨initial 0xff 0xff 0xff 0xff 0xff 0x7f, caller, vals [.i32 4, .i32 2] ++ [.plain (.call ⟨434⟩)]⟩
      ⟨(initial 0xff 0xff 0xff 0xff 0xff 0x7f).setMem 1 (output 0xff 0xff 0xff 0xff 0xff 0x03),
        caller, [constI32 6]⟩ :=
  (check P host 0xff 0xff 0xff 0xff 0xff 0x7f (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)).2

-- Replay the largest six-byte value through both repeated correction steps.
example :
    runIK neverFail 128
      ⟨initial 0xff 0xff 0xff 0xff 0xff 0x7f, caller,
        vals [.i32 4, .i32 2] ++ [.plain (.call ⟨434⟩)]⟩ =
      (⟨(initial 0xff 0xff 0xff 0xff 0xff 0x7f).setMem 1 (output 0xff 0xff 0xff 0xff 0xff 0x03),
        caller, [constI32 6]⟩, true) := by
  kernel_rfl

end SqliteWasm

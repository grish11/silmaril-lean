module

import Silmaril.Wasm.Institution.Operational.LegacyDivision.V1.Thms
import all Batteries.Data.Except

open CategoryTheory Silmaril.Logic.Operational
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Runtime (Value Frame)
open Silmaril.Wasm.Institution.Operational.LegacyDivision
open Silmaril.Wasm.Institution.Operational.LegacyDivision.V1
open Silmaril.Wasm.SingleThreaded.Det (noHost)

private abbrev f : Frame := ⟨[.int .i32 4], {}⟩
private abbrev cfg (code : List V1.Execution.Admin) : V1.Execution.Config Unit := ⟨{}, f, code⟩
private def host : V1.Execution.HostSemantics Unit := fun _ _ _ _ => False

private abbrev suffix : List V1.Execution.Admin := [scalarSyntax.nop]
private abbrev saved : List Value := [.int .i64 99]
private abbrev context (code : List V1.Execution.Admin) := scalarSyntax.values saved ++ code ++ suffix
private abbrev div32 (x y : BitVec 32) (sign : Signedness) :=
  [scalarSyntax.value (.int .i32 x), scalarSyntax.value (.int .i32 y),
    scalarSyntax.divide .i32 sign]

private theorem normal : Derives (context (div32 (-7) 3 .signed))
    (context [scalarSyntax.value (.int .i32 (-2))]) :=
  derives_context saved (derives_redex (.divide .i32 .signed (-7) 3 (-2) (by decide)))
    (by simp)

private theorem zero : Derives (context (div32 84 0 .unsigned)) (context [.trap]) :=
  derives_context saved (derives_redex
    (.divTrap .i32 .unsigned 84 0 .divideByZero (Numerics.intBinOp_div_zero ..))) (by simp)

private theorem overflow : Derives (div32 (BitVec.intMin 32) (-1) .signed) [.trap] :=
  derives_redex (.divTrap .i32 .signed (BitVec.intMin 32) (-1) .overflow (by decide))

-- Read back a native step that first removes the suffix and keeps the value prefix.
private theorem nativeBubble : V1.Execution.Step host (cfg (context [.trap]))
    (cfg (scalarSyntax.values saved ++ [.trap])) :=
  .context (.pure {} f (.trapTail (.source .nop) [])) saved []

private theorem readBubble :
    Derives (context [.trap]) (scalarSyntax.values saved ++ [.trap]) :=
  (step_readback (derives_admitted zero).2 nativeBubble).1

private theorem lastTrap : Derives (scalarSyntax.values saved ++ [.trap]) [.trap] :=
  derives_redex (.trapValues (.int .i64 99) [] [] (by simp))

example : V1.Execution.Steps host (cfg (context (div32 84 0 .unsigned))) (cfg [.trap]) :=
  (steps_iff (derives_admitted zero).1).mpr
    ⟨((Relation.ReflTransGen.single zero).tail readBubble).tail lastTrap, rfl, rfl⟩

example : V1.Execution.Step host (cfg (div32 (BitVec.intMin 32) (-1) .signed)) (cfg [.trap]) :=
  step_sound {} f overflow

example :
    (WasmShape.institution.obj (nativeShape Unit)).Sat
      (Discrete.mk (nativeSystem host).model)
      (encode (cfg (context (div32 (-7) 3 .signed))), (),
        encode (cfg (context [scalarSyntax.value (.int .i32 (-2))]))) :=
  (atom_iff host (derives_admitted normal).1).mpr ⟨normal, rfl, rfl⟩

example : readCode coreEncoding.read (emitCode coreEncoding.emit (context (div32 84 0 .unsigned))) =
    some (context (div32 84 0 .unsigned)) :=
  coreEncoding.code_roundtrip (derives_admitted zero).1

example :
    Execution.Core.Step Numerics.Profile.spec (noHost (H := Unit))
      ⟨{}, {}, emitCode coreEncoding.emit (context (div32 (-7) 3 .signed))⟩
      ⟨{}, {}, emitCode coreEncoding.emit (context [scalarSyntax.value (.int .i32 (-2))])⟩ :=
  coreEncoding.step_to_core Numerics.Profile.spec {} {} normal

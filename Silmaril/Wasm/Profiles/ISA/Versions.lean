module

public import Silmaril.Wasm.Profiles.ISA.Thms
public import Silmaril.Wasm.V1.ToCore.Instructions
public import Silmaril.Wasm.V2.ToCore.Instructions

@[expose] public section

namespace Silmaril.Wasm.Profiles.ISA

open Models

def Op.toV1? {inputs outputs} : Op inputs outputs → Option V1.Instr
  | .bin width op => some (.intBinOp width op.toCore)
  | _ => none

def Op.toV2? {inputs outputs} : Op inputs outputs → Option V2.Instr
  | .bin width op => some (.intBinOp width op.toCore)
  | .extend32S64 => some (.intUnOp .i64 (.extend .i32))
  | .truncSat sign => some (.cvtOp (.int .i32) (.float .f32) (.truncSat sign))
  | .refI31 => none

/-- On this closed set, manifest membership is exact for the translation to
the native 1.0 syntax, and the existing 1.0-to-Core map recovers the instruction. -/
theorem Flat.toV1_core (tag : Flat) : tag.typed.toV1?.map V1.Instr.toCore =
    if tag.use v10 then some tag.erase else none := by cases tag <;> rfl

/-- The corresponding square for native 2.0. This does not assert that an
arbitrary 2.0 instruction has a total Core translation. -/
theorem Flat.toV2_core (tag : Flat) : tag.typed.toV2?.bind V2.Instr.toCore =
    if tag.use v20 then some tag.erase else none := by cases tag <;> rfl

end Silmaril.Wasm.Profiles.ISA

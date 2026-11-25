module

public import Silmaril.SSA.MLIR.WasmSSA.GC.Thms
public import Silmaril.Wasm.SSA.MLIR.WasmSSA.Thms

/-! The first example checks a concrete Core body, including operand order,
local numbering and reuse. The GC examples exercise both projection outcomes. -/

@[expose] public section

namespace Silmaril.MLIR.WasmSSA.Examples

open Silmaril.Wasm (Instr)
open Silmaril.Wasm.Validation (Context DefType Expand FuncOk)

/-- Given local references to x and y, return x when x - y is zero and
the previously bound difference otherwise. -/
def selectDifference : Func [.i64, .i64] .i64 :=
  .letOp (.localGet .here) <|
  .letOp (.localGet (.there .here)) <|
  .letOp (.binary .sub (.there .here) .here) <|
  .letOp (.eqz .here) <|
  .letOp (.select .here (.there (.there (.there .here))) (.there .here)) <|
  .return_ .here

def expectedBody : List Instr :=
  [.localGet ⟨0⟩, .localSet ⟨2⟩,
   .localGet ⟨1⟩, .localSet ⟨3⟩,
   .localGet ⟨2⟩, .localGet ⟨3⟩, .intBinOp .i64 .sub, .localSet ⟨4⟩,
   .localGet ⟨4⟩, .intTestOp .i64 .eqz, .localSet ⟨5⟩,
   .localGet ⟨2⟩, .localGet ⟨4⟩, .localGet ⟨5⟩, .select (some [.num (.int .i64)]), .localSet ⟨6⟩,
   .localGet ⟨6⟩, .return_]

def expected : Silmaril.Wasm.Func :=
  ⟨⟨0⟩, [.num (.int .i64), .num (.int .i64), .num (.int .i64), .num (.int .i32), .num (.int .i64)],
    expectedBody⟩

def signature : DefType :=
  .defn (.group (.cons (.sub true .nil (Func.coreSignature [.i64, .i64] .i64)) .nil)) 0

def context : Context := { types := [signature] }

theorem selectDifference_lowers : selectDifference.toWasm? context ⟨0⟩ = some expected := rfl

theorem selectDifference_validates : FuncOk context expected signature :=
  selectDifference.toWasm?_funcOk rfl (Expand.iff.mpr rfl) selectDifference_lowers

theorem selectDifference_roundTrip :
    ((GC.project? (GC.embed selectDifference)).bind (fun f => Func.toWasm? f context ⟨0⟩)) =
      some expected := by
  simpa only [GC.project_embed, Option.bind_some] using selectDifference_lowers

def constantBits : Func [] .i32 :=
  .letOp (.const 0xffffffff) <|
  .letOp (.const (t := .i64) 0) <|
  .return_ (.there .here)

theorem constantBits_lowers :
    constantBits.toWasm? {} ⟨0⟩ = some
      ⟨⟨0⟩, [.num (.int .i32), .num (.int .i64)],
        [.intConst .i32 0xffffffff, .localSet ⟨0⟩, .intConst .i64 0, .localSet ⟨1⟩,
          .localGet ⟨0⟩, .return_]⟩ :=
  rfl

def lessThan (t : IntType) (sign : Signedness) : Func [t, t] .i32 :=
  .letOp (.localGet .here) <|
  .letOp (.localGet (.there .here)) <|
  .letOp (.lt sign (.there .here) .here) <|
  .return_ .here

def expectedLessThan (t : Silmaril.Wasm.IntType) (sign : Silmaril.Wasm.Signedness) :
    Silmaril.Wasm.Func :=
  ⟨⟨0⟩, [.num (.int t), .num (.int t), .num (.int .i32)],
    [.localGet ⟨0⟩, .localSet ⟨2⟩, .localGet ⟨1⟩, .localSet ⟨3⟩,
      .localGet ⟨2⟩, .localGet ⟨3⟩, .intRelOp t (.lt sign), .localSet ⟨4⟩,
      .localGet ⟨4⟩, .return_]⟩

theorem lessThanSigned_lowers (t : IntType) :
    (lessThan t .signed).toWasm? {} ⟨0⟩ = some (expectedLessThan t.toWasm .signed) := rfl

theorem lessThanUnsigned_lowers (t : IntType) :
    (lessThan t .unsigned).toWasm? {} ⟨0⟩ = some (expectedLessThan t.toWasm .unsigned) := rfl

/-- Even an unused GC binding with integer result is rejected. -/
def unusedGC : GC.Func [] (.core .i32) :=
  .letOp (.core (.const 17)) <|
  .letOp .refNullI31 <|
  .letOp (.refIsNull .here) <|
  .return_ (.there (.there .here))

theorem unusedGC_rejected : GC.project? (Γ := []) unusedGC = none := by simp [GC.project?, unusedGC]

def i31Use : GC.Func [] (.core .i32) :=
  .letOp (.core (.const 17)) <|
  .letOp (.refI31 .here) <|
  .letOp (.i31GetU .here) <|
  .return_ .here

theorem i31Use_rejected : GC.project? (Γ := []) i31Use = none := by
  simp [GC.project?, i31Use]

end Silmaril.MLIR.WasmSSA.Examples

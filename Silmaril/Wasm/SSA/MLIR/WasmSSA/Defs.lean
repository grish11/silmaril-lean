module

public import Silmaril.SSA.MLIR.WasmSSA.Defs
public import Silmaril.Wasm.Validation.Intrinsic.Defs

/-! # Lowering WasmSSA to WebAssembly Core

Parameters occupy the first local slots. Each SSA binding gets its own
integer local, in instruction order. Operands are read from their slots,
then the operation runs on the operand stack and its result is written to
the binding's slot. The return reads its value and emits Core `return`.
-/

@[expose] public section

namespace Silmaril.MLIR.WasmSSA

open Silmaril.Wasm (Instr LocalIdx TypeIdx)
open Silmaril.Wasm.Validation (CCompType CValType Context InstrType LocalType
  NumericInstrOk ResultOk Ty)
open Silmaril.Wasm.Validation.Intrinsic (Body LocalRef)

def IntType.toWasm : IntType → Silmaril.Wasm.IntType
  | .i32 => .i32
  | .i64 => .i64

def IntType.valType (t : IntType) : Silmaril.Wasm.ValType := .num (.int t.toWasm)

def IntType.closed (t : IntType) : CValType := .num (.int t.toWasm)

def IntType.localType (t : IntType) : LocalType := ⟨.set, t.closed⟩

def BinOp.toWasm : BinOp → Silmaril.Wasm.IntBinOp
  | .add => .add
  | .sub => .sub
  | .mul => .mul
  | .and => .and
  | .or => .or
  | .xor => .xor

theorem IntType.width_toWasm (t : IntType) : t.toWasm.width = t.width := by
  cases t <;> rfl

namespace Lowering

abbrev Slot (C : Context) (t : IntType) := LocalRef C t.localType

abbrev Slots (C : Context) (Γ : List IntType) := {t : IntType} → Ref Γ t → Slot C t

def Slots.cons {C : Context} {Γ : List IntType} {s : IntType}
    (slot : Slot C s) (rest : Slots C Γ) : Slots C (s :: Γ)
  | _, .here => slot
  | _, .there ref => rest ref

theorem numericStack (C : Context) (types : List IntType) :
    ResultOk C.toTypeCtx (types.map IntType.closed) := by
  intro t ht
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp ht
  exact .num (.int i.toWasm)

def thenBody {C : Context} {input middle output : List CValType}
    (first : Body C (.plain input middle)) (rest : Body C (.plain middle output)) :
    Body C (.plain input output) :=
  .seq first (by simp) rest

def frame {C : Context} {input output : List CValType} (stack : List IntType)
    (b : Body C (.plain input output)) :
    Body C (.plain (stack.map IntType.closed ++ input) (stack.map IntType.closed ++ output)) :=
  .frame b (numericStack C stack)

def numeric {C : Context} {i : Instr} {sig : InstrType}
    (atomic : Silmaril.Wasm.Validation.Intrinsic.isAtomic i = true)
    (valid : NumericInstrOk C i sig) : Body C sig :=
  .single (.atom i atomic (.numeric valid))

/-- Dropping the initialization effect is admissible by Core instruction
subtyping. The compiler writes the slot even when the binding is unused. -/
def store {C : Context} {t : IntType} (slot : Slot C t) :
    Body C (.plain [t.closed] []) :=
  .sub (.single (.localSet slot))
    ⟨.cons .num .nil, .nil, by simp⟩
    ⟨numericStack C [t], numericStack C [], by simp⟩

def lowerOp {C : Context} {params Γ : List IntType}
    (paramsAt : Slots C params) (valsAt : Slots C Γ) {t : IntType} :
    Rhs params Γ t → Body C (.plain [] [t.closed])
  | .const bits =>
      numeric rfl (.intConst t.toWasm (t.width_toWasm.symm ▸ bits))
  | .localGet param => .single (.localGet (paramsAt param))
  | .binary op lhs rhs =>
      thenBody (.single (.localGet (valsAt lhs))) <|
        thenBody (frame [t] (.single (.localGet (valsAt rhs)))) <|
          numeric rfl (.intBinOp t.toWasm op.toWasm)
  | .eqz (t := inputType) input =>
      thenBody (.single (.localGet (valsAt input))) <| numeric rfl (.intTestOp inputType.toWasm .eqz)
  | .select condition ifTrue ifFalse =>
      thenBody (.single (.localGet (valsAt ifTrue))) <|
        thenBody (frame [t] (.single (.localGet (valsAt ifFalse)))) <|
          thenBody (frame [t, t] (.single (.localGet (valsAt condition)))) <|
            .single (.atom (.select (some [t.valType])) rfl
              (.parametric (.selectExpl (.num (.int t.toWasm)))))

def lowerBlock {C : Context} {params Γ : List IntType} {result : IntType}
    (b : Block params result Γ) (paramsAt : Slots C params) (valsAt : Slots C Γ)
    (next : Nat) (layout : C.locals.drop next = b.bindingTypes.map IntType.localType)
    (fits : C.locals.length ≤ 2 ^ 32) (returns : C.return_ = some [result.closed]) :
    Body C (.plain [] [result.closed]) :=
  match b with
  | .return_ value =>
      thenBody (.single (.localGet (valsAt value)))
        (.single (.return_ (stackPrefix := []) returns
          ⟨numericStack C [], numericStack C [result], by simp⟩))
  | .letOp (t := t) rhs rest =>
      have resolves : C.locals[next]? = some t.localType := by
        have first := congrArg (fun slots : List LocalType => slots[0]?) layout
        simpa [Block.bindingTypes] using first
      have existsSlot := (List.getElem?_eq_some_iff.mp resolves).choose
      let slot : Slot C t := ⟨⟨⟨next, Nat.lt_of_lt_of_le existsSlot fits⟩⟩, resolves⟩
      have restLayout : C.locals.drop (next + 1) = rest.bindingTypes.map IntType.localType := by
        rw [← List.drop_drop, layout]
        rfl
      thenBody (lowerOp paramsAt valsAt rhs) <| thenBody (store slot) <|
        lowerBlock rest paramsAt (Slots.cons slot valsAt) (next + 1) restLayout fits returns

end Lowering

/-- The local index resource bound for the lowering, including parameters. -/
abbrev Func.Fits {params : List IntType} {result : IntType} (f : Func params result) : Prop :=
  params.length + f.bindingTypes.length ≤ 2 ^ 32

/-- Closed parameter types, for use with the Core validator. -/
def Func.paramTypes (params : List IntType) : List CValType := params.map IntType.closed

/-- The composite type expected at the lowered function's type index. -/
def Func.coreSignature (params : List IntType) (result : IntType) : CCompType :=
  Ty.funcOf (Func.paramTypes params) [result.closed]

def Func.bodyContext {params : List IntType} {result : IntType} (f : Func params result)
    (C : Context) : Context :=
  C.funcBody (Func.paramTypes params) [result.closed] (f.bindingTypes.map IntType.localType)

/-- Translate into the existing intrinsically typed Core instruction sequence. -/
def Func.toBody {params : List IntType} {result : IntType} (f : Func params result)
    (C : Context) (fits : f.Fits) : Body (f.bodyContext C) (.plain [] [result.closed]) := by
  let ctx := f.bodyContext C
  have layout : ctx.locals = params.map IntType.localType ++ f.bindingTypes.map IntType.localType := by
    simp [ctx, Func.bodyContext, Func.paramTypes, Context.funcBody, Function.comp_def, IntType.localType]
  have bound : ctx.locals.length ≤ 2 ^ 32 := by simpa [layout] using fits
  let paramSlot : Lowering.Slots ctx params := fun {t} ref =>
    have hIndex : ref.index < params.length := (List.getElem?_eq_some_iff.mp ref.getElem?_index).choose
    let idx : LocalIdx := ⟨⟨ref.index, by
      have : ref.index < params.length + f.bindingTypes.length :=
        Nat.lt_of_lt_of_le hIndex (Nat.le_add_right _ _)
      exact Nat.lt_of_lt_of_le this fits⟩⟩
    ⟨idx, by
      change ctx.locals[ref.index]? = some t.localType
      rw [layout, List.getElem?_append_left (by simpa using hIndex)]
      simp⟩
  have remaining : ctx.locals.drop params.length = f.bindingTypes.map IntType.localType := by
    rw [layout, List.drop_left' (List.length_map IntType.localType)]
  exact Lowering.lowerBlock f paramSlot (fun ref => nomatch ref) params.length remaining bound rfl

/-- Erase the Core typing witness to obtain an ordinary function definition.
The caller supplies the Core type index. -/
def Func.toWasm {params : List IntType} {result : IntType} (f : Func params result)
    (C : Context) (type : TypeIdx) (fits : f.Fits) : Silmaril.Wasm.Func :=
  ⟨type, f.bindingTypes.map IntType.valType, (f.toBody C fits).erase⟩

/-- Refuse local layouts that exceed the Core local index space. -/
def Func.toWasm? {params : List IntType} {result : IntType} (f : Func params result)
    (C : Context) (type : TypeIdx) : Option Silmaril.Wasm.Func :=
  if fits : f.Fits then some (f.toWasm C type fits) else none

end Silmaril.MLIR.WasmSSA

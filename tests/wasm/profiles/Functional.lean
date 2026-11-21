module

import Silmaril.Wasm.Profiles.Functional.Thms
import Silmaril.Wasm.Profiles.Thms
import Silmaril.Wasm.Validation.Check.Validate

open Silmaril.Wasm Silmaril.Wasm.Validation
open Silmaril.Wasm.Models
open Silmaril.Wasm.Profiles (FunctionalCore GCMode ExceptionMode CheckedModule Wasm1 Wasm2 Wasm3 Lime FX)
open Silmaril.Wasm.Profiles.FunctionalISA

private def accepts (gc : GCMode) (exceptions : ExceptionMode) (mod : Module) : Bool :=
  (FunctionalCore.check? gc exceptions mod).isSome

private def funcType (params results : List ValType) : RecType := ⟨[⟨true, [], .func ⟨params, results⟩⟩]⟩

private def mutatePair : Module :=
  { types := [⟨[⟨true, [], .struct [⟨.var, .val .i32⟩, ⟨.const, .val .i32⟩]⟩]⟩, funcType [.i32, .i32] [.i32]]
    funcs := [⟨⟨1⟩, [], [.block (.value .i32) [
        .localGet ⟨0⟩, .localGet ⟨1⟩, .structNew ⟨0⟩, .intConst .i32 42, .structSet ⟨0⟩ ⟨0⟩, .intConst .i32 42]]⟩]
    exports := [⟨"update", .func ⟨0⟩⟩] }

example : (validate? mutatePair).isSome = true := by decide +kernel
example : accepts .mutable .disabled mutatePair = true := by decide +kernel
example : accepts .immutable .internal mutatePair = false := by decide +kernel

private def writeModule := (FunctionalCore.check? .mutable .disabled mutatePair).get (by decide +kernel)
private def writeIface := (validate? mutatePair).get (by decide +kernel)
private def checkedWrite : CheckedModule (FunctionalCore .mutable .disabled) writeIface :=
  ⟨writeModule, validate?_sound (by rfl)⟩
example : (FunctionalCore.checkedToCore writeIface checkedWrite).val = mutatePair := rfl

example : Instr.insInFeatB (FunctionalCore.features .immutable .internal)
    [.block .empty [.structSet ⟨0⟩ ⟨0⟩]] = false := by decide +kernel

private def catchInternal : Module :=
  { types := [funcType [] [], funcType [] [.i32]]
    tags := [⟨0⟩]
    funcs := [⟨⟨1⟩, [], [.block .empty [.tryTable .empty [.catch_ ⟨0⟩ ⟨0⟩] [.throw ⟨0⟩]], .intConst .i32 42]⟩]
    exports := [⟨"caught", .func ⟨0⟩⟩] }

example : (validate? catchInternal).isSome = true := by decide +kernel
example : accepts .immutable .internal catchInternal = true := by decide +kernel
example : accepts .mutable .disabled catchInternal = false := by decide +kernel
example : accepts .immutable .internal { catchInternal with exports := [⟨"tag", .tag ⟨0⟩⟩] } = false := by decide +kernel
example : Instr.insInFeatB (FunctionalCore.features .mutable .disabled)
    [.block .empty [.tryTable .empty [] [.throw ⟨0⟩]]] = false := by decide +kernel

private def capturedAdd : Module :=
  { types := [funcType [.i32, .i32] [.i32], ⟨[⟨true, [], .struct
        [⟨.const, .val .i32⟩, ⟨.const, .val (.ref ⟨true, .typeIdx ⟨0⟩⟩)⟩]⟩]⟩]
    funcs := [⟨⟨0⟩, [], [.localGet ⟨0⟩, .localGet ⟨1⟩, .intBinOp .i32 .add]⟩,
      ⟨⟨0⟩, [.ref ⟨true, .typeIdx ⟨1⟩⟩],
        [.localGet ⟨0⟩, .refFunc ⟨0⟩, .structNew ⟨1⟩, .localSet ⟨2⟩,
         .localGet ⟨2⟩, .structGet none ⟨1⟩ ⟨0⟩, .localGet ⟨1⟩, .localGet ⟨2⟩,
         .structGet none ⟨1⟩ ⟨1⟩, .callRef ⟨0⟩]⟩]
    exports := [⟨"code", .func ⟨0⟩⟩, ⟨"captureAndApply", .func ⟨1⟩⟩] }

example : (validate? capturedAdd).isSome = true := by decide +kernel
example : accepts .immutable .disabled capturedAdd = true := by decide +kernel
example : accepts .mutable .internal { capturedAdd with imports := [⟨"host", "f", .func ⟨0⟩⟩] } = false := by decide +kernel
example : accepts .mutable .internal { capturedAdd with memories := [⟨.i32, ⟨1, none⟩⟩] } = false := by decide +kernel

private theorem i32sOk (ctx : Context) (count : Nat) : ResultOk ctx.toTypeCtx (List.replicate count .i32) := by
  intro value mem
  obtain rfl := (List.mem_replicate.mp mem).2
  exact .num (.int .i32)

private def callParams : Ty (.list .val) := .cons .i32 (.cons .i32 .nil)
private def callResults : Ty (.list .val) := .cons .i32 .nil
private def callee : DefType := .defn (.group (.cons (.sub true .nil (.func callParams callResults)) .nil)) 0
private def calleeRef : CValType := .refT true (.defHeap callee)
private def captureFields : Ty (.list .field) :=
  .cons (.field .const (.val .i32)) (.cons (.field .const (.val calleeRef)) .nil)
private def closure : DefType := .defn (.group (.cons (.sub true .nil (.struct captureFields)) .nil)) 0
private def closureCtx : Context :=
  { types := [callee, closure], funcs := [callee, callee], refs := [0, 1]
    locals := [⟨.set, .i32⟩, ⟨.set, .i32⟩, ⟨.set, .refT true (.defHeap closure)⟩] }

private def functionPointer : TypedAtom closureCtx .immutable [] [.refT false (.defHeap callee)] :=
  .refFunc ⟨0⟩ rfl (by simp [closureCtx, Idx.toNat])

example : InstrOk closureCtx (.refFunc ⟨0⟩) (.plain [] [.refT false (.defHeap callee)]) :=
  functionPointer.sound

private def allocateClosure : Code .immutable closureCtx [.i32, calleeRef] [.refT false (.defHeap closure)] :=
  .cons (base := []) (i32sOk _ 0) (.structNew (fs := captureFields) ⟨1⟩ rfl (.mk rfl))
    (.done (ResultOk.check_sound (by decide +kernel)))

private def captureClosure : Code .immutable closureCtx [] [.refT false (.defHeap closure)] :=
  .cons (base := []) (i32sOk _ 0) (.localGet ⟨0⟩ rfl) <|
  .cons (base := [.i32]) (i32sOk _ 1) functionPointer <|
  .sub allocateClosure (InstrTypeSub.check_sound (by decide +kernel))
    (InstrTypeOk.check_sound (by decide +kernel))

private def applyClosure : Code .immutable closureCtx [] [.i32] :=
  .cons (base := []) (i32sOk _ 0) (.localGet ⟨2⟩ rfl) <|
  .cons (base := []) (i32sOk _ 0)
    (.structGet (fs := captureFields) none ⟨1⟩ ⟨0⟩ rfl (.mk rfl) rfl rfl) <|
  .cons (base := [.i32]) (i32sOk _ 1) (.localGet ⟨1⟩ rfl) <|
  .cons (base := [.i32, .i32]) (i32sOk _ 2) (.localGet ⟨2⟩ rfl) <|
  .cons (base := [.i32, .i32]) (i32sOk _ 2)
    (.structGet (fs := captureFields) none ⟨1⟩ ⟨1⟩ rfl (.mk rfl) rfl rfl) <|
  .cons (base := []) (i32sOk _ 0)
    (.callRef (params := callParams) (results := callResults) ⟨0⟩ rfl (.mk rfl)) (.done (i32sOk _ 1))

private def rawClosureBody : Expr := (capturedAdd.funcs[1]'(by decide)).body

example : captureClosure.erase ++ [.localSet ⟨2⟩] ++ applyClosure.erase = rawClosureBody := rfl
example : ExprOk closureCtx captureClosure.erase [.refT false (.defHeap closure)] := captureClosure.sound
example : ExprOk closureCtx applyClosure.erase [.i32] := applyClosure.sound
example : exprC closureCtx captureClosure.erase [.refT false (.defHeap closure)] = true := by decide +kernel
example : exprC closureCtx applyClosure.erase [.i32] = true := by decide +kernel
example : Instr.insInFeatB (FunctionalCore.features .immutable .disabled) applyClosure.erase = true :=
  applyClosure.features .disabled
example : exprC { closureCtx with refs := [] } [functionPointer.toRaw.erase] [.refT false (.defHeap callee)] = false :=
  by decide +kernel
example : exprC { closureCtx with types := [closure, closure] } applyClosure.erase [.i32] = false :=
  by decide +kernel

private def branchBody : Code .immutable {} [] [.i32] :=
  .blockI32 (base := []) (i32sOk _ 0)
    (.cons (base := []) (i32sOk _ 0) (.intConst 28)
      (.cons (base := [.i32]) (i32sOk _ 1) (.intConst 14)
        (.cons (base := []) (i32sOk _ 0) (.bin .i32 .add)
          (.cons (base := [.i32]) (i32sOk _ 1) (.intConst 1)
            (.cons (base := []) (i32sOk _ 0) (.brIf0 rfl) (.done (i32sOk _ 1)))))))
    (.done (i32sOk _ 1))

example : branchBody.erase = [.block (.value .i32)
    [.intConst .i32 28, .intConst .i32 14, .intBinOp .i32 .add, .intConst .i32 1, .brIf ⟨0⟩]] := rfl
example : ExprOk {} branchBody.toRaw.allowWrites.erase [.i32] := by
  rw [Raw.allowWrites_erase]
  exact branchBody.sound
example : ∃ body : Intrinsic.Body {} (.plain [] [.i32]), body.erase = branchBody.erase := branchBody.liftCore

private def fields : Ty (.list .field) := .cons (.field .var (.val .i32)) .nil
private def cell : DefType := .defn (.group (.cons (.sub true .nil (.struct fields)) .nil)) 0
private def cellCtx : Context := { types := [cell] }
private def setter : TypedAtom cellCtx .mutable [.refT true (.defHeap cell), .i32] [] :=
  .structSet (defType := cell) (fs := fields) (storage := .val .i32) ⟨0⟩ ⟨0⟩ rfl (.mk rfl) rfl
example : InstrOk cellCtx (.structSet ⟨0⟩ ⟨0⟩) (.plain [.refT true (.defHeap cell), .i32] []) := setter.sound
example : ∀ atom : Atom .immutable, atom.erase ≠ .structSet ⟨0⟩ ⟨0⟩ := by
  intro atom
  cases atom <;> simp [Atom.erase]

example : Profiles.Value Wasm1 = NumType := rfl
example : Profiles.Value Lime = NumType := rfl
example : Profiles.Value Wasm2 = V2.ValType := rfl
example : Profiles.Value Wasm3 = ValType := rfl
example : Profiles.Instruction Wasm1 = V1.Instr := rfl
example : Profiles.Instruction Wasm2 = V2.Instr := rfl
example : Profiles.Instruction Lime = Lime1.Instr := rfl
example : Profiles.Instruction FX = Models.FX.InstrFX := rfl

#print axioms FunctionalCore.inclusion_square
#print axioms FunctionalCore.checkedToCore
#print axioms FunctionalCore.resources_empty
#print axioms FunctionalCore.exports_function
#print axioms FunctionalCore.tags_empty
#print axioms Code.sound
#print axioms captureClosure
#print axioms applyClosure
#print axioms Code.liftCore
#print axioms Raw.features
#print axioms Raw.allowWrites_erase

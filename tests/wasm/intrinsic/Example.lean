module

public import Silmaril.Wasm.Validation.Intrinsic.Thms
public import Silmaril.Wasm.Validation.Intrinsic.Quote
public import Silmaril.Wasm.Validation.Check.Validate

@[expose] public section

namespace WasmIntrinsicExample

open Silmaril Silmaril.Wasm Silmaril.Wasm.Validation

def zero {kind : IndexKind} : Idx kind := ⟨0⟩

def signature : RecType := ⟨[⟨true, [], .func ⟨[.i32], [.i32]⟩⟩]⟩
def closed : DefType := (Context.rollGroup {} signature)[0]'(by decide +kernel)
def incoming : Wasm.Import := ⟨"host", "transform", .func zero⟩
def signatureStack : Ty (.list .val) := .cons .i32 .nil
def metadata : Wasm.Module := { types := [signature], imports := [incoming] }
def ctx : Context := { types := [closed], funcs := [closed, closed] }
def bodyCtx : Context := ctx.funcBody [.i32] [.i32] []
def labelCtx : Context := bodyCtx.withLabel [.i32]
theorem closedExpands : Expand closed (.func signatureStack signatureStack) :=
  Expand.iff.mpr rfl

def code : Intrinsic.Body bodyCtx (.plain [] [.i32]) :=
  .single (.block (.value .i32) (.value (TyOk.check_sound (by decide +kernel)))
    (.seq (Intrinsic.Body.single (Intrinsic.Step.localGet
        (context := labelCtx) (type := .i32) ⟨zero, rfl⟩)) (by simp)
      (.single (.call ⟨closed, ⟨zero, rfl⟩, closedExpands⟩))))

def func : Intrinsic.Function ctx closed :=
  ⟨zero, rfl, signatureStack, signatureStack, closedExpands, [], [], .nil, code⟩

def interface : CModuleType := ⟨[.func closed], []⟩

wasm_intrinsic intrinsic : interface := {
  metadata := metadata
  noRawFunctions := rfl
  definedTypes := [closed]
  definedTags := []
  definedGlobals := []
  definedTables := []
  definedFuncs := [closed]
  elementTypes := []
  baseContext := ctx
  context := ctx
  typesValid := typesCheck?_sound (fun _ _ _ valid => RecTypeOkAt.check_sound valid) (by decide +kernel)
  importsValid := .cons (importCheck?_sound tyOkC_sound' rfl) .nil
  baseContextEq := rfl
  contextEq := rfl
  tagsValid := .nil
  globalsValid := .nil
  memoriesValid := by simp [metadata]
  tablesValid := .nil
  funcs := .cons func .nil
  dataValid := by simp [metadata]
  elemsValid := .nil
  startValid := by simp [metadata]
  exportsValid := .nil
  exportsDisjoint := .nil }

end WasmIntrinsicExample

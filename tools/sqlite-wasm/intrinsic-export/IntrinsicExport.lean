module

public import SqliteWasm.InitializerFlag
public import SqliteWasm.ValidationInputs
public import Silmaril.Wasm.Validation.Intrinsic.Thms

public section

namespace SqliteWasm

open Silmaril.Wasm Silmaril.Wasm.Validation
open Silmaril.Wasm.Validation.Intrinsic (Body FunctionRef)
open SqliteWasmArtifact (definedFunction?)

set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

private def thenBody {C : Context} {input mid output : List CValType}
    (head : Body C (.plain input mid)) (rest : Body C (.plain mid output)) :
    Body C (.plain input output) :=
  .seq (firstInits := []) (restInits := []) head (by simp) rest

private def i32Const (C : Context) (value : BitVec 32) : Body C (.plain [] [.i32]) :=
  .single (.atom (.intConst .i32 value) rfl (.numeric (.intConst .i32 value)))

private def initializerAddressBody (C : Context) (global : C.globals[1]? = some ⟨.const, .i32⟩) :
    Body C (.plain [] [.i32]) :=
  thenBody (.single (.atom (.globalGet ⟨1⟩) rfl (.variable (.globalGet global))))
    (thenBody (.frame (stackPrefix := [.i32]) (i32Const C 59328) (.check_sound rfl))
      (.single (.atom (.intBinOp .i32 .add) rfl (.numeric (.intBinOp .i32 .add)))))

private def initializerGuardBody (C : Context)
    (global : C.globals[1]? = some ⟨.const, .i32⟩)
    {limits : Limits} (memory : C.mems[0]? = some ⟨.i32, limits⟩) :
    Body C (.plain [] []) :=
  .single (.block .empty .empty
    (thenBody (initializerAddressBody (C.withLabel []) global)
      (thenBody (.single (.atom (.intLoad .i32 none ⟨0⟩ ⟨2, 0⟩) rfl
        (.memory (.intLoad (a := .i32) memory (by decide)))))
        (thenBody (.single (.atom (.intTestOp .i32 .eqz) rfl (.numeric (.intTestOp .i32 .eqz))))
          (thenBody (.single (.brIf (target := []) ⟨⟨0⟩, rfl⟩))
            (.single (.unreachable (.check_sound rfl))))))))

private def initializerWriteBody (C : Context)
    (global : C.globals[1]? = some ⟨.const, .i32⟩)
    {limits : Limits} (memory : C.mems[0]? = some ⟨.i32, limits⟩) :
    Body C (.plain [] []) :=
  thenBody (initializerAddressBody C global)
    (thenBody (.frame (stackPrefix := [.i32]) (i32Const C 1) (.check_sound rfl))
      (.single (.atom (.intStore .i32 none ⟨0⟩ ⟨2, 0⟩) rfl
        (.memory (.intStore (a := .i32) memory (by decide))))))

private def initializerCode (C : Context)
    (global : C.globals[1]? = some ⟨.const, .i32⟩)
    {limits : Limits} (memory : C.mems[0]? = some ⟨.i32, limits⟩)
    (setup finish : FunctionRef C .nil .nil) : Body C (.plain [] []) :=
  thenBody (initializerGuardBody C global memory)
    (thenBody (initializerWriteBody C global memory)
      (thenBody (.single (.call setup)) (.single (.call finish))))

sqlite_check_eq initializerValidationInputsExist :
    (bodyInputs? sqlite).isSome = true

def initializerValidationInputs : BodyInputs :=
  (bodyInputs? sqlite).get initializerValidationInputsExist

private abbrev bodyContext := initializerValidationInputs.context.funcBody [] [] []

def typedInitializerSignature : DefType :=
  (initializerValidationInputs.context.type? initializerFunction.type).get rfl

private def setupSignature : DefType :=
  (initializerValidationInputs.context.funcs[1516]?).get rfl

private def finishSignature : DefType :=
  (initializerValidationInputs.context.funcs[23]?).get rfl

def typedInitializer : Validation.Intrinsic.Function initializerValidationInputs.context typedInitializerSignature where
  typeIndex := initializerFunction.type
  resolves := rfl
  params := .nil
  results := .nil
  expands := Expand.iff.mpr rfl
  locals := []
  localTypes := []
  localValid := .nil
  body := initializerCode bodyContext rfl (limits := ⟨2, none⟩) rfl
    ⟨setupSignature, ⟨⟨1516⟩, rfl⟩, Expand.iff.mpr rfl⟩
    ⟨finishSignature, ⟨⟨23⟩, rfl⟩, Expand.iff.mpr rfl⟩

private theorem typedInitializerErasesExact : typedInitializer.erase = initializerFunction := rfl

theorem typedInitializerErases : typedInitializer.erase = initializerFunction :=
  typedInitializerErasesExact

private theorem initializerValidationInputsExact :
    bodyInputs? sqlite = some initializerValidationInputs := rfl

theorem originalInitializerContext :
    bodyInputs? sqlite = some initializerValidationInputs :=
  initializerValidationInputsExact

private theorem initializerSignatureAtOrdinalExact :
    initializerValidationInputs.signatures[2]? = some typedInitializerSignature := rfl

theorem initializerSignatureAtOrdinal :
    initializerValidationInputs.signatures[2]? = some typedInitializerSignature :=
  initializerSignatureAtOrdinalExact

theorem originalIntrinsicInitializer :
    ((Binary.Core.decode? originalBytes.toByteArray).bind fun m => definedFunction? m 25) =
      some typedInitializer.erase := by
  rw [typedInitializerErases, originalInitializerFunction]

theorem originalInitializerTyped :
    FuncOk initializerValidationInputs.context initializerFunction typedInitializerSignature :=
  typedInitializerErases ▸ typedInitializer.sound

#print axioms typedInitializerErases
#print axioms originalIntrinsicInitializer
#print axioms originalInitializerTyped

end SqliteWasm

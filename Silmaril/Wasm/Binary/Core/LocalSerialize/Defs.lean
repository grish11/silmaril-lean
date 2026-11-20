module

public import Silmaril.Wasm.Binary.Core.Decode
public import Silmaril.Wasm.Tools.Meta.Leb.Defs
public import Silmaril.Wasm.Validation.Intrinsic.Defs
public import Silmaril.Wasm.Validation.Check.TyOk

@[expose] public section

namespace Silmaril.Wasm.Binary.Core.LocalSerialize

open Decode Validation
open Silmaril.Wasm.Tools.Meta (encU32)

/-- One exported `[] → [i32]` function, one nonempty homogeneous group of
`i32` locals, one `local.get`. The sole variable reference is a real Core index. -/
def bodyBytes (locals index : Nat) : List UInt8 :=
  [1] ++ encU32 locals ++ [0x7f, 0x20] ++ encU32 index ++ [0x0b]

def codeBytes (locals index : Nat) : List UInt8 :=
  let body := bodyBytes locals index
  [1] ++ encU32 body.length ++ body

structure Fits (locals index : Nat) : Prop where
  localCount : locals < 2 ^ 32
  decoderCap : locals ≤ maxLocals
  resolves : index < locals
  bodySize : (bodyBytes locals index).length < 2 ^ 32
  codeSize : (codeBytes locals index).length < 2 ^ 32

instance {locals index : Nat} : Decidable (Fits locals index) :=
  decidable_of_iff (locals < 2 ^ 32 ∧ locals ≤ maxLocals ∧ index < locals ∧
    (bodyBytes locals index).length < 2 ^ 32 ∧ (codeBytes locals index).length < 2 ^ 32) ⟨
    fun ⟨localCount, decoderCap, resolves, bodySize, codeSize⟩ =>
      ⟨localCount, decoderCap, resolves, bodySize, codeSize⟩,
    fun fits => ⟨fits.localCount, fits.decoderCap, fits.resolves, fits.bodySize, fits.codeSize⟩⟩

structure Shape where
  locals : Nat
  index : Nat
  fits : Fits locals index

def Shape.localIndex (shape : Shape) : LocalIdx :=
  ⟨⟨shape.index, Nat.lt_trans shape.fits.resolves shape.fits.localCount⟩⟩

def signature : Wasm.RecType := ⟨[⟨true, [], .func ⟨[], [.i32]⟩⟩]⟩

def closed : DefType := (Context.rollGroup {} signature)[0]'(by decide +kernel)

def iface : CModuleType := ⟨[], [.func closed]⟩

def exportF : Wasm.Export := ⟨"f", .func ⟨0⟩⟩

def metadata : Wasm.Module := { types := [signature], exports := [exportF] }

def rawFunc (shape : Shape) : Wasm.Func :=
  ⟨⟨0⟩, List.replicate shape.locals .i32, [.localGet shape.localIndex]⟩

def raw (shape : Shape) : Wasm.Module := { metadata with funcs := [rawFunc shape] }

def context : Context := { types := [closed], funcs := [closed], refs := [0] }

def localTypes (count : Nat) : List LocalType := List.replicate count ⟨.set, .i32⟩

theorem localTypes_ok (count : Nat) : List.Forall₂ (LocalOk context)
    (List.replicate count .i32) (localTypes count) := by
  induction count with
  | zero => exact .nil
  | succ count ih => exact .cons (.set (TyOk.check_sound (by decide +kernel)) (by decide +kernel)) ih

def typedFunc (shape : Shape) : Intrinsic.Function context closed where
  typeIndex := ⟨0⟩
  resolves := rfl
  params := .nil
  results := .cons .i32 .nil
  expands := Expand.iff.mpr rfl
  locals := List.replicate shape.locals .i32
  localTypes := localTypes shape.locals
  localValid := localTypes_ok shape.locals
  body := .single (.localGet ⟨shape.localIndex, by
    change (List.replicate shape.locals (⟨.set, .i32⟩ : LocalType))[shape.index]? = some ⟨.set, .i32⟩
    simp [shape.fits.resolves]⟩)

/-- Construct a checked intrinsic function and module, not a raw term with a typing proof. -/
def typed (shape : Shape) : Intrinsic.Module iface where
  metadata := metadata
  noRawFunctions := rfl
  definedTypes := [closed]
  definedTags := []
  definedGlobals := []
  definedTables := []
  definedFuncs := [closed]
  elementTypes := []
  baseContext := context
  context := context
  typesValid := .cons (RecTypeOkAt.check_sound (by decide +kernel)) .nil
  importsValid := .nil
  baseContextEq := rfl
  contextEq := rfl
  tagsValid := .nil
  globalsValid := .nil
  memoriesValid := by simp [metadata]
  tablesValid := .nil
  funcs := .cons (typedFunc shape) .nil
  dataValid := by simp [metadata]
  elemsValid := .nil
  startValid := by simp [metadata]
  exportsValid := .cons (.func rfl) .nil
  exportsDisjoint := by simp [metadata]

def bytesBeforeCode : List UInt8 :=
  magic ++ version ++ [1, 5, 1, 0x60, 0, 1, 0x7f, 3, 2, 1, 0, 7, 5, 1, 1, 0x66, 0, 0]

def encode (shape : Shape) : ByteArray :=
  let code := codeBytes shape.locals shape.index
  (bytesBeforeCode ++ [10] ++ encU32 code.length ++ code).toByteArray

def Serializable (mod : Wasm.Module) : Prop := ∃ shape : Shape, raw shape = mod

abbrev RawModule := { mod : { mod : Wasm.Module // ModuleOk mod iface } // Serializable mod.val }
abbrev IntrinsicModule := { mod : Intrinsic.Module iface // Serializable mod.erase }

def extract (mod : Wasm.Module) (fits : Serializable mod) : Shape :=
  let fn := mod.funcs.headD ⟨⟨0⟩, [], []⟩
  let index := match fn.body with
    | [.localGet index] => index.toNat
    | _ => 0
  ⟨fn.locals.length, index, by
    obtain ⟨shape, rfl⟩ := fits
    simpa [fn, index, raw, rawFunc, Shape.localIndex, Idx.toNat] using shape.fits⟩

def RawModule.encode (mod : RawModule) : ByteArray := LocalSerialize.encode (extract mod.val.val mod.property)

def IntrinsicModule.encode (mod : IntrinsicModule) : ByteArray :=
  LocalSerialize.encode (extract mod.val.erase mod.property)

def IntrinsicModule.ofShape (shape : Shape) : IntrinsicModule := ⟨typed shape, ⟨shape, rfl⟩⟩

/-- Recognize this exact AST profile after decoding. No claim about the source's byte layout. -/
def accept? : (mod : Wasm.Module) → Option { shape : Shape // raw shape = mod }
  | ⟨types, [], [], [], [], [], [⟨typeIndex, locals, [.localGet index]⟩], [], [], none, exports⟩ =>
    if fits : Fits locals.length index.toNat then
      if profile : types = [signature] ∧ typeIndex = ⟨0⟩ ∧ exports = [exportF] ∧
          List.replicate locals.length Wasm.ValType.i32 = locals then
        some ⟨⟨locals.length, index.toNat, fits⟩, by
          obtain ⟨rfl, rfl, rfl, localsMatch⟩ := profile
          have indexMatch : (Shape.mk locals.length index.toNat fits).localIndex = index := by
            cases index
            exact congrArg Idx.mk (Fin.ext rfl)
          simp only [raw, rawFunc, metadata, indexMatch, localsMatch]⟩
      else none
    else none
  | _ => none

def decodeShape? (bytes : ByteArray) : Option Shape := do
  let mod ← Core.decode? bytes
  return (← accept? mod).val

def decodeIntrinsic? (bytes : ByteArray) : Option IntrinsicModule :=
  (decodeShape? bytes).map IntrinsicModule.ofShape

end Silmaril.Wasm.Binary.Core.LocalSerialize

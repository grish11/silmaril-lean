module

public import Silmaril.Wasm.Binary.Core.Decode
public import Silmaril.Wasm.Tools.Meta.Leb.Defs
public import Silmaril.Wasm.Validation.Intrinsic.Defs

@[expose] public section

namespace Silmaril.Wasm.Binary.Core.PassiveSerialize

open Validation
open Silmaril.Wasm.Tools.Meta (encU32)

def sectionSize (length : Nat) : Nat := 2 + (encU32 length).length + length

/-- The only variable vector length is the payload. The count/mode are both one.
The section body includes the count, mode, length encoding and the payload. -/
structure Fits (length : Nat) : Prop where
  payload : length < 2 ^ 32
  body : sectionSize length < 2 ^ 32

abbrev Payload := { bytes : ByteArray // Fits bytes.size }

def sections (bytes : ByteArray) : Wasm.ModuleSections := { data := [⟨bytes, .passive⟩] }

def raw (bytes : ByteArray) : Wasm.Module := (sections bytes).assemble []

def iface : CModuleType := ⟨[], []⟩

def typed (bytes : ByteArray) : Intrinsic.Module iface where
  sections := sections bytes
  definedTypes := []
  definedTags := []
  definedGlobals := []
  definedTables := []
  definedFuncs := []
  elementTypes := []
  baseContext := {}
  context := { datas := [()] }
  typesValid := .nil
  importsValid := .nil
  baseContextEq := rfl
  contextEq := rfl
  tagsValid := .nil
  globalsValid := .nil
  memoriesValid := by simp [sections]
  tablesValid := .nil
  funcs := .nil
  dataValid := by
    intro data_ member
    have eq := List.mem_singleton.mp member
    subst data_
    exact .passive
  elemsValid := .nil
  startValid := by simp [sections]
  exportsValid := .nil
  exportsDisjoint := .nil

def serializable (mod : Wasm.Module) : Prop := ∃ payload : Payload, mod = raw payload.val

abbrev RawModule := { mod : { mod : Wasm.Module // ModuleOk mod iface } // serializable mod.val }

abbrev IntrinsicModule := { mod : Intrinsic.Module iface // serializable mod.erase }

def extract (mod : Wasm.Module) (fits : serializable mod) : Payload :=
  ⟨(mod.data.headD ⟨ByteArray.empty, .passive⟩).bytes, by
    obtain ⟨payload, rfl⟩ := fits
    exact payload.property⟩

def encode (payload : Payload) : ByteArray :=
  ((magic ++ version) ++ ([11] ++ (encU32 (sectionSize payload.val.size) ++ ([1] ++ ([1] ++
    (encU32 payload.val.size ++ payload.val.data.toList)))))).toByteArray

def RawModule.encode (mod : RawModule) : ByteArray := PassiveSerialize.encode (extract mod.val.val mod.property)

def IntrinsicModule.encode (mod : IntrinsicModule) : ByteArray :=
  PassiveSerialize.encode (extract mod.val.erase mod.property)

/-- Recognize the representable AST after the ordinary Core decoder has run. -/
def accept? : (mod : Wasm.Module) → Option { payload : Payload // raw payload.val = mod }
  | ⟨[], [], [], [], [], [], [], [⟨bytes, .passive⟩], [], none, []⟩ =>
    if guard : bytes.size < 2 ^ 32 ∧ sectionSize bytes.size < 2 ^ 32 then
      some ⟨⟨bytes, ⟨guard.1, guard.2⟩⟩, rfl⟩
    else none
  | _ => none

def decodePayload? (bytes : ByteArray) : Option Payload := do
  let mod ← Core.decode? bytes
  let accepted ← accept? mod
  pure accepted.val

def IntrinsicModule.ofPayload (payload : Payload) : IntrinsicModule :=
  ⟨typed payload.val, ⟨payload, rfl⟩⟩

def decodeIntrinsic? (bytes : ByteArray) : Option IntrinsicModule :=
  (decodePayload? bytes).map IntrinsicModule.ofPayload

end Silmaril.Wasm.Binary.Core.PassiveSerialize

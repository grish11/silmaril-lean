module

public import Silmaril.Wasm.Region.ByteMap.Defs

/-! # Whole-module provenance for body-byte maps

A layout is untrusted source framing. The checker independently validates the
whole module, section sizes, the actual code-section vector, body order, exact
source slices and import-adjusted function identities. No file offset is
identified with a function-body offset. Grammar acceptance is not validation,
instantiation or an execution theorem.
-/

@[expose] public section
namespace Silmaril.Wasm.Region.ByteMap.ModuleSource
open Silmaril.Wasm.Binary Silmaril.Wasm.Binary.Core

structure Section where
  id : UInt8
  sizeBytes : List UInt8
  payload : List UInt8

def Section.encoded (s : Section) : List UInt8 := [s.id] ++ s.sizeBytes ++ s.payload

structure Body where
  sizeBytes : List UInt8
  input : Input

def Body.encoded (b : Body) : List UInt8 := b.sizeBytes ++ b.input.bytes

structure Layout where
  sections : List Section
  codeSection : Nat
  countBytes : List UInt8
  bodies : List Body

def Layout.code? (layout : Layout) : Option Section := layout.sections[layout.codeSection]?

def Layout.codePayloadStart (layout : Layout) : Nat :=
  8 + ((layout.sections.take layout.codeSection).flatMap Section.encoded).length +
    1 + (layout.code?.map (·.sizeBytes.length)).getD 0

/-- Module/file byte offset of the locals-vector prefix of a defined body.
The body's byte coordinate zero starts here, after its own size prefix. -/
def Layout.bodyStart (layout : Layout) (i : Nat) : Nat :=
  layout.codePayloadStart + layout.countBytes.length +
    ((layout.bodies.take i).flatMap Body.encoded).length +
    ((layout.bodies[i]?).map (·.sizeBytes.length)).getD 0

def functionBody (f : Silmaril.Wasm.Func) : List ValType × Silmaril.Wasm.Expr := (f.locals, f.body)

def Body.Checks (raw : List UInt8) (m : Silmaril.Wasm.Module) (layout : Layout)
    (i : Nat) (b : Body) : Prop :=
  parseAll? (Decode.readU 32) b.sizeBytes = some b.input.bytes.length ∧
  b.input.BodyChecks ∧
  b.input.functionIndex = m.importedFunctions.length + i ∧
  (m.funcs[i]?).map functionBody = some (b.input.localGroups.flatMap expandLocal, b.input.body) ∧
  layout.bodyStart i + b.input.bytes.length ≤ raw.length ∧
  (raw.drop (layout.bodyStart i)).take b.input.bytes.length = b.input.bytes

instance (raw : List UInt8) (m : Silmaril.Wasm.Module) (layout : Layout) (i : Nat) (b : Body) :
    Decidable (b.Checks raw m layout i) := inferInstanceAs (Decidable (_ ∧ _))

/-- Redundant source-slice checks make the file/body-coordinate bridge explicit.
The exact code vector is parsed independently and compared in definition order.
Custom sections can contain arbitrary bytes; they never supply a code body. -/
def Layout.Checks (raw : List UInt8) (m : Silmaril.Wasm.Module) (layout : Layout) : Prop :=
  raw = magic ++ version ++ layout.sections.flatMap Section.encoded ∧
  (∀ s ∈ layout.sections, parseAll? (Decode.readU 32) s.sizeBytes = some s.payload.length) ∧
  (layout.sections.filter fun s => s.id == 10).length = 1 ∧
  (∃ s ∈ layout.code?.toList, s.id = 10 ∧
    s.payload = layout.countBytes ++ layout.bodies.flatMap Body.encoded ∧
    parseAll? (Decode.readVec Decode.readCode) s.payload = some (m.funcs.map functionBody)) ∧
  parseAll? (Decode.readU 32) layout.countBytes = some layout.bodies.length ∧
  layout.bodies.length = m.funcs.length ∧
  (∀ i : Fin layout.bodies.length, (layout.bodies[i]).Checks raw m layout i.val)

instance (raw : List UInt8) (m : Silmaril.Wasm.Module) (layout : Layout) :
    Decidable (layout.Checks raw m) := inferInstanceAs (Decidable (_ ∧ _))

structure Certified (raw : List UInt8) where
  decoded : Silmaril.Wasm.Module
  encoding : Encodes raw decoded
  layout : Layout
  checked : layout.Checks raw decoded

/-- A proposed layout can only be attached to the module decoded from the same
original bytes. No caller-supplied module or imported-function count is trusted. -/
def validate? (raw : List UInt8) (layout : Layout) : Option (Certified raw) :=
  match decoded : Binary.Core.decode? ⟨raw.toArray⟩ with
  | none => none
  | some m =>
    if checked : layout.Checks raw m then
      some ⟨m, by simpa using Binary.Core.decode?_sound decoded, layout, checked⟩
    else none

end Silmaril.Wasm.Region.ByteMap.ModuleSource

module

public import Silmaril.Wasm.Region.Defs
public import Silmaril.Wasm.Binary.Core.DecodeSound
public import Silmaril.Wasm.Region.ByteMap.Equality.Thms

/-! # Decoder-validated root instruction/body-byte maps

A heuristic supplies a body, its locals boundary and proposed spans. The
checker validates the whole body, locals vector, each instruction and its
preceding instruction sequence using the existing sound Core decoder. Prefix
validation ties repeated identical instructions to their actual occurrence.
This first producer covers root instructions (including whole structured
instructions). It rejects nested sequence paths rather than guessing their
byte positions. Body offsets exclude the code-section size prefix and include
locals; the end delimiter is not an instruction row.
-/

@[expose] public section
namespace Silmaril.Wasm.Region.ByteMap
open Silmaril.Machine.Region (Range)
open Silmaril.Wasm.Binary Silmaril.Wasm.Binary.Core

/-- A parser must consume the entire slice; unknown/partial parses fail. -/
def parseAll? {α : Type} (parser : Decode.DecodeM α) (bytes : List UInt8) : Option α :=
  match parser.run ⟨⟨bytes.toArray⟩, 0⟩ with
  | .error _ => none
  | .ok (a, cursor) => if cursor.rest = [] then some a else none

/-- The existing instruction decoder expects the opcode already consumed. -/
def readOne (fuel : Nat) : Decode.DecodeM Silmaril.Wasm.Instr := do
  let op ← Decode.readByte
  Decode.readInstr fuel op.toNat

def readLocal : Decode.DecodeM (Nat × ValType) := do
  let n ← Decode.readU 32
  let t ← Decode.readValType
  pure (n, t)

def expandLocal (p : Nat × ValType) : List ValType := List.replicate p.1 p.2

structure Input where
  functionIndex : Nat
  bytes : List UInt8
  codeStart : Nat
  localGroups : List (Nat × ValType)
  body : Silmaril.Wasm.Expr

/-- These are actual source slices, not re-encodings: nonminimal LEBs remain
valid when accepted by the underlying decoder. -/
def Input.spanBytes (input : Input) (r : Range) : List UInt8 :=
  (input.bytes.drop r.start).take (r.stop - r.start)

def Input.prefixBytes (input : Input) (r : Range) : List UInt8 :=
  (input.bytes.drop input.codeStart).take (r.start - input.codeStart)

def Input.BodyChecks (input : Input) : Prop :=
  input.codeStart ≤ input.bytes.length ∧
  (input.localGroups.flatMap expandLocal).length < 2 ^ 32 ∧
  parseAll? (Decode.readVec readLocal) (input.bytes.take input.codeStart) =
    some input.localGroups ∧
  parseAll? Decode.readExpr (input.bytes.drop input.codeStart) = some input.body

instance (input : Input) : Decidable input.BodyChecks := inferInstanceAs (Decidable (_ ∧ _))

def Input.SpanChecks (input : Input) (m : ByteMapEntry) : Prop :=
  m.decoded.functionIndex = input.functionIndex ∧ m.decoded.sequencePath = [] ∧
  input.codeStart ≤ m.bytes.start ∧ m.bytes.start < m.bytes.stop ∧
  m.bytes.stop ≤ input.bytes.length ∧
  parseAll? Decode.readExpr (input.prefixBytes m.bytes ++ [0x0B]) =
    some (input.body.take m.decoded.instructionOffset) ∧
  (input.body[m.decoded.instructionOffset]?).isSome ∧
  parseAll? (readOne ((input.spanBytes m.bytes).length + 1)) (input.spanBytes m.bytes) =
    input.body[m.decoded.instructionOffset]?

instance (input : Input) (m : ByteMapEntry) : Decidable (input.SpanChecks m) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The semantic certificate records both the encoded instruction prefix and
the instruction at this position in the declared decoded body. -/
def Input.DecodesAt (input : Input) (label : DecodedLabel) (r : Range) : Prop :=
  label.functionIndex = input.functionIndex ∧ label.sequencePath = [] ∧
  input.codeStart ≤ r.start ∧
  Instrs Forms.all (input.prefixBytes r) (input.body.take label.instructionOffset) ∧
  ∃ i, input.body[label.instructionOffset]? = some i ∧
    Binary.Core.Instr Forms.all (input.spanBytes r) i

def Input.TableChecks (input : Input) (entries : List ByteMapEntry) : Prop :=
  (∀ m ∈ entries, input.SpanChecks m) ∧
  (∀ m ∈ entries, ∀ n ∈ entries, m.decoded = n.decoded → m.bytes = n.bytes) ∧
  (∀ m ∈ entries, ∀ n ∈ entries,
    m.decoded.functionIndex = n.decoded.functionIndex → m.bytes.start = n.bytes.start →
      m.decoded = n.decoded)

instance (input : Input) (entries : List ByteMapEntry) : Decidable (input.TableChecks entries) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Coverage of root instruction positions is separate from table validity.
This finite criterion does not claim coverage of nested sequence paths. -/
def Input.RootCovered (input : Input) (entries : List ByteMapEntry) : Prop :=
  ∀ k : Fin input.body.length, ∃ m ∈ entries,
    m.decoded = ⟨input.functionIndex, [], k.val⟩

instance (input : Input) (entries : List ByteMapEntry) : Decidable (input.RootCovered entries) :=
  inferInstanceAs (Decidable (∀ _k : Fin input.body.length, _))

/-- A full source-body certificate plus a possibly partial validated table.
Coverage is separate; an empty successful table says nothing about coverage. -/
structure Certified (input : Input) where
  localsEncoding : Vec (Locals Forms.all) (input.bytes.take input.codeStart) (input.localGroups.map expandLocal)
  expressionEncoding : Binary.Core.Expr Forms.all (input.bytes.drop input.codeStart) input.body
  bodyEncoding : Binary.Core.Func Forms.all input.bytes ((input.localGroups.flatMap expandLocal), input.body)
  map : ValidatedByteMap (fun _ => input.bytes.length) input.DecodesAt

end Silmaril.Wasm.Region.ByteMap

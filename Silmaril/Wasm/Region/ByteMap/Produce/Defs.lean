module

public import Silmaril.Wasm.Region.ByteMap.Module.Defs
public import Silmaril.Wasm.Region.ByteMap.Nested.Thms

/-! # Automatic candidates with checked acceptance

Source cursors of existing parsers produce section/body framing and nested
instruction spines. This producer is untrusted: certificates arise only after
whole-module, body, nested-map and complete CFG-inventory checks. Fuel or unknown
layouts fail closed, never create empty target sets or guessed byte labels.
-/

@[expose] public section
namespace Silmaril.Wasm.Region.ByteMap.Produce
open Silmaril.Wasm.Binary Silmaril.Wasm.Binary.Core
open Silmaril.Machine.Region (Range)

/-- Execute an existing parser at an exact original-source cursor. -/
def at? {α : Type} (bytes : List UInt8) (pos : Nat) (p : Decode.DecodeM α) : Option (α × Nat) :=
  match p.run ⟨⟨bytes.toArray⟩, pos⟩ with
  | .error _ => none
  | .ok (a, c) => some (a, c.pos)

def slice (bytes : List UInt8) (start stop : Nat) : List UInt8 :=
  (bytes.drop start).take (stop - start)

def sections? (bytes : List UInt8) : Nat → Nat → Option (List ModuleSource.Section)
  | 0, _ => none
  | fuel + 1, pos =>
    if pos = bytes.length then some [] else do
      let (id, afterId) ← at? bytes pos Decode.readByte
      let (size, payloadStart) ← at? bytes afterId (Decode.readU 32)
      let (payload, stop) ← at? bytes payloadStart (Decode.readBytes size)
      let rest ← sections? bytes fuel stop
      pure (⟨id, slice bytes afterId payloadStart, payload.toList⟩ :: rest)

def bodies? (imported : Nat) (payload : List UInt8) : Nat → Nat → Nat → Option (List ModuleSource.Body)
  | 0, _, _ => some []
  | count + 1, index, pos => do
    let (size, bodyStart) ← at? payload pos (Decode.readU 32)
    let (raw, stop) ← at? payload bodyStart (Decode.readBytes size)
    let bytes := raw.toList
    let (groups, codeStart) ← at? bytes 0 (Decode.readVec readLocal)
    let body ← parseAll? Decode.readExpr (bytes.drop codeStart)
    let rest ← bodies? imported payload count (index + 1) stop
    pure (⟨slice payload pos bodyStart, ⟨imported + index, bytes, codeStart, groups, body⟩⟩ :: rest)

def layout? (raw : List UInt8) (m : Silmaril.Wasm.Module) : Option ModuleSource.Layout := do
  let (_, headerEnd) ← at? raw 0 Decode.readHeader
  let sections ← sections? raw (raw.length + 1) headerEnd
  let codeIndex ← (List.range sections.length).find? fun i => (sections[i]?.map (·.id)) == some 10
  let code ← sections[codeIndex]?
  let (count, bodyStart) ← at? code.payload 0 (Decode.readU 32)
  let bodies ← bodies? m.importedFunctions.length code.payload count 0 bodyStart
  pure ⟨sections, codeIndex, code.payload.take bodyStart, bodies⟩

/-- Parse the actual block header and arm delimiters to propose source layout.
The nested checker independently rechecks this decomposition and CFG identity. -/
def layoutOf? (bytes : List UInt8) (start : Nat) (instr : Silmaril.Wasm.Instr) : Option Nested.Layout := do
  let (_, header0) ← at? bytes (start + 1) Decode.readBlockType
  let headerEnd ← match instr with
    | .tryTable .. => do let (_, stop) ← at? bytes header0 (Decode.readVec Decode.readCatch); pure stop
    | .block .. | .loop .. | .if_ .. => some header0
    | _ => none
  let ((_, term), firstStop) ← at? bytes headerEnd (Decode.readSeq (bytes.length + 1))
  let first := slice bytes headerEnd (firstStop - 1)
  if term == 0x05 then do
    let ((_, last), stop) ← at? bytes firstStop (Decode.readSeq (bytes.length + 1))
    if last == 0x0B then
      pure ⟨slice bytes (start + 1) headerEnd, first, some (slice bytes firstStop (stop - 1))⟩
    else none
  else if term == 0x0B then pure ⟨slice bytes (start + 1) headerEnd, first, none⟩
  else none

/-- Recursion fuel bounds nesting only. Siblings use the original sequence's
parser cursors; canonical CFG segmentation chooses the opener's segment index. -/
def sequence? (input : Input) : Nat → Nested.Sequence → List Nested.Frame → Option (List Nested.Candidate) :=
  Nat.rec (fun _ _ => none) (fun _ recurse seq spine => do
    let mut pos := seq.span.start
    let mut result := []
    -- Structural list iteration also supports kernel evaluation of concrete examples.
    for index in List.range seq.body.length do
      let (instr, stop) ← at? input.bytes pos (readOne (input.bytes.length + 1))
      let expected ← seq.body[index]?
      if instr != expected then none else do
        let span : Range := ⟨pos, max pos stop, Nat.le_max_left _ _⟩
        result := result ++ [⟨⟨⟨input.functionIndex, seq.path, index⟩, span⟩, spine⟩]
        match instr with
        | .block .. | .loop .. | .if_ .. | .tryTable .. =>
          let layout ← layoutOf? input.bytes pos instr
          let segmentIndex ← (List.range (Cfg.segment seq.body).length).find? fun segment =>
            decide ((Nested.Frame.mk segment index span 0 layout).Opens seq instr)
          for arm in [0, 1] do
            let frame : Nested.Frame := ⟨segmentIndex, index, span, arm, layout⟩
            if let some child := frame.child? seq then
              let entries ← recurse child (spine ++ [frame])
              result := result ++ entries
        | _ => pure ()
        pos := stop
    pure result)

def candidates? (input : Input) : Option (List Nested.Candidate) :=
  sequence? input (input.bytes.length + 1) (Nested.root input) []

structure FullMap (input : Input) where
  candidates : List Nested.Candidate
  certified : Nested.Certified input
  validated : Nested.validate? input candidates = some certified
  coverage : Nested.Covered (Nested.inventory input) candidates

/-- Success provides both table correctness and coverage, never just a list
of plausible offsets. No completeness theorem for the heuristic is assumed. -/
def fullMap? (input : Input) : Option (FullMap input) := do
  let candidates ← candidates? input
  match validated : Nested.validate? input candidates with
  | none => none
  | some result =>
    if coverage : Nested.Covered (Nested.inventory input) candidates then
      some ⟨candidates, result, validated, coverage⟩
    else none

structure MappedModule (raw : List UInt8) where
  source : ModuleSource.Certified raw
  maps : ∀ i : Fin source.layout.bodies.length, FullMap (source.layout.bodies[i]).input

/-- No code section is a separate unsupported/empty-module case for this body
adapter. Failure never asserts that the module has no instructions/functions. -/
def module? (raw : List UInt8) : Option (MappedModule raw) := do
  let decoded ← Binary.Core.decode? ⟨raw.toArray⟩
  let layout ← layout? raw decoded
  let source ← ModuleSource.validate? raw layout
  if complete : ∀ i : Fin source.layout.bodies.length, (fullMap? (source.layout.bodies[i]).input).isSome then
    some ⟨source, fun i => (fullMap? (source.layout.bodies[i]).input).get (complete i)⟩
  else none

end Silmaril.Wasm.Region.ByteMap.Produce

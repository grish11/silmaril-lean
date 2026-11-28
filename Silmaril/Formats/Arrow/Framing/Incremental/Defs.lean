module

public import Silmaril.Formats.Arrow.Metadata.Defs
import Silmaril.Prelude.Bytes.Thms

/-! Incremental modern V5 framing of Schema and RecordBatch messages. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.Framing.Incremental

structure Buffer (capacity : Nat) where
  bytes : KBytes
  bounded : bytes.len ≤ capacity
  source : bytes.wf = true

def Buffer.empty (capacity : Nat) : Buffer capacity := ⟨.empty, Nat.zero_le _, rfl⟩

structure Filled (capacity : Nat) where
  buffered : Buffer capacity
  rest : KBytes

/-- Consume only the bytes wanted by the current request. The remainder
belongs to the caller and can contain any number of further frames. -/
def Buffer.feed {capacity : Nat} (buffer : Buffer capacity) (chunk : KBytes)
    (valid : chunk.wf = true) : Filled capacity :=
  let count := min (capacity - buffer.bytes.len) chunk.len
  let bytes := if count = 0 then buffer.bytes else buffer.bytes ++ chunk.slice 0 count
  have fits : count ≤ chunk.len := Nat.min_le_right _ _
  have small := buffer.bounded
  have countBound : count ≤ capacity - buffer.bytes.len := Nat.min_le_left _ _
  have bounded : bytes.len ≤ capacity := by
    dsimp only [bytes]
    split
    · exact small
    · change buffer.bytes.len + (chunk.slice 0 count).len ≤ capacity
      rw [KBytes.len_slice]
      omega
  have source : bytes.wf = true := by
    dsimp only [bytes]
    split
    · exact buffer.source
    · exact KBytes.wf_append buffer.source (chunk.wf_slice 0 count valid (by simpa using fits))
  ⟨⟨bytes, bounded, source⟩, chunk.slice count (chunk.len - count)⟩

/-- Rechunk only the completed metadata before inspecting its Message
table so the planner observes one deterministic representation. -/
def metadataBytes (bytes : KBytes) : KBytes :=
  .leaf bytes.len (bytes.read 0 bytes.len)

def plan (limits : Limits) (metadata : KBytes) : Except Arrow.Error Nat := do
  let size ← frameBodyLength limits (metadataBytes metadata)
  if size % 8 ≠ 0 then throw (.malformed .bodyLength)
  if size > limits.bodyBytes then throw (.limit .bodyBytes)
  return size

inductive Part where
  | prefix | metadata | body | tail
  deriving DecidableEq, Repr

structure Failure where
  part : Part
  offset : Nat
  cause : Arrow.Error
  deriving DecidableEq, Repr

structure Frame where
  offset : Nat
  metadata : KBytes
  body : KBytes

def Frame.next (frame : Frame) : Nat := frame.offset + 8 + frame.metadata.len + frame.body.len

inductive State where
  | prefix (offset : Nat) (pending : Buffer 8)
  | metadata (offset size : Nat) (pending : Buffer size)
  | body (offset : Nat) (metadata : KBytes) (size : Nat) (pending : Buffer size)
  | ended (offset : Nat)

def start (offset : Nat := 0) : State := .prefix offset (.empty 8)

def State.position : State → Nat
  | .prefix offset pending => offset + pending.bytes.len
  | .metadata offset _ pending => offset + 8 + pending.bytes.len
  | .body offset header _ pending => offset + 8 + header.len + pending.bytes.len
  | .ended offset => offset

def State.part : State → Part
  | .prefix .. => .prefix
  | .metadata .. => .metadata
  | .body .. => .body
  | .ended .. => .tail

def State.requestOffset : State → Nat
  | .prefix offset _ => offset
  | .metadata offset _ _ => offset
  | .body offset header _ _ => offset + 8 + header.len
  | .ended offset => offset

inductive Progress where
  | wait (state : State)
  | advance (state : State) (rest : KBytes)
  | frame (value : Frame) (next : State) (rest : KBytes)

/-- Final input ends successfully only after the complete modern EOS.
An unfinished request is distinguished from the ordinary wait returned
by feed while the input remains open. -/
def finish (state : State) : Except Failure Nat :=
  match state with
  | .ended offset => .ok offset
  | _ => .error ⟨state.part, state.requestOffset, .malformed .truncated⟩

/-- Feed an ordered fragment into the current request. An advance hands the
remainder back for the next request, including a zero-length body. EOS is
provisional until finish, so later nonempty fragments are rejected. -/
def feed (limits : Limits) (state : State) (chunk : KBytes) : Except Failure Progress :=
  if valid : chunk.wf = true then
    match state with
    | .prefix offset pending => do
      if offset % 8 ≠ 0 then throw ⟨.prefix, offset, .malformed .alignment⟩
      let filled := pending.feed chunk valid
      let bytes := filled.buffered.bytes
      if bytes.len < 8 then return .wait (.prefix offset filled.buffered)
      let header ← (readPrefix limits (bytes.read 0 4) (bytes.read 4 4)).mapError
        (fun cause => ⟨.prefix, offset, cause⟩)
      match header with
      | .metadata size => return .advance (.metadata offset size (.empty size)) filled.rest
      | .eos =>
        if filled.rest.len = 0 then return .advance (.ended (offset + 8)) filled.rest
        else throw ⟨.tail, offset + 8, .malformed .trailingBytes⟩
    | .metadata offset size pending => do
      let filled := pending.feed chunk valid
      let bytes := filled.buffered.bytes
      if bytes.len < size then return .wait (.metadata offset size filled.buffered)
      let bodyLength ← (plan limits bytes).mapError (fun cause => ⟨.metadata, offset, cause⟩)
      return .advance (.body offset bytes bodyLength (.empty bodyLength)) filled.rest
    | .body offset header size pending => do
      let filled := pending.feed chunk valid
      let bytes := filled.buffered.bytes
      if bytes.len < size then return .wait (.body offset header size filled.buffered)
      let frame : Frame := ⟨offset, header, bytes⟩
      return .frame frame (start frame.next) filled.rest
    | .ended offset =>
      if chunk.len = 0 then .ok (.wait (.ended offset))
      else .error ⟨.tail, offset, .malformed .trailingBytes⟩
  else .error ⟨state.part, state.position, .malformed .source⟩

/-- A bounded slice in the immutable carrier, compared by its octets. -/
structure Window (input : KBytes) (offset : Nat) (bytes : KBytes) : Prop where
  source : bytes.wf = true
  bounded : offset + bytes.len ≤ input.len
  exact : bytes.toList = (input.toList.drop offset).take bytes.len

/-- A pending state represents the original prefix of its current request.
This relation allows the immutable reference itself to end mid-request. -/
def State.InCarrier (limits : Limits) (input : KBytes) : State → Prop
  | .prefix offset pending => Window input offset pending.bytes
  | .metadata offset size pending =>
    offset % 8 = 0 ∧
    readPrefix limits (input.read offset 4) (input.read (offset + 4) 4) = .ok (.metadata size) ∧
    Window input (offset + 8) pending.bytes
  | .body offset header size pending =>
    readEnvelope limits input offset = .ok (.metadata header.len) ∧
    Window input (offset + 8) header ∧ plan limits header = .ok size ∧
    Window input (offset + 8 + header.len) pending.bytes
  | .ended offset => ∃ eos, offset = eos + 8 ∧ readEnvelope limits input eos = .ok .eos

/-- A completed frame agrees with both existing carrier decoders and has
the exact original metadata and body octets. -/
def Frame.InCarrier (limits : Limits) (input : KBytes) (frame : Frame) : Prop :=
  readEnvelope limits input frame.offset = .ok (.metadata frame.metadata.len) ∧
    Window input (frame.offset + 8) frame.metadata ∧
    plan limits (input.slice (frame.offset + 8) frame.metadata.len) = .ok frame.body.len ∧
    ∃ body, readBody limits input (frame.offset + 8 + frame.metadata.len) frame.body.len = .ok body ∧
      frame.body.toList = body.toList

/-- A successful call accounts for its input bytes and returned suffix.
The frame branch also checks the original immutable-carrier observation. -/
def Progress.InCarrier (limits : Limits) (input : KBytes) (previous : State) (chunk : KBytes) :
    Progress → Prop
  | .wait state =>
    state.InCarrier limits input ∧ state.position = previous.position + chunk.len
  | .advance state rest =>
    state.InCarrier limits input ∧ Window input state.position rest ∧
      state.position + rest.len = previous.position + chunk.len
  | .frame value next rest =>
    value.InCarrier limits input ∧ next.InCarrier limits input ∧
      next.position = value.next ∧ Window input next.position rest ∧
      next.position + rest.len = previous.position + chunk.len

end Silmaril.Formats.Arrow.Framing.Incremental

module

public import Silmaril.Formats.Blake3Cas.Evidence.Thms
public import Silmaril.Formats.Iroh.Thms
public import Silmaril.Semantics.Naming.ByteRange.Thms

@[expose] public section

namespace Silmaril.Formats.Blake3Cas

open Silmaril.Crypto.Blake3
open Silmaril.Semantics.Naming.ByteRange (Slice slice_iff)

structure SpanFact (size : Nat) (digest : Bytes) where
  offset : Nat
  bytes : Bytes
  checked : Checked concrete size digest offset bytes

/-- Position agreement is checked against the kernel's shape reached by the
authenticated path, not against a coordinate supplied by the body. -/
def Aligned (span : Bao.Span) (shape : Shape) (base : Nat) : Prop :=
  span = shapeSpan shape ∧ span.byteStart = base

instance (span : Bao.Span) (shape : Shape) (base : Nat) : Decidable (Aligned span shape base) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Every constructor is indexed by the actual field consumed. For a pair the two
word vectors must serialize to that field in left/right order. -/
inductive Cell (size : Nat) (digest : Bytes) : Bytes → Type where
  | pair {raw : Bytes} (span : Bao.Span) (root : Bool) (left right expected : CV)
      (wire : digestBytes left ++ digestBytes right = raw)
      (checked : parentCV root left right = expected)
      (location : ∃ leftShape rightShape base edge,
        Aligned span (.fork leftShape rightShape) base ∧
          Anchor size digest (.fork leftShape rightShape) root expected base edge) : Cell size digest raw
  | data (span : Bao.Span) (fact : SpanFact size digest)
      (location : ∃ shape root expected edge, Aligned span shape fact.offset ∧
        fact.bytes.length = span.byteSize size ∧ fact.bytes.length = shape.size ∧
        Anchor size digest shape root expected fact.offset edge ∧
        subtreeCV? root shape fact.bytes = some expected) : Cell size digest fact.bytes

structure Work (size : Nat) (digest : Bytes) where
  plan : Bao.Plan
  shape : Shape
  root : Bool
  expected : CV
  base : Nat
  edge : Bool
  anchor : Anchor size digest shape root expected base edge

abbrev EOFProof (size : Nat) (digest : Bytes) := PLift (CheckedEOF concrete size digest)

structure Session (size : Nat) (digest : Bytes) where
  pending : List (Work size digest)
  eof : Option (EOFProof size digest)

def begin? (size cap : Nat) (digest : Bytes) (plan : Bao.Plan) : Option (Session size digest) := do
  if size > cap then none else
    if valid : validSize size then
      let cv ← parseCV digest
      match plan with
      | .skip => none
      | _ => some ⟨[⟨plan, geometry 0 size, true, cv.val, 0, true, rootAnchor valid cv.property⟩], none⟩
    else none

def Work.enqueue {size : Nat} {digest : Bytes} (work : Work size digest)
    (tail : List (Work size digest)) : List (Work size digest) :=
  match work.plan with
  | .skip => tail
  | _ => work :: tail

def parsePair (raw : Bytes) : Option {pair : CV × CV //
    digestBytes pair.1 ++ digestBytes pair.2 = raw} := do
  let left ← parseCV (raw.take 32)
  let right ← parseCV (raw.drop 32)
  return ⟨(left.val, right.val), by rw [left.property, right.property, List.take_append_drop]⟩

def nextSlot {size : Nat} {digest : Bytes} (state : Session size digest) : Option Bao.Slot :=
  match state.pending with
  | ⟨.fork span _ _, _, _, _, _, _, _⟩ :: _ => some (.pair span)
  | ⟨.leaf span width, _, _, _, _, _, _⟩ :: _ => some (.data span width)
  | _ => none

set_option maxHeartbeats 1000000 in
/-- One proof cell. All coordinates and widths are cross-checked with the canonical
kernel subtree. The final-chunk proof comes from hashing data on the rightmost path. -/
def step? {size : Nat} {digest : Bytes} (state : Session size digest) (raw : Bytes) :
    Option (Session size digest × Cell size digest raw) :=
  match state.pending with
  | [] => none
  | work :: tail =>
    match work.plan with
    | .skip => none
    | .fork span leftPlan rightPlan => do
      if aligned : Aligned span work.shape work.base then
        match shapeEq : work.shape with
        | .leaf .. => none
        | .fork left right => do
          let pair ← parsePair raw
          let lcv := pair.val.1
          let rcv := pair.val.2
          if hit : parentCV work.root lcv rcv = work.expected then
            let anchor : Anchor size digest (.fork left right) work.root work.expected work.base work.edge :=
              shapeEq ▸ work.anchor
            let lhs : Work size digest := ⟨leftPlan, left, false, lcv, work.base, false, anchor.left hit⟩
            let rhs : Work size digest :=
              ⟨rightPlan, right, false, rcv, work.base + left.size, work.edge, anchor.right hit⟩
            some (⟨lhs.enqueue (rhs.enqueue tail), state.eof⟩,
              .pair span work.root lcv rcv work.expected pair.property hit
                ⟨left, right, work.base, work.edge, shapeEq ▸ aligned, anchor⟩)
          else none
      else none
    | .leaf span width =>
      if aligned : Aligned span work.shape work.base then
        if exactWidth : raw.length = width ∧ raw.length = span.byteSize size ∧ raw.length = work.shape.size then
          if hit : subtreeCV? work.root work.shape raw = some work.expected then
            let facts := work.anchor.openCell exactWidth.2.2 hit
            let eof := if edge : work.edge = true then some ⟨facts.2 edge⟩ else state.eof
            some (⟨tail, eof⟩, .data span ⟨work.base, raw, facts.1⟩
              ⟨work.shape, work.root, work.expected, work.edge, aligned, exactWidth.2.1, exactWidth.2.2,
                work.anchor, hit⟩)
          else none
        else none
      else none

structure RawStep (size : Nat) (digest input : Bytes) where
  next : Session size digest
  field : Bytes
  cell : Cell size digest field
  rest : Bytes
  wire : input = field ++ rest

/-- Incremental entry point for already available bytes. No assertion about the
rest of the frame is needed to use the returned cell. -/
def readStep? {size : Nat} {digest : Bytes} (state : Session size digest) (input : Bytes) :
    Option (RawStep size digest input) := do
  let slot ← nextSlot state
  match parsed : Bao.takeExact slot.width input with
  | none => none
  | some (field, rest) =>
    let (next, cell) ← step? state field
    return ⟨next, field, cell, rest, (Bao.takeExact_spec.mp parsed).2⟩

inductive Tape (size : Nat) (digest : Bytes) : List Bytes → Type where
  | nil : Tape size digest []
  | cons {raw : Bytes} {fields : List Bytes} (cell : Cell size digest raw)
      (tail : Tape size digest fields) : Tape size digest (raw :: fields)

def Tape.pairs {size : Nat} {digest : Bytes} {fields : List Bytes} : Tape size digest fields → List Bytes
  | .nil => []
  | .cons (raw := raw) (.pair ..) tail => raw :: tail.pairs
  | .cons (.data ..) tail => tail.pairs

def Tape.spans {size : Nat} {digest : Bytes} {fields : List Bytes} :
    Tape size digest fields → List (SpanFact size digest)
  | .nil => []
  | .cons (.pair ..) tail => tail.spans
  | .cons (.data _ fact _) tail => fact :: tail.spans

def checkTape? {size : Nat} {digest : Bytes} (state : Session size digest) :
    (fields : List Bytes) → Option (Session size digest × Tape size digest fields)
  | [] => some (state, .nil)
  | raw :: fields => do
    let (next, cell) ← step? state raw
    let (final, tape) ← checkTape? next fields
    return (final, .cons cell tape)

/-- Finishing a scheduled body additionally requires a known frame boundary and
no trailing bytes; reaching EOF is an independent authentication fact. -/
def finished {size : Nat} {digest : Bytes} (state : Session size digest)
    (rest : Bytes) (endOfFrame : Bool) : Bool :=
  state.pending.isEmpty && rest.isEmpty && endOfFrame

structure CompleteBody (size : Nat) (digest : Bytes) (fields : List Bytes) where
  tape : Tape size digest fields
  final : Session size digest
  complete : final.pending.isEmpty = true

def checkBody? (size cap : Nat) (digest : Bytes) (plan : Bao.Plan) (fields : List Bytes) :
    Option (CompleteBody size digest fields) := do
  let state ← begin? size cap digest plan
  let (final, tape) ← checkTape? state fields
  if done : final.pending.isEmpty = true then some ⟨tape, final, done⟩ else none

def HeaderBinds (input : Bytes) (size : Nat) (body : Bytes) : Prop :=
  ∃ header : Bytes, header.length = 8 ∧ Bao.getLE header = size ∧ input = header ++ body

structure InlineFrame (input digest : Bytes) where
  size : Nat
  fields : List Bytes
  body : CompleteBody size digest fields
  wire : HeaderBinds input size fields.flatten

inductive InlineEncoding where
  | combined
  | slice (request : Bao.RangeRequest)

def InlineEncoding.encoding : InlineEncoding → Bao.Encoding
  | .combined => .combined
  | .slice request => .slice request

def InlineEncoding.plan (encoding : InlineEncoding) (size : Nat) : Bao.Plan :=
  match encoding with
  | .combined => Bao.fullPlan size 1
  | .slice request => Bao.slicePlan size request

/-- Strict single-frame Bao combined or slice. The returned tape is indexed by the
fields of the actual unmodified input body. -/
def checkBaoInline? (encoding : InlineEncoding) (cap : Nat) (digest input : Bytes) :
    Option (InlineFrame input digest) := do
  let (claim, _) ← Bao.readHeader input
  if claim > cap then none else
    match parsed : Bao.decode encoding.encoding input with
    | none => none
    | some (size, fields) => do
      let body ← checkBody? size cap digest (encoding.plan size) fields
      let wire := Bao.readHeader_spec.mp (Bao.decode_spec.mp parsed).2.2.1
      return ⟨size, fields, body, wire⟩

structure OutboardFrame (input original digest : Bytes) where
  size : Nat
  fields : List Bytes
  body : CompleteBody size digest fields
  wire : HeaderBinds input size body.tape.pairs.flatten
  dataWire : (body.tape.spans.map SpanFact.bytes).flatten = original
  dataAt : ∀ fact ∈ body.tape.spans, Slice original fact.offset fact.bytes

def SpanFact.matches {size : Nat} {digest : Bytes} (fact : SpanFact size digest) (original : Bytes) : Bool :=
  decide (fact.offset + fact.bytes.length ≤ original.length ∧
    (original.drop fact.offset).take fact.bytes.length = fact.bytes)

/-- Strict official Bao outboard plus its separate original-data input. The shared
verifier sees interleaved fields; both projections are checked against the sources. -/
def checkBaoOutboard? (cap : Nat) (digest input original : Bytes) :
    Option (OutboardFrame input original digest) := do
  let (claim, _) ← Bao.readHeader input
  if claim > cap || original.length != claim then none else
    match parsed : Bao.decode .outboard input with
    | none => none
    | some (size, fields) => do
      let plan := Bao.fullPlan size 1
      let pairs := Bao.positioned (plan.pairs false) fields
      let interleaved ← plan.preorder.mapM (Bao.outboardSource pairs original)
      let body ← checkBody? size cap digest plan interleaved
      if exactPairs : body.tape.pairs = fields then
        if exactData : (body.tape.spans.map SpanFact.bytes).flatten = original then
          if atOffsets : (body.tape.spans.all (fun fact => fact.matches original)) = true then
            let wire := Bao.readHeader_spec.mp (Bao.decode_spec.mp parsed).2.2.1
            let dataAt := fun fact mem => slice_iff.mpr (of_decide_eq_true (List.all_eq_true.mp atOffsets fact mem))
            return ⟨size, interleaved, body, by simpa only [HeaderBinds, exactPairs] using wire, exactData, dataAt⟩
          else none
        else none
      else none

structure RawGetFrame (request response digest : Bytes) where
  get : Iroh.Get
  requestWire : Iroh.readGet request = some get
  canonicalWire : request = Iroh.writeGet get
  rootWire : get.hash.bytes.toArray.toList = digest
  frame : InlineFrame response digest

/-- Canonical raw single-blob Get; no HashSeq children or transport are inferred.
The root in the actual request must equal the independently expected name. -/
def checkIrohRawGet? (cap : Nat) (digest request response : Bytes) :
    Option (RawGetFrame request response digest) := do
  let (claim, _) ← Bao.readHeader response
  if claim > cap then none else
    match getEq : Iroh.readGet request with
    | none => none
    | some get => do
      let [(0, query), (1, [])] := get.ranges | none
      if canonical : request = Iroh.writeGet get then
        if query.isEmpty then none else
          if expected : get.hash.bytes.toArray.toList = digest then
            match parsed : Iroh.readResponse query response with
            | some (size, fields, []) => do
              let body ← checkBody? size cap digest (Iroh.responsePlan size query) fields
              let wire := Bao.readHeader_spec.mp (Iroh.readResponse_spec.mp parsed).1
              return ⟨get, getEq, canonical, expected, size, fields, body, by simpa [HeaderBinds] using wire⟩
            | _ => none
          else none
      else none

/-- `take` always advances by a positive, kernel-checked span starting at the
current cursor. A proof cell outside the requested window does not advance it. -/
inductive Advance (size : Nat) (digest : Bytes) : Nat → Nat → Type where
  | skip (offset : Nat) : Advance size digest offset offset
  | take (offset : Nat) (bytes : Bytes) (nonempty : 0 < bytes.length)
      (checked : Checked concrete size digest offset bytes) :
      Advance size digest offset (offset + bytes.length)

def Advance.bytes {size before after : Nat} {digest : Bytes} :
    Advance size digest before after → Bytes
  | .skip _ => []
  | .take _ bytes _ _ => bytes

def Advance.released {size : Nat} {digest : Bytes} :
    {before after : Nat} → Advance size digest before after → Option (SpanFact size digest)
  | _, _, .skip _ => none
  | _, _, .take offset bytes _ checked => some ⟨offset, bytes, checked⟩

def project? {size : Nat} {digest : Bytes} (request : Bao.RangeRequest) (cursor : Nat)
    (fact : SpanFact size digest) : Option (Σ next, Advance size digest cursor next) :=
  let lo := max request.start fact.offset
  let hi := min (request.start + request.count) (fact.offset + fact.bytes.length)
  if lo < hi then
    let shift := lo - fact.offset
    let bytes := (fact.bytes.drop shift).take (hi - lo)
    if valid : fact.offset + shift = cursor ∧ 0 < bytes.length ∧
        shift + bytes.length ≤ fact.bytes.length ∧ cursor + bytes.length = hi then
      let slice : Slice fact.bytes shift bytes := slice_iff.mpr
        ⟨valid.2.2.1, by simp [bytes, List.length_take]⟩
      let checked := fact.checked.sub slice
      some ⟨cursor + bytes.length, .take cursor bytes valid.2.1 (valid.1 ▸ checked)⟩
    else none
  else some ⟨cursor, .skip cursor⟩

def Cell.project? {size : Nat} {digest raw : Bytes} (request : Bao.RangeRequest)
    (cursor : Nat) : Cell size digest raw → Option (Σ next, Advance size digest cursor next)
  | .pair .. => some ⟨cursor, .skip cursor⟩
  | .data _ fact _ => Blake3Cas.project? request cursor fact

/-- A sequence of checked emissions, indexed by its exact start and end offsets.
This is a prefix fact: it has no dependency on successful frame completion. -/
inductive Coverage (size : Nat) (digest : Bytes) : Nat → Nat → Type where
  | nil (offset : Nat) : Coverage size digest offset offset
  | cons {before middle after : Nat} (head : Advance size digest before middle)
      (tail : Coverage size digest middle after) : Coverage size digest before after

def Coverage.bytes {size before after : Nat} {digest : Bytes} : Coverage size digest before after → Bytes
  | .nil _ => []
  | .cons head tail => head.bytes ++ tail.bytes

def Tape.project? {size : Nat} {digest : Bytes} (request : Bao.RangeRequest) (cursor : Nat)
    {fields : List Bytes} (tape : Tape size digest fields) :
    Option (Σ next, Coverage size digest cursor next) :=
  match tape with
  | .nil => some ⟨cursor, .nil cursor⟩
  | .cons cell tail => do
    let ⟨next, advance⟩ ← cell.project? request cursor
    let ⟨finish, coverage⟩ ← tail.project? request next
    return ⟨finish, .cons advance coverage⟩

structure RangeStep (size : Nat) (digest input : Bytes) (cursor : Nat) where
  raw : RawStep size digest input
  next : Nat
  advance : Advance size digest cursor next

/-- The incremental driver consumes at most one cell. A truncation or invalid
next cell cannot invalidate an earlier `Advance` or `Coverage` witness. -/
def readRangeStep? {size : Nat} {digest : Bytes} (request : Bao.RangeRequest) (cursor : Nat)
    (state : Session size digest) (input : Bytes) : Option (RangeStep size digest input cursor) := do
  let raw ← readStep? state input
  let ⟨next, advance⟩ ← raw.cell.project? request cursor
  return ⟨raw, next, advance⟩

/-- Promote a staged span using a caller-supplied trusted extent, never the header. -/
def RangeStep.trustedSpan? {size cursor : Nat} {digest input : Bytes}
    (step : RangeStep size digest input cursor) (trustedSize : Nat) : Option (SpanFact trustedSize digest) :=
  if same : size = trustedSize then step.advance.released.map (same ▸ ·) else none

/-- A proof from this or another frame may promote a staged span for the same claim and root. -/
def RangeStep.verifiedSpan? {size cursor : Nat} {digest input : Bytes}
    (step : RangeStep size digest input cursor) (eof : EOFProof size digest) :
    Option (SpanFact size digest × EOFProof size digest) := step.advance.released.map (·, eof)

/-- An actual successful prefix of raw reads, with both cursors and the unconsumed
suffix indexed. No hypothesis states that the suffix is a valid continuation. -/
inductive Prefix {size : Nat} {digest : Bytes} (request : Bao.RangeRequest) :
    Nat → Session size digest → Bytes → Nat → Session size digest → Bytes → Type where
  | nil (cursor : Nat) (state : Session size digest) (rest : Bytes) :
      Prefix request cursor state rest cursor state rest
  | cons {before after : Nat} {initial final : Session size digest} {input rest : Bytes}
      {step : RangeStep size digest input before}
      (hit : readRangeStep? request before initial input = some step)
      (tail : Prefix request step.next step.raw.next step.raw.rest after final rest) :
      Prefix request before initial input after final rest

def Prefix.coverage {size before after : Nat} {digest input rest : Bytes}
    {request : Bao.RangeRequest} {initial final : Session size digest} :
    Prefix request before initial input after final rest → Coverage size digest before after
  | .nil cursor _ _ => .nil cursor
  | .cons (step := step) _ tail => .cons step.advance tail.coverage

def Prefix.fields {size before after : Nat} {digest input rest : Bytes}
    {request : Bao.RangeRequest} {initial final : Session size digest} :
    Prefix request before initial input after final rest → List Bytes
  | .nil .. => []
  | .cons (step := step) _ tail => step.raw.field :: tail.fields

def rangeFinished {size : Nat} {digest : Bytes} (request : Bao.RangeRequest)
    (cursor : Nat) (state : Session size digest) (rest : Bytes) (endOfFrame : Bool) : Bool :=
  finished state rest endOfFrame && cursor == request.start + request.count && Bao.strictBounds size request

structure ExactRange (size : Nat) (digest : Bytes) (request : Bao.RangeRequest) where
  within : request.start + request.count ≤ size
  coverage : Coverage size digest request.start (request.start + request.count)

def CompleteBody.range? {size : Nat} {digest : Bytes} {fields : List Bytes}
    (body : CompleteBody size digest fields) (request : Bao.RangeRequest) :
    Option (ExactRange size digest request) := do
  if within : request.start + request.count ≤ size then
    let ⟨stop, coverage⟩ ← body.tape.project? request request.start
    if done : stop = request.start + request.count then some ⟨within, done ▸ coverage⟩ else none
  else none

/-- The extent used for the wire schedule must equal a caller's trusted extent. -/
def CompleteBody.trustedRange? {size : Nat} {digest : Bytes} {fields : List Bytes}
    (body : CompleteBody size digest fields) (trustedSize : Nat) (request : Bao.RangeRequest) :
    Option (ExactRange trustedSize digest request) :=
  if matchSize : size = trustedSize then (body.range? request).map (matchSize ▸ ·) else none

/-- This mode does not promote the extent field; a kernel right-edge witness is required. -/
def CompleteBody.verifiedRange? {size : Nat} {digest : Bytes} {fields : List Bytes}
    (body : CompleteBody size digest fields) (request : Bao.RangeRequest) :
    Option (ExactRange size digest request × EOFProof size digest) := do
  let eof ← body.final.eof
  return (← body.range? request, eof)

/-- Distinct actual compression inputs with identical low 256 output bits. -/
def ConcreteCollision : Prop := ∃ left right : Input, left ≠ right ∧ compress32 left = compress32 right

end Silmaril.Formats.Blake3Cas

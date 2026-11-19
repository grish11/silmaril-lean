module

public import Silmaril.Machine.Region.Defs
public import Silmaril.Wasm.Cfg.BlockCfg.Defs

/-! # Wasm region candidates and typed byte-map obligations

Reuses `Cfg.blockCfg`/`lookup`; no second CFG builder or region execution
semantics. These are syntactic candidates, NOT operational certificates.
Existing `Cfg.Region`/`Cfg.Session` prove operational results under their own
profiles and call interfaces; no theorem here equates this graph with them.
-/

@[expose] public section
namespace Silmaril.Wasm.Region
open Silmaril.Semantics.Region

/-- An instruction position in one structured sequence, scoped by module
function index (imports count). The path resolves nested sequences. -/
structure DecodedLabel where
  functionIndex : Nat
  sequencePath : List Cfg.SeqStep
  instructionOffset : Nat
  deriving DecidableEq, Repr

/-- A byte offset within the encoded function body, not a module/file offset.
Locals and delimiters affect this offset; it is NOT an instruction index. -/
structure RawLabel where
  functionIndex : Nat
  bodyByteOffset : Nat
  deriving DecidableEq, Repr

structure DecodedSegment where
  functionIndex : Nat
  sequencePath : List Cfg.SeqStep
  instructions : Silmaril.Machine.Region.Range
  deriving DecidableEq

structure RawSegment where
  functionIndex : Nat
  bodyBytes : Silmaril.Machine.Region.Range
  deriving DecidableEq

/-- The imported decoder/encoder must prove each nonempty byte span decodes
at the declared structured instruction position. An arbitrary table is not
validated merely because its offsets are in bounds. -/
structure ByteMapEntry where
  decoded : DecodedLabel
  bytes : Silmaril.Machine.Region.Range

structure ValidatedByteMap (bodySize : Nat → Nat)
    (decodesAt : DecodedLabel → Silmaril.Machine.Region.Range → Prop) where
  entries : List ByteMapEntry
  correct : ∀ m ∈ entries, decodesAt m.decoded m.bytes
  bounds : ∀ m ∈ entries, m.bytes.start < m.bytes.stop ∧ m.bytes.stop ≤ bodySize m.decoded.functionIndex
  uniqueDecoded : ∀ m ∈ entries, ∀ n ∈ entries, m.decoded = n.decoded → m.bytes = n.bytes
  uniqueRaw : ∀ m ∈ entries, ∀ n ∈ entries,
    m.decoded.functionIndex = n.decoded.functionIndex → m.bytes.start = n.bytes.start → m.decoded = n.decoded

/-- Partial mapping: absence stays unknown. Consumers must prove coverage for
all labels in the region before erasing the decoded representation. -/
def ValidatedByteMap.raw? {bodySize : Nat → Nat}
    {decodesAt : DecodedLabel → Silmaril.Machine.Region.Range → Prop}
    (map : ValidatedByteMap bodySize decodesAt) (label : DecodedLabel) : Option RawLabel :=
  (map.entries.find? fun m => m.decoded == label).map fun m =>
    ⟨m.decoded.functionIndex, m.bytes.start⟩

/-- Target labels are scoped by the functionIndex of this row. Cfg's block
identity is a segment position, not a byte or instruction offset. `exit`,
`trap`, `raise`, `invalid` remain distinct synthetic targets. -/
structure CandidateRow where
  functionIndex : Nat
  block : Cfg.BlockId
  targets : Targets Cfg.Target
  effects : List Cfg.Effect

/-- Calls and unresolved handlers remain Top in this interface: finite
resumption edges need an operational call/handler certificate. -/
def candidateTargets (body : Expr) (b : Cfg.BlockId) (s : Cfg.Segment) : Targets Cfg.Target :=
  let effects := Cfg.blockEffects body b s
  if effects.contains .call || effects.contains .unresolvedHandler then .top
  else .finite (Cfg.succOf body b s ++ Cfg.effectSucc body b s).toFinset

/-- Reuses the existing extracted block inventory. -/
def candidates (functionIndex : Nat) (body : Expr) : List CandidateRow :=
  (Cfg.blocks body).map fun (b, s) =>
    ⟨functionIndex, b, candidateTargets body b s, Cfg.blockEffects body b s⟩

end Silmaril.Wasm.Region

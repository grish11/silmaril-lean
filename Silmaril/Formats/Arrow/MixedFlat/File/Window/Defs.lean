module

public import Silmaril.Formats.Arrow.MixedFlat.File.Defs

/-! Opt-in random access to a mixed V5 file in an absolute carrier window. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.MixedFlat.File.Window

inductive Error where
  | window (cause : Arrow.Error)
  | file (cause : MixedFlat.File.Error)
  deriving DecidableEq, Repr

structure Bounds (input : KBytes) (start stop : Nat) : Type where
  ordered : start ≤ stop
  bounded : stop ≤ input.len
  aligned : start % 8 = 0
  source : input.wf = true

def checkBounds (input : KBytes) (start stop : Nat) : Except Error (Bounds input start stop) :=
  if outside : stop < start ∨ input.len < stop then .error (.window (.malformed .truncated))
  else if aligned : start % 8 = 0 then
    if source : input.wf = true then
      .ok ⟨Nat.le_of_not_gt (fun order => outside (.inl order)),
        Nat.le_of_not_gt (fun bound => outside (.inr bound)), aligned, source⟩
    else .error (.window (.malformed .source))
  else .error (.window (.malformed .alignment))

/-- The footer trailer is checked against the bounded file slice. Its
block offsets are absolute positions in the original immutable input. -/
structure Index (input : KBytes) (start stop : Nat) where
  bounds : Bounds input start stop
  span : FileReader.FooterSpan (input.slice start (stop - start))
  footer : MixedFlat.FileFooter
  schemaSize : Nat
  schemaFits : 16 + schemaSize + 8 ≤ span.start
  fits : FileReader.BlocksFit (start + span.start) (start + 16 + schemaSize) footer.blocks

def Index.footerStart {input : KBytes} {start stop : Nat} (index : Index input start stop) : Nat :=
  start + index.span.start

def Index.schemaMetadata {input : KBytes} {start stop : Nat} (index : Index input start stop) :
    KBytes :=
  input.slice (start + 16) index.schemaSize

/-- Admit the file in `[start, stop)`. Only the footer span is found using
the bounded slice. The Schema and block positions stay carrier-relative. -/
def readIndex (limits : Arrow.Limits) (input : KBytes) (start stop : Nat) :
    Except Error (Index input start stop) := do
  let bounds ← checkBounds input start stop
  let span ← (FileReader.readFooterSpan limits (input.slice start (stop - start))).mapError
    (fun cause => .file (.footer cause))
  let footerStart := start + span.start
  let footer ← (MixedFlat.readFileFooter limits (input.slice footerStart span.length)).mapError
    (fun cause => .file (.footer cause))
  if 24 > span.start then throw (.file (.schema (.malformed .truncated)))
  let envelope ← (readEnvelope limits input (start + 8)).mapError (fun cause => .file (.schema cause))
  let .metadata size := envelope | throw (.file (.schema (.malformed .schemaOrder)))
  if schemaFits : 16 + size + 8 ≤ span.start then
    let fields ← (MixedFlat.readSchema limits (input.slice (start + 16) size)).mapError
      (fun cause => .file (.schema cause))
    if fields ≠ footer.fields then throw (.file .schemaMismatch)
    if fits : FileReader.BlocksFit footerStart (start + 16 + size) footer.blocks then
      let tail ← (readEnvelope limits input (footerStart - 8)).mapError (fun cause => .file (.eos cause))
      let .eos := tail | throw (.file (.eos (.malformed .trailingBytes)))
      return ⟨bounds, span, footer, size, schemaFits, fits⟩
    else throw (.file .blockLayout)
  else throw (.file (.schema (.malformed .truncated)))

/-- Decode the selected block on the original carrier. A missing entry is
`.ok none`; a bad record reports the selected footer ordinal. -/
def Index.readAt {input : KBytes} {start stop : Nat} (index : Index input start stop)
    (limits : MixedFlat.Limits) (n : Nat) : Except Error (Option MixedFlat.Observed) :=
  index.footer.blocks[n]?.mapM fun block =>
    (MixedFlat.File.readRecord limits input index.footer.fields block).mapError
      (fun cause => .file (.batch n cause))

end Silmaril.Formats.Arrow.MixedFlat.File.Window

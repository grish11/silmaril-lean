module

public import Silmaril.Formats.Bytes
public import Silmaril.Prelude.Bytes.Digits.Defs

/-! Plaintext Parquet framing over a finite file snapshot. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Footer

inductive FramingError where
  | shortFile
  | leadingMagic
  | trailingMagic
  | invalidLength
  | footerLimit
  deriving DecidableEq, Repr

/-- The half-open metadata span. `stop` is the start of the four-octet length word. -/
structure Span where
  start : Nat
  stop : Nat
  deriving DecidableEq, Repr

def magic : Bytes := Bytes.ofList [0x50, 0x41, 0x52, 0x31]

def fileBytes (file : Bytes) (start stop : Nat) : Bytes := ⟨file.data.extract start stop⟩

def footerLength (file : Bytes) : Nat :=
  KBytes.leVal (fileBytes file (file.length - 8) (file.length - 4)).toList

/-- The advertised metadata occupies a nonempty span between the two magic words
and ends immediately before the length word. -/
structure Framed (maxFooterBytes : Nat) (file : Bytes) (span : Span) : Prop where
  leading : fileBytes file 0 4 = magic
  trailing : fileBytes file (file.length - 4) file.length = magic
  start : 4 ≤ span.start
  nonempty : span.start < span.stop
  stop : span.stop + 8 = file.length
  width : span.stop - span.start = footerLength file
  cap : footerLength file ≤ maxFooterBytes

/-- Locate the footer before copying or decoding it. The length is an unsigned
32-bit little-endian count, and the footer must lie after the leading magic. -/
def locate (maxFooterBytes : Nat) (file : Bytes) : Except FramingError Span :=
  if file.length < 12 then .error .shortFile
  else if fileBytes file 0 4 ≠ magic then .error .leadingMagic
  else if fileBytes file (file.length - 4) file.length ≠ magic then .error .trailingMagic
  else
    let count := footerLength file
    let stop := file.length - 8
    if count = 0 ∨ stop - 4 < count then .error .invalidLength
    else if maxFooterBytes < count then .error .footerLimit
    else .ok ⟨stop - count, stop⟩

end Silmaril.Formats.Parquet.Footer

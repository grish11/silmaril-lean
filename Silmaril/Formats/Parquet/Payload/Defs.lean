module

public import Silmaril.Formats.Compression.Snappy.Defs
public import Silmaril.Formats.Compression.Lz4Raw.Defs
public import Silmaril.Formats.Compression.Gzip.Defs
public import Silmaril.Formats.Compression.Inflate.Stream.MemberMachine

/-! # Checked Parquet compression payloads

The caller supplies an exact codec-covered slice. Page and footer metadata,
V2 level prefixes and page checksums belong to the caller.
-/

@[expose] public section

namespace Silmaril.Formats.Parquet.Payload

open Silmaril.Formats.Compression
open Inflate.Stream (MemberMachine RawMachine RawState)

/-- Parquet `CompressionCodec` from the pinned Thrift IDL. -/
inductive Codec where
  | uncompressed | snappy | gzip | lzo | brotli | lz4 | zstd | lz4Raw
  deriving DecidableEq, Repr

def Codec.id : Codec → Int
  | .uncompressed => 0
  | .snappy => 1
  | .gzip => 2
  | .lzo => 3
  | .brotli => 4
  | .lz4 => 5
  | .zstd => 6
  | .lz4Raw => 7

/-- Footer metadata can retain the signed ID and interpret it here. -/
def Codec.ofId : Int → Option Codec
  | 0 => some .uncompressed
  | 1 => some .snappy
  | 2 => some .gzip
  | 3 => some .lzo
  | 4 => some .brotli
  | 5 => some .lz4
  | 6 => some .zstd
  | 7 => some .lz4Raw
  | _ => none

structure Bounds where
  compressedSize : Nat
  compressedLimit : Nat
  expectedSize : Nat
  outputLimit : Nat
  /-- Maximum controller calls for the GZIP member. Used only for GZIP. -/
  gzipCallLimit : Nat
  deriving Repr

inductive Error where
  | compressedLimit
  | outputLimit
  | compressedSizeMismatch
  | outputSizeMismatch
  | unsupportedCodec (id : Int)
  | malformed (codec : Codec)
  | trailingInput (codec : Codec)
  | gzipIncomplete
  deriving DecidableEq, Repr

/-- Interpretation of each supported payload in the corresponding codec model. -/
inductive Decodes (expectedSize : Nat) : Codec → List UInt8 → List UInt8 → Prop where
  | uncompressed (bytes : List UInt8) : Decodes expectedSize .uncompressed bytes bytes
  | snappy {input out : List UInt8} {block : Snappy.Block} :
      Snappy.parseMember expectedSize input = .ok (block, []) →
      Snappy.Denotes [] block.tags out →
      Decodes expectedSize .snappy input out
  | lz4Raw {input out : List UInt8} {block : Lz4Raw.Block} :
      Lz4Raw.Wire input block → Lz4Raw.Denotes none [] block out →
      Decodes expectedSize .lz4Raw input out
  | gzip {input out : List UInt8} :
      Gzip.decoder input = some (out, []) → Decodes expectedSize .gzip input out

namespace Internal

/-- Inspect at most the declared extent and whether any suffix exists. -/
def hasLength : Nat → List UInt8 → Bool
  | 0, [] => true
  | n + 1, _ :: rest => hasLength n rest
  | _, _ => false

def pendingOutput : MemberMachine → Bool
  | .body _ checked =>
    match checked.machine with
    | .storedCopy _ (_ + 1) _ => true
    | .symbols _ _ _ (.emitting _ pending) => pending.remaining > 0
    | _ => false
  | _ => false

def gzipOutputBlocked (expectedSize : Nat) (machine : MemberMachine) : Bool :=
  machine.output.length ≥ expectedSize && pendingOutput machine

def gzipCanStep (expectedSize : Nat) : MemberMachine → Bool
  | .done _ | .bad _ _ => false
  | machine => !gzipOutputBlocked expectedSize machine

/-- All input is already offered. Recompute the remaining output room before
    every call, including when zero room remains for the end marker and trailer. -/
def gzipCall (expectedSize : Nat) (machine : MemberMachine) : RawMachine.Call :=
  ⟨[], 64, expectedSize - machine.output.length⟩

def driveGzip (expectedSize : Nat) : Nat → MemberMachine → MemberMachine
  | 0, machine => machine
  | fuel + 1, machine =>
    if gzipCanStep expectedSize machine then
      driveGzip expectedSize fuel (machine.applyCall .v131 (gzipCall expectedSize machine))
    else machine

/-- Single RFC 1952 member. The bit reservoir must have no prefetched suffix
    and no unread input bytes. A suspended schedule has its own error. -/
def decodeGzip (bounds : Bounds) (input : List UInt8) : Except Error (List UInt8) :=
  let machine := driveGzip bounds.expectedSize bounds.gzipCallLimit (MemberMachine.start .gzip input)
  match machine with
  | .bad _ _ => .error (.malformed .gzip)
  | .done state =>
    if state.reservoir.bits = 0 ∧ state.reservoir.input = [] then .ok state.output
    else .error (.trailingInput .gzip)
  | _ =>
    if gzipOutputBlocked bounds.expectedSize machine then .error .outputSizeMismatch
    else .error .gzipIncomplete

def decodeCodec (bounds : Bounds) (input : List UInt8) : Codec → Except Error (List UInt8)
  | .uncompressed => .ok input
  | .snappy =>
    match Snappy.decode bounds.expectedSize input with
    | .ok out => .ok out
    | .error (.malformed .trailingInput) => .error (.trailingInput .snappy)
    | .error (.limited ..) => .error .outputSizeMismatch
    | .error _ => .error (.malformed .snappy)
  | .gzip => decodeGzip bounds input
  | .lz4Raw =>
    match Lz4Raw.decode
        ⟨bounds.compressedSize, bounds.compressedLimit, bounds.expectedSize, bounds.outputLimit⟩ input with
    | .ok out => .ok out
    | .error .outputSizeMismatch => .error .outputSizeMismatch
    | .error _ => .error (.malformed .lz4Raw)
  | codec => .error (.unsupportedCodec codec.id)

end Internal

/-- Decode an exact compression slice with caller-supplied unsigned lengths.
    Both size caps and the input extent are checked before dispatch. The final
    equality check establishes exact length; the decoders already have output budgets. -/
def decode (bounds : Bounds) (codecId : Int) (input : List UInt8) : Except Error (List UInt8) :=
  if bounds.compressedLimit < bounds.compressedSize then .error .compressedLimit
  else if bounds.outputLimit < bounds.expectedSize then .error .outputLimit
  else if !Internal.hasLength bounds.compressedSize input then .error .compressedSizeMismatch
  else
    match Codec.ofId codecId with
    | none => .error (.unsupportedCodec codecId)
    | some codec => do
      let out ← Internal.decodeCodec bounds input codec
      if out.length = bounds.expectedSize then .ok out else .error .outputSizeMismatch

end Silmaril.Formats.Parquet.Payload

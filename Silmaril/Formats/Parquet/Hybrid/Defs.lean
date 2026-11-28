module

public import Silmaril.Formats.Bytes
public import Silmaril.Prelude.Bytes.Digits.Defs
import Init.Omega

/-! Parquet RLE/bit-packed hybrid encoding for an already delimited values slice.
The caller supplies the bit width, expected value count, and allocation limits. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Hybrid

inductive Error where
  | invalidWidth
  | valueLimit
  | byteLimit
  | truncated
  | headerOverflow
  | noncanonicalHeader
  | invalidRunLength
  | valueOverflow
  | countMismatch
  | trailingBytes
  deriving DecidableEq, Repr

structure Limits where
  values : Nat
  bytes : Nat
  deriving DecidableEq, Repr

/-- Parquet bounds the physical length of either run form to positive signed i32. -/
def runLimit : Nat := 2 ^ 31

def repeatedByteCount (width : Nat) : Nat := (width + 7) / 8

/-- Minimal unsigned base-128 digits, least significant first. -/
def uleb (value : Nat) : List UInt8 :=
  if value < 128 then [UInt8.ofNat value]
  else UInt8.ofNat (128 + value % 128) :: uleb (value / 128)
termination_by value
decreasing_by omega

/-- A bounded ULEB prefix. The terminating group must be nonzero in a
multi-byte header. -/
def readULEB : Nat → List UInt8 → Except Error (Nat × List UInt8)
  | 0, _ => .error .headerOverflow
  | _ + 1, [] => .error .truncated
  | fuel + 1, byte :: rest =>
    if byte.toNat < 128 then .ok (byte.toNat, rest) else
      match readULEB fuel rest with
      | .error err => .error err
      | .ok (high, tail) =>
        if high = 0 then .error .noncanonicalHeader
        else .ok (byte.toNat - 128 + 128 * high, tail)

def readHeader (input : List UInt8) : Except Error (Nat × List UInt8) :=
  match readULEB 5 input with
  | .error err => .error err
  | .ok (code, tail) =>
    if code < 2 * runLimit then .ok (code, tail) else .error .headerOverflow

/-- Read exactly a payload prefix. Its size is checked before interpreting it. -/
def takeExact (size : Nat) (input : List UInt8) : Except Error (List UInt8 × List UInt8) :=
  let octets := input.take size
  if octets.length = size then .ok (octets, input.drop size) else .error .truncated

inductive Run where
  | repeated (count value : Nat)
  | packed (groups : Nat) (payload : List UInt8)
  deriving DecidableEq, Repr

def Run.size : Run → Nat
  | .repeated count _ => count
  | .packed groups _ => groups * 8

/-- Wire-size and value constraints on the two run forms. -/
def Run.Valid (width : Nat) (run : Run) : Prop :=
  0 < run.size ∧ run.size < runLimit ∧
    match run with
    | .repeated _ value => value < 2 ^ width
    | .packed groups payload => payload.length = groups * width

/-- An overshooting packed run may supply up to seven final padding values. -/
def Run.Fits (run : Run) (remaining : Nat) : Prop :=
  match run with
  | .repeated count _ => count ≤ remaining
  | .packed groups _ => groups * 8 ≤ remaining + 7

instance (run : Run) (remaining : Nat) : Decidable (run.Fits remaining) :=
  match run with
  | .repeated _ _ => inferInstanceAs (Decidable (_ ≤ _))
  | .packed _ _ => inferInstanceAs (Decidable (_ ≤ _))

/-- The wire prefix of a run, including its header. -/
def Run.wire (width : Nat) : Run → List UInt8
  | .repeated count value => uleb (count * 2) ++ KBytes.unpack (repeatedByteCount width) value
  | .packed groups payload => uleb (groups * 2 + 1) ++ payload

/-- Scan one run. Packed data stays in byte form until the caller checks
the remaining logical count. -/
def readRun (width : Nat) (input : List UInt8) : Except Error (Run × List UInt8) :=
  match readHeader input with
  | .error err => .error err
  | .ok (code, bytes) =>
    let units := code / 2
    if units = 0 then .error .invalidRunLength
    else if code % 2 = 0 then
      match takeExact (repeatedByteCount width) bytes with
      | .error err => .error err
      | .ok (payload, rest) =>
        let value := KBytes.leVal payload
        if value < 2 ^ width then .ok (.repeated units value, rest) else .error .valueOverflow
    else if units * 8 < runLimit then
      match takeExact (units * width) bytes with
      | .error err => .error err
      | .ok (payload, rest) => .ok (.packed units payload, rest)
    else .error .invalidRunLength

/-- The eight values of a little-endian packed group. The first value occupies
the least significant `width` bits. -/
def unpackGroup (width : Nat) (bytes : List UInt8) : List Nat :=
  let word := KBytes.leVal bytes
  let radix := 2 ^ width
  List.ofFn fun (i : Fin 8) => word / radix ^ i.val % radix

def unpackGroups (width : Nat) : Nat → List UInt8 → List Nat → List Nat
  | 0, _, acc => acc.reverse
  | groups + 1, bytes, acc =>
    let group := unpackGroup width (bytes.take width)
    unpackGroups width groups (bytes.drop width) (group.reverse ++ acc)

def Run.values (width : Nat) : Run → List Nat
  | .repeated count value => List.replicate count value
  | .packed groups payload => unpackGroups width groups payload []

/-- A sequence of runs accounts for all the payload bytes and all the requested
values. Only a final packed run can contribute ignored padding values. -/
inductive Wire (width : Nat) : Nat → List UInt8 → List Nat → Prop where
  | empty : Wire width 0 [] []
  | next {remaining : Nat} {run : Run} {tail : List UInt8} {values : List Nat}
      (positive : 0 < remaining) (valid : run.Valid width) (fits : run.Fits remaining)
      (rest : Wire width (remaining - run.size) tail values) :
      Wire width remaining (run.wire width ++ tail) ((run.values width).take remaining ++ values)

def decodeRuns (width : Nat) :
    Nat → Nat → List UInt8 → List (List Nat) → Except Error (List Nat)
  | _, 0, [], acc => .ok acc.reverse.flatten
  | _, 0, _ :: _, _ => .error .trailingBytes
  | 0, _ + 1, _, _ => .error .countMismatch
  | fuel + 1, remaining + 1, bytes, acc =>
    match readRun width bytes with
    | .error err => .error err
    | .ok (run, tail) =>
      if run.Fits (remaining + 1) then
        decodeRuns width fuel (remaining + 1 - run.size) tail
          ((run.values width).take (remaining + 1) :: acc)
      else .error .countMismatch

/-- Check the external count and byte budget before decoding or expanding runs.
An accepted slice has no remaining bytes. -/
def decode (width expected : Nat) (limits : Limits) (source : Bytes) : Except Error (List Nat) :=
  if 32 < width then .error .invalidWidth
  else if runLimit ≤ expected ∨ limits.values < expected then .error .valueLimit
  else if limits.bytes < source.length then .error .byteLimit
  else decodeRuns width expected expected source.toList []

/-- Write one nonempty RLE run. The caller chooses the run and its framing. -/
def encodeRepeated (width count value : Nat) : Except Error Bytes :=
  if 32 < width then .error .invalidWidth
  else if count = 0 ∨ runLimit ≤ count then .error .invalidRunLength
  else if 2 ^ width ≤ value then .error .valueOverflow
  else .ok (Bytes.ofList ((Run.repeated count value).wire width))

end Silmaril.Formats.Parquet.Hybrid

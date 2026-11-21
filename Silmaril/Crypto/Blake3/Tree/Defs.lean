module

public import Silmaril.Crypto.Blake3.Compression.Defs
public import Init.Data.Nat.Lemmas

@[expose] public section

namespace Silmaril.Crypto.Blake3

inductive Shape where
  | leaf (chunk size : Nat)
  | fork (left right : Shape)
  deriving Repr

def Shape.size : Shape → Nat
  | .leaf _ size => size
  | .fork left right => left.size + right.size

/-- The largest power of two strictly below the number of chunks, expressed in bytes.
Only used for an extent greater than one chunk. -/
def splitBytes (size : Nat) : Nat := 1024 * 2 ^ ((size - 1) / 1024).log2

/-- Canonical left-filled BLAKE3 geometry, including a zero-byte leaf for empty input. -/
def geometry (first size : Nat) : Shape :=
  if small : size ≤ 1024 then .leaf first size
  else
    have positive : 0 < splitBytes size := by
      unfold splitBytes
      exact Nat.mul_pos (by decide) (Nat.pow_pos (by decide))
    have smaller : splitBytes size < size := by
      have bound : 2 ^ ((size - 1) / 1024).log2 ≤ (size - 1) / 1024 :=
        (Nat.le_log2 (by omega)).mp (Nat.le_refl _)
      have := Nat.mul_le_mul_left 1024 bound
      unfold splitBytes
      omega
    .fork (geometry first (splitBytes size))
      (geometry (first + splitBytes size / 1024) (size - splitBytes size))
termination_by size
decreasing_by all_goals omega

def validSize (size : Nat) : Prop := size < 2 ^ 64

instance (size : Nat) : Decidable (validSize size) := inferInstanceAs (Decidable (_ < _))

def Shape.Valid : Shape → Prop
  | .leaf chunk size => size ≤ 1024 ∧ validSize chunk
  | .fork left right => left.Valid ∧ right.Valid

def chunkInput (root first last : Bool) (chunk : Nat) (cv : CV) (bytes : Bytes) : Input :=
  ⟨cv, paddedBlock bytes, if root then 0 else UInt64.ofNat chunk, UInt32.ofNat bytes.length,
    (if first then 1 else 0) + (if last then 2 else 0) + (if root then 8 else 0)⟩

def parentInput (root : Bool) (left right : CV) : Input :=
  ⟨iv, left ++ right, 0, 64, if root then 4 + 8 else 4⟩

/-- `more` counts non-final blocks. A final block can have length zero (empty chunk). -/
inductive Chain (rel : Compression) (root : Bool) (chunk : Nat) :
    Nat → Bool → CV → Bytes → CV → Prop where
  | last {first cv bytes output} : bytes.length ≤ 64 →
      rel (chunkInput root first true chunk cv bytes) output → Chain rel root chunk 0 first cv bytes output
  | step {more first cv bytes mid output} : 64 < bytes.length →
      rel (chunkInput false first false chunk cv (bytes.take 64)) mid →
      Chain rel root chunk more false mid (bytes.drop 64) output →
      Chain rel root chunk (more + 1) first cv bytes output

def chain? (run : Input → Option CV) (root : Bool) (chunk : Nat) :
    Nat → Bool → CV → Bytes → Option CV
  | 0, first, cv, bytes =>
    if bytes.length ≤ 64 then run (chunkInput root first true chunk cv bytes) else none
  | more + 1, first, cv, bytes =>
    if 64 < bytes.length then do
      let mid ← run (chunkInput false first false chunk cv (bytes.take 64))
      chain? run root chunk more false mid (bytes.drop 64)
    else none

inductive Opening where
  | opaque (cv : CV)
  | leaf (bytes : Bytes)
  | fork (left right : Opening)

def leafOK (chunk size : Nat) (bytes : Bytes) : Prop :=
  bytes.length = size ∧ size ≤ 1024 ∧ validSize chunk

instance (chunk size : Nat) (bytes : Bytes) : Decidable (leafOK chunk size bytes) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ validSize chunk))

/-- An opaque CV can be a non-root frontier node; no preimage is asserted. -/
inductive Trace (rel : Compression) : Bool → Shape → Opening → CV → Prop where
  | opaque (shape cv) : Trace rel false shape (.opaque cv) cv
  | leaf {root chunk size bytes output} : leafOK chunk size bytes →
      Chain rel root chunk ((size - 1) / 64) true iv bytes output →
      Trace rel root (.leaf chunk size) (.leaf bytes) output
  | fork {root left right lhs rhs lcv rcv output} :
      Trace rel false left lhs lcv → Trace rel false right rhs rcv →
      rel (parentInput root lcv rcv) output → Trace rel root (.fork left right) (.fork lhs rhs) output

/-- Executable, compositional CV/ROOT evaluation, with a partial compression backend. -/
def eval? (run : Input → Option CV) (root : Bool) (shape : Shape) (opening : Opening) : Option CV :=
  match opening with
  | .opaque cv => if root then none else some cv
  | .leaf bytes => match shape with
    | .leaf chunk size => if leafOK chunk size bytes then
        chain? run root chunk ((size - 1) / 64) true iv bytes else none
    | .fork .. => none
  | .fork lhs rhs => match shape with
    | .fork left right => do
      let lcv ← eval? run false left lhs
      let rcv ← eval? run false right rhs
      run (parentInput root lcv rcv)
    | .leaf .. => none

/-- Fully disclosed opening, splitting a supplied payload by the verifier's geometry. -/
def disclose : Shape → Bytes → Opening
  | .leaf .., bytes => .leaf bytes
  | .fork left right, bytes =>
    .fork (disclose left (bytes.take left.size)) (disclose right (bytes.drop left.size))

def Root (rel : Compression) (size : Nat) (digest : Bytes) (opening : Opening) : Prop :=
  validSize size ∧ ∃ output, Trace rel true (geometry 0 size) opening output ∧ digestBytes output = digest

def root? (run : Input → Option CV) (size : Nat) (opening : Opening) : Option Bytes :=
  if validSize size then (eval? run true (geometry 0 size) opening).map digestBytes else none

def hash? (run : Input → Option CV) (bytes : Bytes) : Option Bytes :=
  root? run bytes.length (disclose (geometry 0 bytes.length) bytes)

end Silmaril.Crypto.Blake3

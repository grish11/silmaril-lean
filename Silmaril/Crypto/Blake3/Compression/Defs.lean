module

public import Init.Data.Vector.Lemmas
public import Init.Data.UInt.Bitwise
public import Silmaril.Crypto.Word

@[expose] public section

namespace Silmaril.Crypto.Blake3

abbrev Bytes := List UInt8
abbrev CV := Vector UInt32 8
abbrev Block := Vector UInt32 16

/-- Actual BLAKE3 primitive arguments after padding and little-endian word loading. -/
structure Input where
  cv : CV
  block : Block
  counter : UInt64
  blockLen : UInt32
  flags : UInt32
  deriving DecidableEq

abbrev Compression := Input → CV → Prop

namespace Compression

def graph (run : Input → Option CV) : Compression := fun input output => run input = some output

/-- A partial implementation can reject inputs but cannot invent transitions. -/
def Consistent (rel : Compression) (run : Input → Option CV) : Prop :=
  ∀ ⦃input output⦄, graph run input output → rel input output

/-- Output uniqueness at a fixed input; not collision resistance. -/
def Canonical (rel : Compression) : Prop :=
  ∀ ⦃input left right⦄, rel input left → rel input right → left = right

/-- Distinct actual inputs with equal observed 256-bit outputs. -/
def Collision (rel : Compression) : Prop :=
  ∃ left right output, left ≠ right ∧ rel left output ∧ rel right output

/-- Input uniqueness on a specified domain, not a claim of global injectivity. -/
def BindingOn (rel : Compression) (domain : Input → Prop) : Prop :=
  ∀ ⦃left right output⦄, domain left → domain right → rel left output → rel right output → left = right

end Compression

def iv : CV := #v[0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
                   0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19]

abbrev packWord := Word.pack32LE

def loadWords {count : Nat} (bytes : Vector UInt8 (4 * count)) : Vector UInt32 count :=
  Vector.ofFn fun pos => packWord bytes[4 * pos.val] bytes[4 * pos.val + 1]
    bytes[4 * pos.val + 2] bytes[4 * pos.val + 3]

def paddedBlock (bytes : Bytes) : Block :=
  loadWords (Vector.ofFn (fun pos : Fin 64 => (bytes[pos.val]?).getD 0))

def wordByte (word : UInt32) (pos : Nat) : UInt8 :=
  let bytes := Word.unpack32LE word
  match pos with
  | 0 => bytes.1
  | 1 => bytes.2.1
  | 2 => bytes.2.2.1
  | 3 => bytes.2.2.2
  | _ => 0

def digestBytes (cv : CV) : Bytes :=
  (Vector.ofFn fun pos : Fin 32 => wordByte cv[pos.val / 4] (pos.val % 4)).toList

def mix (state : Block) (aa bb cc dd : Fin 16) (mx my : UInt32) : Block :=
  let firstA := state.get aa + state.get bb + mx
  let firstD := Word.rotateRight (state.get dd ^^^ firstA) 16
  let firstC := state.get cc + firstD
  let firstB := Word.rotateRight (state.get bb ^^^ firstC) 12
  let lastA := firstA + firstB + my
  let lastD := Word.rotateRight (firstD ^^^ lastA) 8
  let lastC := firstC + lastD
  let lastB := Word.rotateRight (firstB ^^^ lastC) 7
  state.set aa.val lastA |>.set bb.val lastB |>.set cc.val lastC |>.set dd.val lastD

def round (state msg : Block) : Block :=
  let state := mix state 0 4  8 12 msg[0]  msg[1]
  let state := mix state 1 5  9 13 msg[2]  msg[3]
  let state := mix state 2 6 10 14 msg[4]  msg[5]
  let state := mix state 3 7 11 15 msg[6]  msg[7]
  let state := mix state 0 5 10 15 msg[8]  msg[9]
  let state := mix state 1 6 11 12 msg[10] msg[11]
  let state := mix state 2 7  8 13 msg[12] msg[13]
  mix state 3 4  9 14 msg[14] msg[15]

def permute (msg : Block) : Block :=
  let permutation : Vector (Fin 16) 16 := #v[2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8]
  Vector.ofFn fun pos => msg.get (permutation.get pos)

/-- Scalar BLAKE3 compression, including both feed-forward halves. -/
def compressWide (input : Input) : Block :=
  let initial := input.cv ++ #v[iv[0], iv[1], iv[2], iv[3], input.counter.toUInt32,
    (input.counter >>> 32).toUInt32, input.blockLen, input.flags]
  let (final, _) := (List.range 7).foldl
    (fun (state, msg) _ => (round state msg, permute msg)) (initial, input.block)
  Vector.ofFn fun pos => if low : pos.val < 8 then final[pos.val] ^^^ final[pos.val + 8]
    else final[pos.val] ^^^ input.cv[pos.val - 8]

/-- Chaining and the first 32 ROOT bytes observe the low half, on different inputs. -/
def compress32 (input : Input) : CV :=
  Vector.ofFn fun pos => (compressWide input)[pos.val]

def concrete : Compression := Compression.graph (some ∘ compress32)

end Silmaril.Crypto.Blake3

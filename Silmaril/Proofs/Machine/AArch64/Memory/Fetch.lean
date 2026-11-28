module

public import Silmaril.Machine.AArch64.Memory.Defs

/-!
# AArch64 little-endian bytes and instruction fetch: proofs

Proofs for `Silmaril.Machine.AArch64.Memory.Thms`.

Method. A little-endian byte list and a number are related through one fact, stated over
`Nat` so that no width `8 * n` appears in a type: byte `i` of a number `x` is
`x / 2 ^ (8 * i) % 256`. `valueLE_div_mod` says the bytes of `valueLE bytes` are `bytes`;
`valueLE_eq_mod` says a list holding the bytes of `x` denotes `x` cut to its length. The
two round trips between `bytesLE` and `ofBytesLE` follow by `BitVec.eq_of_toNat_eq`.
`toNat_ofBytesLE` and `valueLE_bytesLE` then say what number each side denotes:
`valueLE_lt` shows that nothing is cut off for exactly `n` bytes.

For `fetchWord_installWords`, `wordsBytes_getElem?` locates byte `j` of word `i` at index
`4 * i + j` of `wordsBytes words`; `Memory.install_get` and `Memory.readWith_eq` then give
the four bytes read back. The address `base + 4 * i` does not wrap, because the permission
check on its four bytes (`Memory.checkSpan_iff`) already puts them below `2^64`.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.AArch64.Memory

open Silmaril.Process (Memory Byte Access)
open Silmaril.Machine.AArch64

/-! ## Little-endian bytes -/

/-- `bytesLE n` gives `n` bytes. -/
theorem bytesLE_length (n : Nat) (v : BitVec (8 * n)) : (bytesLE n v).length = n := by
  simp [bytesLE]

/-- Byte `i` is bits `8i+7 : 8i` of the value. -/
theorem bytesLE_getElem (n : Nat) (v : BitVec (8 * n)) (i : Nat) (h : i < (bytesLE n v).length) :
    (bytesLE n v)[i] = v.extractLsb' (8 * i) 8 := by
  simp [bytesLE]

/-- `k` bytes denote a number below `2 ^ (8 * k)`. -/
theorem valueLE_lt (bytes : List Byte) : valueLE bytes < 2 ^ (8 * bytes.length) := by
  induction bytes with
  | nil => simp [valueLE]
  | cons byte rest ih =>
    have := byte.isLt
    rw [valueLE, List.length_cons, show 8 * (rest.length + 1) = 8 + 8 * rest.length by omega,
      Nat.pow_add]
    omega

/-- Dividing by `2 ^ (8 * (i + 1))` is dividing by 256 and then by `2 ^ (8 * i)`. -/
theorem div_pow_succ (x i : Nat) : x / 2 ^ (8 * (i + 1)) = x / 256 / 2 ^ (8 * i) := by
  rw [show 8 * (i + 1) = 8 + 8 * i by omega, Nat.pow_add, Nat.div_div_eq_div_mul]

/-- Byte `i` of the number that `bytes` denote is `bytes[i]`. -/
theorem valueLE_div_mod (bytes : List Byte) (i : Nat) (h : i < bytes.length) :
    valueLE bytes / 2 ^ (8 * i) % 256 = bytes[i].toNat := by
  induction bytes generalizing i with
  | nil => simp at h
  | cons byte rest ih =>
    have := byte.isLt
    cases i with
    | zero =>
      simp only [valueLE, Nat.mul_zero, Nat.pow_zero, Nat.div_one, List.getElem_cons_zero]
      omega
    | succ i =>
      have tail : (byte.toNat + 256 * valueLE rest) / 256 = valueLE rest := by omega
      rw [valueLE, div_pow_succ, tail, List.getElem_cons_succ]
      exact ih i (by simpa using h)

/-- A list whose element `i` is byte `i` of `x` denotes `x` cut to `8 * length` bits. -/
theorem valueLE_eq_mod (bytes : List Byte) (x : Nat)
    (digits : ∀ i (h : i < bytes.length), bytes[i].toNat = x / 2 ^ (8 * i) % 256) :
    valueLE bytes = x % 2 ^ (8 * bytes.length) := by
  induction bytes generalizing x with
  | nil => simp [valueLE, Nat.mod_one]
  | cons byte rest ih =>
    have head := digits 0 (Nat.zero_lt_succ _)
    rw [List.getElem_cons_zero, Nat.mul_zero, Nat.pow_zero, Nat.div_one] at head
    have tail : ∀ i (h : i < rest.length), rest[i].toNat = x / 256 / 2 ^ (8 * i) % 256 := by
      intro i h
      have next := digits (i + 1) (Nat.succ_lt_succ h)
      rwa [List.getElem_cons_succ, div_pow_succ] at next
    rw [valueLE, ih (x / 256) tail, head, List.length_cons,
      show 8 * (rest.length + 1) = 8 + 8 * rest.length by omega, Nat.pow_add, Nat.mod_mul]

/-- Writing a value as bytes and reading the bytes back gives the value. -/
theorem ofBytesLE_bytesLE (n : Nat) (v : BitVec (8 * n)) : ofBytesLE n (bytesLE n v) = v := by
  apply BitVec.eq_of_toNat_eq
  have digits : ∀ i (h : i < (bytesLE n v).length),
      (bytesLE n v)[i].toNat = v.toNat / 2 ^ (8 * i) % 256 := by
    intro i h
    rw [bytesLE_getElem, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [ofBytesLE, BitVec.toNat_ofNat, valueLE_eq_mod _ v.toNat digits, bytesLE_length,
    Nat.mod_mod, Nat.mod_eq_of_lt v.isLt]

/-- Reading `n` bytes as a value and writing the value as bytes gives the bytes. -/
theorem bytesLE_ofBytesLE {n : Nat} (bytes : List Byte) (h : bytes.length = n) :
    bytesLE n (ofBytesLE n bytes) = bytes := by
  subst h
  apply List.ext_getElem (bytesLE_length _ _)
  intro i h1 h2
  apply BitVec.eq_of_toNat_eq
  rw [bytesLE_getElem, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, ofBytesLE,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (valueLE_lt bytes)]
  exact valueLE_div_mod bytes i h2

/-- The value of exactly `n` bytes denotes the same number as the bytes. -/
theorem toNat_ofBytesLE {n : Nat} (bytes : List Byte) (h : bytes.length = n) :
    (ofBytesLE n bytes).toNat = valueLE bytes := by
  subst h
  rw [ofBytesLE, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (valueLE_lt bytes)]

/-- The bytes of a value denote the number of the value. -/
theorem valueLE_bytesLE (n : Nat) (v : BitVec (8 * n)) : valueLE (bytesLE n v) = v.toNat := by
  rw [← toNat_ofBytesLE (bytesLE n v) (bytesLE_length n v), ofBytesLE_bytesLE]

/-- The number a four-byte word denotes. -/
theorem ofBytesLE_four_toNat (b0 b1 b2 b3 : Byte) :
    (ofBytesLE 4 [b0, b1, b2, b3]).toNat =
      b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat := by
  have := b0.isLt
  have := b1.isLt
  have := b2.isLt
  have := b3.isLt
  simp only [ofBytesLE, valueLE, BitVec.toNat_ofNat]
  omega

/-- A four-byte word as a concatenation: the last byte is the most significant. -/
theorem ofBytesLE_four_append (b0 b1 b2 b3 : Byte) :
    (ofBytesLE 4 [b0, b1, b2, b3] : BitVec 32) = b3 ++ b2 ++ b1 ++ b0 := by
  apply BitVec.eq_of_toNat_eq
  have := b0.isLt
  have := b1.isLt
  have := b2.isLt
  have := b3.isLt
  rw [ofBytesLE_four_toNat]
  simp only [BitVec.toNat_append]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega), ← Nat.shiftLeft_add_eq_or_of_lt (by omega),
    ← Nat.shiftLeft_add_eq_or_of_lt (by omega)]
  simp only [Nat.shiftLeft_eq]
  omega

/-! ## Checked little-endian reads -/

/-- A read gives `value` exactly when the checked byte read gives the bytes of `value`. -/
theorem readLE_eq_some_iff {memory : Memory} {access : Access} {address : BitVec 64} {n : Nat}
    {value : BitVec (8 * n)} :
    readLE memory access address n = some value ↔
      memory.readWith access address.toNat n = some (bytesLE n value) := by
  rw [readLE, Option.map_eq_some_iff]
  constructor
  · rintro ⟨bytes, read, rfl⟩
    rw [read, bytesLE_ofBytesLE bytes (Memory.readWith_length read)]
  · intro read
    exact ⟨_, read, ofBytesLE_bytesLE n value⟩

/-! ## Instruction fetch -/

/-- The bytes of a list of words starting with `word`. -/
theorem wordsBytes_cons (word : BitVec 32) (words : List (BitVec 32)) :
    wordsBytes (word :: words) = bytesLE 4 word ++ wordsBytes words :=
  List.flatMap_cons

/-- Each word gives four bytes. -/
theorem wordsBytes_length (words : List (BitVec 32)) :
    (wordsBytes words).length = 4 * words.length := by
  induction words with
  | nil => rfl
  | cons word words ih =>
    rw [wordsBytes_cons, List.length_append, bytesLE_length, ih, List.length_cons]
    omega

/-- Byte `j` of word `i` is at index `4 * i + j`. -/
theorem wordsBytes_getElem? (words : List (BitVec 32)) (i j : Nat) (hi : i < words.length)
    (hj : j < 4) : (wordsBytes words)[4 * i + j]? = (bytesLE 4 words[i])[j]? := by
  induction words generalizing i with
  | nil => simp at hi
  | cons word words ih =>
    cases i with
    | zero =>
      rw [wordsBytes_cons, Nat.mul_zero, Nat.zero_add, List.getElem_cons_zero,
        List.getElem?_append_left (by rw [bytesLE_length]; exact hj)]
    | succ i =>
      rw [wordsBytes_cons, List.getElem?_append_right (by rw [bytesLE_length]; omega),
        bytesLE_length, show 4 * (i + 1) + j - 4 = 4 * i + j by omega, List.getElem_cons_succ]
      exact ih i (by simpa using hi)

/-- After installing instruction words at `base`, a fetch at `base + 4 * i` gives word `i`,
provided the four bytes are executable. -/
theorem fetchWord_installWords (memory : Memory) (base : BitVec 64) (words : List (BitVec 32))
    (i : Nat) (hi : i < words.length)
    (permitted : memory.Permitted .execute (base.toNat + 4 * i) 4) :
    fetchWord { memory with bytes := Memory.install memory.bytes base.toNat (wordsBytes words) }
      (base + BitVec.ofNat 64 (4 * i)) = some words[i] := by
  have below : base.toNat + 4 * i + 4 ≤ 2 ^ 64 :=
    ((Memory.checkSpan_iff memory .execute (base.toNat + 4 * i) 4).mp permitted).2.1
  have address : (base + BitVec.ofNat 64 (4 * i)).toNat = base.toNat + 4 * i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have installed : ∀ j (h : j < (bytesLE 4 words[i]).length),
      (Memory.install memory.bytes base.toNat (wordsBytes words)).get? (base.toNat + 4 * i + j) =
        some ((bytesLE 4 words[i])[j]) := by
    intro j h
    have hj : j < 4 := by rwa [bytesLE_length] at h
    have inside : 4 * i + j < (wordsBytes words).length := by rw [wordsBytes_length]; omega
    have located := wordsBytes_getElem? words i j hi hj
    rw [List.getElem?_eq_getElem inside, List.getElem?_eq_getElem h] at located
    rw [Nat.add_assoc, Memory.install_get _ _ _ _ inside, Option.some.inj located]
  have read := Memory.readWith_eq
    { memory with bytes := Memory.install memory.bytes base.toNat (wordsBytes words) } .execute
    (base.toNat + 4 * i) (bytesLE 4 words[i]) (by rw [bytesLE_length]; exact permitted) installed
  rw [bytesLE_length] at read
  exact (readLE_eq_some_iff (n := 4)).mpr (address ▸ read)

end Silmaril.Proofs.Machine.AArch64.Memory

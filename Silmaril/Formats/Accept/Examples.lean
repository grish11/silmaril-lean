module

public import Silmaril.Formats.Accept.Thms
public import Mathlib.Computability.DFA

/-! # Byte languages: examples and tests

* Membership of every bytes-like representation (`List UInt8`, `Array UInt8`, `ByteArray`,
  `KBytes` leaves and ropes, `Formats.Bytes`) in one byte language, decided by the kernel.
* A Mathlib `DFA` over bytes (strings without a `NUL` byte) is a byte language as it stands;
  a specification that also bounds the length is sound for the bounded acceptor, and the
  DFA's language is complete for it (`Lang.Sound`, `Lang.Complete`).
* CSLib: a byte language is a CSLib `Acceptor` whose language is itself.
-/

@[expose] public section

namespace Silmaril.Formats.Accept.Examples

open Silmaril.Formats.Accept

/-- Strings of even length. -/
def even : ByteLang := {bs | bs.length % 2 = 0}

instance (bs : List UInt8) : Decidable (bs ∈ even) := inferInstanceAs (Decidable (_ = _))

example : ([1, 2] : List UInt8) ∈ even := by decide

example : even.Accepts ([1, 2] : List UInt8) := by
  rw [ByteLang.accepts_list]; decide

example : even.Accepts (#[1, 2, 3, 4] : Array UInt8) := by
  rw [ByteLang.accepts_array]; decide

example : even.Accepts (ByteArray.mk #[7, 7]) := by
  rw [ByteLang.accepts_byteArray]; decide

/-- A `KBytes` leaf: two bytes packed into one number. -/
example : even.Accepts (KBytes.leaf 2 0x0201) := by
  rw [ByteLang.accepts_kbytes]; decide +kernel

/-- A `KBytes` rope: membership sees the bytes, not the tree. -/
example : even.Accepts (KBytes.leaf 1 5 ++ KBytes.leaf 3 0x030201) := by
  rw [ByteLang.accepts_kbytes]; decide +kernel

example : ¬ even.Accepts (KBytes.ofList [1, 2, 3]) := by
  rw [ByteLang.accepts_kbytes, KBytes.toList_ofList]; decide

/-- A rope and its `ByteArray` are accepted together. -/
example (t : KBytes) (h : even.Accepts t) : even.Accepts t.toByteArray :=
  (ByteLang.accepts_toByteArray even t).2 h

example : even.Accepts (Formats.Bytes.ofList [0, 0]) := by
  rw [ByteLang.accepts_bytes, Formats.Bytes.toList_ofList]; decide

/-- The even-length checker decides `even` (the Bool-checker vocabulary of
`Silmaril.Semantics.Accept`). -/
def evenCheck (bs : List UInt8) : Bool := bs.length % 2 == 0

example : Silmaril.Accept.Decides evenCheck even :=
  Lang.exact_ofBool_iff.1 (by ext bs; simp [evenCheck, even, Silmaril.Accept.ofBool])

example : ByteLang.Accepts (Silmaril.Accept.ofBool evenCheck) (KBytes.leaf 4 0) := by
  rw [ByteLang.accepts_ofBool]; decide +kernel

/-! ## A DFA over bytes -/

/-- Strings without a `NUL` byte: state `true` until a `0` is read. -/
def noNul : DFA UInt8 Bool where
  step s b := s && b != 0
  start := true
  accept := {true}

example : ByteLang.Accepts noNul.accepts "hi".toUTF8 := by
  rw [ByteLang.accepts_byteArray, DFA.mem_accepts]
  show noNul.eval _ = true
  decide +kernel

example : ¬ ByteLang.Accepts noNul.accepts (ByteArray.mk #[104, 0, 105]) := by
  rw [ByteLang.accepts_byteArray, DFA.mem_accepts]
  show ¬ noNul.eval _ = true
  decide +kernel

/-- C strings of at most `n` bytes. -/
def cstr (n : Nat) : ByteLang := noNul.accepts ⊓ {bs | bs.length ≤ n}

/-- The bounded acceptor is sound for the DFA's language ... -/
example (n : Nat) : Lang.Sound (cstr n) noNul.accepts := fun _ h => h.1

/-- ... which is complete for it. -/
example (n : Nat) : Lang.Complete noNul.accepts (cstr n) := fun _ h => h.1

/-- Soundness is preserved by concatenation: two bounded strings are a string of two DFA
strings. -/
example (n : Nat) : Lang.Sound (cstr n * cstr n) (noNul.accepts * noNul.accepts) :=
  ByteLang.sound_mul (fun _ h => h.1) (fun _ h => h.1)

/-! ## CSLib -/

example : Cslib.Automata.Acceptor.language even = even := ByteLang.acceptor_language even

example : ByteLang.Accepts (Cslib.Automata.Acceptor.language even) (KBytes.ofList [9, 9]) := by
  rw [ByteLang.accepts_language]
  show (KBytes.ofList [9, 9]).toList ∈ even
  rw [KBytes.toList_ofList]; decide

end Silmaril.Formats.Accept.Examples

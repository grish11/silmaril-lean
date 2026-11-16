module

public import Silmaril.Wasm.Game.Accept.Thms
public import Silmaril.Semantics.Accept.Thms
public import Silmaril.Formats.Accept.Bounds.Thms

/-! # Byte-length bounds of module acceptors

What `accept(ptr, len)` can observe, exactly:

* **The `i32` encoding bounds the length strictly**: `len` is an `i32`, so an observed
  segment has `len.toNat < 2 ^ 32` bytes (`Callout.length_lt_of_bytes32`), that is at most
  `2 ^ 32 - 1` (`length_le_of_bytes32`). The `memory64` form gives `< 2 ^ 64`
  (`length_lt_of_bytes64`). These are bounds of the argument encoding alone; they do not
  assume anything about the memory's size.
* **The segment lies in the memory**: `ptr + len ≤ size` (`add_length_le_of_segment`), so a
  segment is never longer than the memory it is read from. A memory of a 32-bit module has
  at most `65536` pages of `65536` bytes, so `size ≤ 2 ^ 32`: this bound alone would allow
  `2 ^ 32` bytes, one more than the `i32` bound.
* **Zero length**: `accept(ptr, 0)` observes `[]` exactly when `ptr ≤ size`; the pointer may be
  one past the end, `ptr = size` (`bytes32_zero_iff`). The canonical ABI's bounds check
  (`ptr + len * 1 > size` traps) agrees.
* **The decoder is complete**: every in-bounds segment is observed (`bytes32_of_le`), so the
  bounds above are the only constraints the decoder imposes.
* **Consequences for the accepted sets**: every byte language of a module through
  `accept(ptr: i32, len: i32)` is a set of strings shorter than `2 ^ 32`
  (`bytesLang_length_lt`), and so **finite** (`bytesLang_finite`); it is unchanged by the
  size filter at `2 ^ 32 - 1` (`upTo_bytesLang`). Likewise for `memory64` with `2 ^ 64`.
  Finiteness holds for every module, every profile and every environment class: it is a
  property of the decoder, not of the program.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.Accept

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Formats.Accept

namespace Callout

/-- A segment fits in the memory it is read from. -/
theorem add_length_le_of_segment {o : Callout} {ptr len : Nat} {bs : List UInt8}
    (h : o.segment ptr len = some bs) : ∃ mem, o.mem = some mem ∧ ptr + bs.length ≤ mem.size := by
  obtain ⟨mem, b, hm, hb, rfl⟩ := segment_eq_some_iff.1 h
  obtain ⟨hle, -⟩ := (Execution.Memory.readBytes_eq_some_iff _ _ _ _).1 hb
  refine ⟨mem, hm, ?_⟩
  rw [Array.length_toList, show b.data.size = b.size from rfl,
    Execution.Memory.readBytes_size mem b _ _ hb]
  exact hle

/-- **Every in-bounds segment is observed** (the decoder is complete). -/
theorem segment_of_le {imp : String × String} {args : List Val} {mem : ByteArray} {ptr len : Nat}
    (h : ptr + len ≤ mem.size) :
    (⟨imp, args, some mem⟩ : Callout).segment ptr len =
      some (mem.data.toList.extract ptr (ptr + len)) := by
  simp [segment, Execution.Memory.readBytes, h, ByteArray.data_extract]

/-- `accept(ptr: i32, len: i32)` observes fewer than `2 ^ 32` bytes. -/
theorem length_lt_of_bytes32 {o : Callout} {bs : List UInt8} (h : o.bytes32 = some bs) :
    bs.length < 2 ^ 32 := by
  obtain ⟨p, n, -, hs⟩ := bytes32_eq_some_iff.1 h
  rw [length_of_segment hs]
  exact n.isLt

/-- The same bound, non-strictly: at most `2 ^ 32 - 1` bytes. -/
theorem length_le_of_bytes32 {o : Callout} {bs : List UInt8} (h : o.bytes32 = some bs) :
    bs.length ≤ 2 ^ 32 - 1 := by
  have := length_lt_of_bytes32 h; omega

theorem bytes64_eq_some_iff {o : Callout} {bs : List UInt8} :
    o.bytes64 = some bs ↔ ∃ p n : BitVec 64,
      args2 i64? o.args = some (p, n) ∧ o.segment p.toNat n.toNat = some bs := by
  simp only [bytes64, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists]

/-- `accept(ptr: i64, len: i64)` observes fewer than `2 ^ 64` bytes. -/
theorem length_lt_of_bytes64 {o : Callout} {bs : List UInt8} (h : o.bytes64 = some bs) :
    bs.length < 2 ^ 64 := by
  obtain ⟨p, n, -, hs⟩ := bytes64_eq_some_iff.1 h
  rw [length_of_segment hs]
  exact n.isLt

/-- **Zero-length calls**: `accept(ptr, 0)` observes `[]` iff `ptr ≤ size` (one past the end
included), and nothing otherwise. -/
theorem bytes32_zero_iff {imp : String × String} {p : BitVec 32} {mem : ByteArray} :
    (⟨imp, [.num ⟨.int .i32, p⟩, .num ⟨.int .i32, 0⟩], some mem⟩ : Callout).bytes32 = some [] ↔
      p.toNat ≤ mem.size := by
  change Option.map (·.data.toList) (Execution.Memory.readBytes mem p.toNat 0) = _ ↔ _
  unfold Execution.Memory.readBytes
  split_ifs with h
  · simp only [Nat.add_zero] at h
    simp [h]
  · simp only [Nat.add_zero] at h
    simp [h]

/-- An in-bounds `accept(ptr: i32, len: i32)` observes its segment. -/
theorem bytes32_of_le {imp : String × String} {p n : BitVec 32} {mem : ByteArray}
    (h : p.toNat + n.toNat ≤ mem.size) :
    (⟨imp, [.num ⟨.int .i32, p⟩, .num ⟨.int .i32, n⟩], some mem⟩ : Callout).bytes32 =
      some (mem.data.toList.extract p.toNat (p.toNat + n.toNat)) :=
  bytes32_eq_some_iff.2 ⟨p, n, rfl, segment_of_le h⟩

end Callout

variable {P : Profile} {Envs : Store Nat → SEnv UImp → Prop} {k : Nat} {imp : String × String}
  {m : Module}

/-- Strings accepted through `accept(ptr: i32, len: i32)` are shorter than `2 ^ 32`. -/
theorem accepted_bytes32_length_lt {w : List UInt8}
    (h : w ∈ accepted Callout.bytes32 P Envs k imp m) : w.length < 2 ^ 32 :=
  h.elim fun _ ⟨_, _, hd⟩ => Callout.length_lt_of_bytes32 hd

/-- Strings accepted through `accept(ptr: i64, len: i64)` are shorter than `2 ^ 64`. -/
theorem accepted_bytes64_length_lt {w : List UInt8}
    (h : w ∈ accepted Callout.bytes64 P Envs k imp m) : w.length < 2 ^ 64 :=
  h.elim fun _ ⟨_, _, hd⟩ => Callout.length_lt_of_bytes64 hd

theorem bytesLang_length_lt {w : List UInt8} (h : w ∈ bytesLang P m imp) : w.length < 2 ^ 32 :=
  accepted_bytes32_length_lt h

theorem bytes64Lang_length_lt {w : List UInt8} (h : w ∈ bytes64Lang P m imp) :
    w.length < 2 ^ 64 :=
  accepted_bytes64_length_lt h

/-- **Every 32-bit byte language of a module is finite.** -/
theorem accepted_bytes32_finite : (accepted Callout.bytes32 P Envs k imp m).Finite :=
  ByteLang.finite_of_length_lt (n := 2 ^ 32) fun _ h => accepted_bytes32_length_lt h

/-- **Every 64-bit byte language of a module is finite.** -/
theorem accepted_bytes64_finite : (accepted Callout.bytes64 P Envs k imp m).Finite :=
  ByteLang.finite_of_length_lt (n := 2 ^ 64) fun _ h => accepted_bytes64_length_lt h

theorem bytesLang_finite : (bytesLang P m imp : Set (List UInt8)).Finite := accepted_bytes32_finite

theorem bytes64Lang_finite : (bytes64Lang P m imp : Set (List UInt8)).Finite :=
  accepted_bytes64_finite

/-- The size filter at the `i32` bound `2 ^ 32 - 1` (`≤`) leaves a byte language unchanged. -/
theorem upTo_bytesLang :
    Silmaril.Accept.upTo List.length (2 ^ 32 - 1) (bytesLang P m imp) = bytesLang P m imp :=
  ByteLang.upTo_eq_self fun _ h => by have := bytesLang_length_lt h; omega

/-- The size filter at `2 ^ 64 - 1` leaves a `memory64` byte language unchanged. -/
theorem upTo_bytes64Lang :
    Silmaril.Accept.upTo List.length (2 ^ 64 - 1) (bytes64Lang P m imp) = bytes64Lang P m imp :=
  ByteLang.upTo_eq_self fun _ h => by have := bytes64Lang_length_lt h; omega

end Silmaril.Wasm.Game.Accept

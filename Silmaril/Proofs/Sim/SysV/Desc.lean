module

public import Silmaril.Sim.SysV.Defs

/-!
# The descriptor serialization

* `decodeWords_flatMap`: little-endian words read back.
* **`decode_encode`**: a valid descriptor is read back from its bytes.
* `encode_length`, `resultOffset_le`: the result area lies inside the encoding, after the
  arguments (its three words are the last 24 bytes).
-/

@[expose] public section

namespace Silmaril.Sim.SysV

open Silmaril.X86 (Word Byte)
open Silmaril.Machine.LittleEndian (encodeWords)

theorem decodeWords_flatMap (ws : List Word) :
    decodeWords (ws.flatMap fun w => encodeWords [w]) = some ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have h := Silmaril.X86.wordOfBytes?_encodeWords w
    rw [Silmaril.X86.encodeWords_singleton] at h
    rw [List.flatMap_cons, Silmaril.X86.encodeWords_singleton]
    simp only [List.cons_append, decodeWords, h, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def, List.nil_append, ih]

theorem regArgs_length (d : SysVCall) (h : d.intArgs.length ≤ 6) : d.regArgs.length = 6 := by
  simp only [SysVCall.regArgs, List.length_append, List.length_replicate]
  omega

/-- **Round trip**: a valid descriptor is decoded from its encoding. -/
theorem decode_encode (d : SysVCall) (hd : d.Valid) : SysVCall.decode d.encode = some d := by
  obtain ⟨hk, hn⟩ := hd
  have hlen := regArgs_length d hk
  have hk64 : (BitVec.ofNat 64 d.intArgs.length).toNat = d.intArgs.length := by
    rw [BitVec.toNat_ofNat]; omega
  have hn64 : (BitVec.ofNat 64 d.stackArgs.length).toNat = d.stackArgs.length := by
    rw [BitVec.toNat_ofNat]; omega
  rw [SysVCall.decode, SysVCall.encode, decodeWords_flatMap, Option.bind_some, SysVCall.words]
  have hd6 : (d.regArgs ++ BitVec.ofNat 64 d.stackArgs.length :: (d.stackArgs ++ [0, 0, 0])).drop 6 =
      BitVec.ofNat 64 d.stackArgs.length :: (d.stackArgs ++ [0, 0, 0]) :=
    List.drop_left' hlen
  have ht6 : (d.regArgs ++ BitVec.ofNat 64 d.stackArgs.length :: (d.stackArgs ++ [0, 0, 0])).take 6 =
      d.regArgs := List.take_left' hlen
  simp only [List.cons_append, List.append_assoc] at hd6 ht6 ⊢
  simp only [ofWords, hd6, ht6, hk64, hn64, hk, ite_true, List.length_append, List.length_cons,
    List.length_nil]
  rw [List.take_left' rfl, SysVCall.regArgs, List.take_left' rfl]

theorem encode_length (d : SysVCall) (hd : d.Valid) :
    d.encode.length = 8 * (12 + d.stackArgs.length) := by
  have hlen := regArgs_length d hd.1
  simp only [SysVCall.encode, SysVCall.words, List.length_flatMap,
    Silmaril.X86.length_encodeWords_singleton]
  simp [List.sum_replicate_nat, hlen]
  omega

/-- The result area (three words) is the end of the encoding. -/
theorem resultOffset_add (d : SysVCall) (hd : d.Valid) : d.resultOffset + 24 = d.encode.length := by
  rw [encode_length d hd, SysVCall.resultOffset]; omega

end Silmaril.Sim.SysV

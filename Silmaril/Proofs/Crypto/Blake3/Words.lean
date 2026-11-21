module

public import Silmaril.Crypto.Blake3.Tree.Defs
import Init.Data.Vector.OfFn

public section

namespace Silmaril.Proofs.Crypto.Blake3

open Silmaril.Crypto.Blake3

private theorem unpack (aa bb cc dd : UInt8) :
    wordByte (packWord aa bb cc dd) 0 = aa ∧ wordByte (packWord aa bb cc dd) 1 = bb ∧
    wordByte (packWord aa bb cc dd) 2 = cc ∧ wordByte (packWord aa bb cc dd) 3 = dd :=
  let eq := Silmaril.Crypto.Word.unpack32LE_pack32LE aa bb cc dd
  ⟨congrArg (·.1) eq, congrArg (·.2.1) eq, congrArg (·.2.2.1) eq, congrArg (·.2.2.2) eq⟩

private theorem repack (word : UInt32) :
    packWord (wordByte word 0) (wordByte word 1) (wordByte word 2) (wordByte word 3) = word :=
  Silmaril.Crypto.Word.pack32LE_unpack32LE word

private theorem load_inj {count : Nat} {left right : Vector UInt8 (4 * count)}
    (eq : loadWords left = loadWords right) : left = right := by
  apply Vector.ext
  intro pos bound
  have index : pos / 4 < count := by omega
  have b0 : 4 * (pos / 4) < 4 * count := by omega
  have b1 : 4 * (pos / 4) + 1 < 4 * count := by omega
  have b2 : 4 * (pos / 4) + 2 < 4 * count := by omega
  have b3 : 4 * (pos / 4) + 3 < 4 * count := by omega
  have words := congrArg (fun (words : Vector UInt32 count) => words[pos / 4]) eq
  simp only [loadWords, Vector.getElem_ofFn] at words
  have decode (vec : Vector UInt8 (4 * count)) :
      wordByte (packWord (vec[4 * (pos / 4)]'b0) (vec[4 * (pos / 4) + 1]'b1)
        (vec[4 * (pos / 4) + 2]'b2) (vec[4 * (pos / 4) + 3]'b3)) (pos % 4) = vec[pos] := by
    obtain ⟨zero, one, two, three⟩ := unpack (vec[4 * (pos / 4)]'b0) (vec[4 * (pos / 4) + 1]'b1)
      (vec[4 * (pos / 4) + 2]'b2) (vec[4 * (pos / 4) + 3]'b3)
    by_cases h0 : pos % 4 = 0
    · simpa only [h0, show 4 * (pos / 4) = pos by omega] using zero
    by_cases h1 : pos % 4 = 1
    · simpa only [h1, show 4 * (pos / 4) + 1 = pos by omega] using one
    by_cases h2 : pos % 4 = 2
    · simpa only [h2, show 4 * (pos / 4) + 2 = pos by omega] using two
    · simpa only [show pos % 4 = 3 by omega, show 4 * (pos / 4) + 3 = pos by omega] using three
  exact (decode left).symm.trans ((congrArg (fun word => wordByte word (pos % 4)) words).trans (decode right))

theorem padded_inj {left right : Bytes} (len : left.length = right.length)
    (bound : left.length ≤ 64) (eq : paddedBlock left = paddedBlock right) : left = right := by
  have pads := load_inj eq
  apply List.ext_getElem len
  intro pos inLeft inRight
  have el := congrArg (fun (vec : Vector UInt8 64) => vec[pos]'(by omega)) pads
  simpa only [Vector.getElem_ofFn, List.getElem?_eq_getElem inLeft, List.getElem?_eq_getElem inRight,
    Option.getD_some] using el

theorem digest_inj {left right : CV} (eq : digestBytes left = digestBytes right) : left = right := by
  apply Vector.ext
  intro pos bound
  have byteEq (off : Nat) (small : off < 4) : wordByte left[pos] off = wordByte right[pos] off := by
    have atByte := congrArg (fun (bytes : Bytes) => bytes[4 * pos + off]?) eq
    have inVec : 4 * pos + off < 32 := by omega
    simpa only [digestBytes, Vector.getElem?_toList, Vector.getElem?_eq_getElem inVec,
      Vector.getElem_ofFn, show (4 * pos + off) / 4 = pos by omega,
      show (4 * pos + off) % 4 = off by omega, Option.some.injEq] using atByte
  rw [← repack left[pos], ← repack right[pos], byteEq 0 (by decide), byteEq 1 (by decide),
    byteEq 2 (by decide), byteEq 3 (by decide)]

theorem parent_inj {root : Bool} {left right lhs rhs : CV}
    (eq : parentInput root left right = parentInput root lhs rhs) : left = lhs ∧ right = rhs := by
  have blocks := congrArg Input.block eq
  change left ++ right = lhs ++ rhs at blocks
  constructor <;> apply Vector.ext <;> intro pos bound
  · simpa only [Vector.getElem_append_left bound] using
      congrArg (fun (words : Block) => words[pos]'(by omega)) blocks
  · simpa only [Vector.getElem_append_right (by omega : pos + 8 < 8 + 8) (by omega : 8 ≤ pos + 8),
      Nat.add_sub_cancel] using congrArg (fun (words : Block) => words[pos + 8]'(by omega)) blocks

end Silmaril.Proofs.Crypto.Blake3

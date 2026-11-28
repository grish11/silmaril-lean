module

import Silmaril.Formats.Parquet.Hybrid.Thms
meta import Silmaril.Formats.Bytes

/-! Raw parquet-java hybrid fixtures and boundary cases. -/

namespace Silmaril.Formats.Parquet.Hybrid

set_option maxRecDepth 8192

private def budget : Limits := ⟨130, 64⟩
private def increasing : List Nat := [0, 1, 2, 3, 4, 5, 6, 7]
private def rle : Bytes := .ofList [0x84, 0x02, 0x13]
private def packed : Bytes := .ofList [0x05, 0x88, 0xc6, 0xfa, 0xd5, 0, 0]
private def mixed : Bytes := .ofList [0x03, 0x88, 0xc6, 0xfa, 0x28, 0x05, 0x03, 0x90, 0x01, 0]
private def zeroWidth : Bytes := .ofList [0x16]
private def width32 : Bytes := .ofList [0x10, 0xff, 0xff, 0xff, 0xff]

private def fixtureLine (name : String) (width count : Nat) (payload : Bytes) : String :=
  let hex := String.ofList (payload.toList.flatMap fun byte =>
    [(byte.toNat / 16).digitChar, (byte.toNat % 16).digitChar])
  name ++ "\t" ++ toString width ++ "\t" ++ toString count ++ "\t" ++ hex ++ "\n"

#guard
    (include_str "../../../../tests/formats/parquet-hybrid/parquet-java-1.16.0.tsv") =
      fixtureLine "rle" 5 130 rle ++
      fixtureLine "packed" 3 11 packed ++
      fixtureLine "mixed" 3 31 mixed ++
      fixtureLine "zero-width" 0 11 zeroWidth ++
      fixtureLine "width32" 32 8 width32

example : decode 5 130 budget rle = .ok (List.replicate 130 19) := rfl
example : encodeRepeated 5 130 19 = .ok rle := by
  change Except.ok (Bytes.ofList (uleb 260 ++ [19])) = .ok rle
  rw [show uleb 260 = [0x84, 2] by decide +kernel]
  rfl
example : decode 3 11 budget packed = .ok (increasing ++ [5, 2, 3]) := rfl
example : decode 3 31 budget mixed = .ok (increasing ++ List.replicate 20 5 ++ [0, 2, 6]) := rfl
example : decode 0 11 budget zeroWidth = .ok (List.replicate 11 0) := rfl
example : encodeRepeated 0 11 0 = .ok zeroWidth := by
  change Except.ok (Bytes.ofList (uleb 22 ++ [])) = .ok zeroWidth
  rw [show uleb 22 = [0x16] by decide +kernel]
  rfl
example : decode 32 8 budget width32 = .ok (List.replicate 8 4294967295) := rfl
example : encodeRepeated 32 8 4294967295 = .ok width32 := by
  change Except.ok (Bytes.ofList (uleb 16 ++ [0xff, 0xff, 0xff, 0xff])) = .ok width32
  rw [show uleb 16 = [0x10] by decide +kernel]
  rfl

-- 0x88 0xc6 0xfa is the pinned spec's little-endian, width-three group.
example : unpackGroup 3 [0x88, 0xc6, 0xfa] = increasing := rfl
example : decode 3 11 budget (.ofList [5, 0x88, 0xc6, 0xfa, 0xd5, 0xff, 0xff]) =
    .ok (increasing ++ [5, 2, 7]) := rfl
-- Change only positions 11 through 15, keeping the third used bit-field equal to 3.
example : decode 3 11 budget (.ofList [5, 0x88, 0xc6, 0xfa, 0xd5, 0xfe, 0xff]) =
    .ok (increasing ++ [5, 2, 3]) := rfl
example : decode 3 9 budget packed = .ok (increasing ++ [5]) := rfl
example : decode 3 8 budget packed = .error .countMismatch := rfl
example : decode 3 11 budget (packed.push 0) = .error .trailingBytes := rfl
example : decode 0 1 budget (.ofList [3]) = .ok [0] := rfl
example : decode 0 1 budget (.ofList [2, 2]) = .error .trailingBytes := rfl
example : decode 32 1 budget (.ofList ([3, 0xff, 0xff, 0xff, 0xff] ++ List.replicate 28 0)) =
    .ok [4294967295] := rfl

example : readRun 0 [0xfe, 0xff, 0xff, 0xff, 0x0f] =
    .ok (.repeated 2147483647 0, []) := rfl
example : readHeader [0x80, 0] = .error .noncanonicalHeader := rfl
example : readHeader [0x80] = .error .truncated := rfl
example : readHeader [0x80, 0x80, 0x80, 0x80, 0x80, 1] = .error .headerOverflow := rfl
example : readHeader [0x80, 0x80, 0x80, 0x80, 0x10] = .error .headerOverflow := rfl
example : readRun 0 [0] = .error .invalidRunLength := rfl
example : readRun 0 [1] = .error .invalidRunLength := rfl
example : readRun 0 [0x81, 0x80, 0x80, 0x80, 0x02] = .error .invalidRunLength := rfl
example : readRun 5 [2, 32] = .error .valueOverflow := rfl
example : decode 3 8 budget (.ofList [3, 0x88, 0xc6]) = .error .truncated := rfl
example : decode 5 1 budget (.ofList [2]) = .error .truncated := rfl
example : decode 0 1 budget (.ofList [4]) = .error .countMismatch := rfl
example : decode 0 2 budget (.ofList [2]) = .error .truncated := rfl
example : decode 1 0 budget .empty = .ok [] := rfl
example : decode 1 0 budget (.ofList [2, 0]) = .error .trailingBytes := rfl

example : decode 33 0 budget .empty = .error .invalidWidth := rfl
example : decode 0 131 budget .empty = .error .valueLimit := rfl
example : decode 0 (2 ^ 31) ⟨2 ^ 31, 0⟩ .empty = .error .valueLimit := rfl
example : decode 5 130 ⟨130, 2⟩ rle = .error .byteLimit := rfl
example : encodeRepeated 33 1 0 = .error .invalidWidth := rfl
example : encodeRepeated 0 0 0 = .error .invalidRunLength := rfl
example : encodeRepeated 0 (2 ^ 31) 0 = .error .invalidRunLength := rfl
example : encodeRepeated 32 1 (2 ^ 32) = .error .valueOverflow := rfl

end Silmaril.Formats.Parquet.Hybrid

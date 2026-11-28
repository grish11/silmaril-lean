module

import Silmaril.Machine.SQLite.Accessories.All

namespace Silmaril.Machine.SQLite.Accessories.Checks

open Silmaril.Formats Silmaril.Formats.Sqlite
open Silmaril.Machine.SQLite.TestCode

private def fixture (bytes : List UInt8) (offset : Nat) (expected : Option (UInt64 × Nat)) :
    Fixture (File.View × Nat) (Option (UInt64 × Nat)) :=
  ⟨(File.View.ofBytes (Bytes.ofList bytes), offset), expected⟩

private def nine : Fixture (File.View × Nat) (Option (UInt64 × Nat)) :=
  fixture [0, 255, 255, 255, 255, 255, 255, 255, 255, 255, 0] 1
    (some (18446744073709551615, 10))

private def read (input : File.View × Nat) : Option (UInt64 × Nat) :=
  Varint.read? input.1 input.2

/-- This reader incorrectly treats the eighth byte as the last position. -/
private def readEight (input : File.View × Nat) : Option (UInt64 × Nat) :=
  (Varint.readAux? input.1 8 input.2 0).map fun (value, next) => (UInt64.ofNat value, next)

example : nine.Passes read :=
  (Fixture.check_iff nine read).mp (by decide)

example : nine.check readEight = false := by decide

example : (fixture [128, 0] 0 (some (0, 2))).check read = true := by decide

example : (fixture [0, 128] 1 none).check read = true := by decide

end Silmaril.Machine.SQLite.Accessories.Checks

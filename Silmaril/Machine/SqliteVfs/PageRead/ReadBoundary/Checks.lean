module

import Silmaril.Machine.SqliteVfs.PageRead.ReadBoundary.Thms
import Init.Omega

namespace Silmaril.Machine.SqliteVfs.PageRead.ReadBoundary

open Silmaril.Machine.SqliteRead (Context BufferView)

private def abi : SqliteRead.Request := ⟨1, 32, 2, 0⟩
private def modeledPage : Page := ⟨⟨0⟩, 1, 2⟩
private def bindings : FileBinding := fun ptr => if ptr = 1 then some ⟨0⟩ else none
private def context : Context := ⟨fun _ => True, fun _ _ => True⟩
private def cache : Cache := fun slot => if slot = 0 then some .vacant else none
private def beforeBuffer : BufferView := fun _ => none
private def written (tail : BitVec 8) : BufferView :=
  fun address => if address = 32 then some 10 else if address = 33 then some tail else none

private theorem safe : context.Admits abi :=
  ⟨by decide, trivial, by decide, by decide, by decide, by decide, by decide, trivial⟩

private theorem aligned : MatchesPage bindings abi modeledPage := ⟨rfl, rfl, rfl⟩

private theorem framed (tail : BitVec 8) :
    Silmaril.Machine.SqliteRead.Framed abi beforeBuffer (written tail) := by
  intro address outside
  change address < 32 ∨ 34 ≤ address at outside
  simp [written, beforeBuffer, show address ≠ 32 from by omega, show address ≠ 33 from by omega]

private theorem writes (tail : BitVec 8) :
    Silmaril.Machine.SqliteRead.Writes abi (written tail) [10, tail] := by
  intro i within
  change i < 2 at within
  have index : i = 0 ∨ i = 1 := by omega
  rcases index with rfl | rfl <;> rfl

private def fullFile : FileState := ⟨[10, 20], some .readOnly, 0⟩
private def shortFile : FileState := ⟨[10], some .readOnly, 0⟩

example : (fill (readOnly 8) fullFile cache 0 modeledPage).result = .ok [10, 20] := by
  have law : SqliteRead.Handler (fullFile.bytes.map UInt8.toBitVec) abi beforeBuffer (written 20) .ok :=
    ⟨framed 20, rfl, writes 20⟩
  have run := returning_handler_agrees_with_fill abi modeledPage context fullFile 8 cache 0
    beforeBuffer (written 20) .ok safe aligned (by decide) rfl rfl law
  exact congrArg Outcome.result run.2.1

example : (fill (readOnly 8) shortFile cache 0 modeledPage).result = .error .shortRead ∧
    written 0 (abi.buffer.toNat + 1) = some 0 := by
  have law : SqliteRead.Handler (shortFile.bytes.map UInt8.toBitVec) abi beforeBuffer (written 0) .shortRead :=
    ⟨framed 0, by decide, writes 0⟩
  have run := returning_handler_agrees_with_fill abi modeledPage context shortFile 8 cache 0
    beforeBuffer (written 0) .shortRead safe aligned (by decide) rfl rfl law
  exact ⟨congrArg Outcome.result run.2.1, run.2.2 1 (by decide)⟩

example : SqliteRead.Framed abi beforeBuffer beforeBuffer := by
  have law : SqliteRead.Handler (shortFile.bytes.map UInt8.toBitVec) abi beforeBuffer beforeBuffer
      (.other 1) := ⟨fun _ _ => rfl, by decide, by decide⟩
  exact (returning_handler_agrees_with_fill abi modeledPage context shortFile 8 cache 0
    beforeBuffer beforeBuffer (.other 1) safe aligned (by decide) rfl rfl law).1

#print axioms read_range_of_admission
#print axioms page_admitted
#print axioms returning_handler_agrees_with_fill

end Silmaril.Machine.SqliteVfs.PageRead.ReadBoundary

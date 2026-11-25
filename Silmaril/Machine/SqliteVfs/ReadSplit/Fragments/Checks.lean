module

import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.Thms
import Silmaril.Machine.SqliteVfs.Thms

namespace Silmaril.Machine.SqliteVfs.ReadSplit.Fragments

private def snapshot : FileState := ⟨[11, 22, 33, 44, 0, 77], some .readOnly, 0⟩
private def handle : Handle := ⟨0⟩

private def counted : Handler (FileState × Nat) :=
  fun state req =>
    let result := readOnly 8 state.1 req
    (result.1, result.2, state.2 + 1)

private theorem counted_law : ReadLaw counted Prod.fst where
  read state := (readOnly_lawful 8).2.1.read state.1
  fileSize state := (readOnly_lawful 8).2.1.fileSize state.1

example :
    let result := readFragments counted handle (snapshot, 0) 2 1 [2, 2]
    result.reply = some (.shortRead [33, 44, 0, 77, 0]) ∧
      result.file = (snapshot, 3) ∧
      result.trace.map Exchange.request = [.read handle 2 1, .read handle 3 2, .read handle 5 2] :=
  by decide

example :
    let result := readFragments counted handle (snapshot, 0) 2 1 [2, 2]
    let request := Request.read handle 2 5
    let whole := counted (snapshot, 0) request
    result.reply = some whole.1 ∧ result.file.1 = whole.2.1 ∧
      Trace.Valid counted (snapshot, 0) result.trace result.file ∧
      result.trace.map Exchange.request = fragmentRequests handle 2 (1 :: [2, 2]) ∧
      Trace.Valid counted (snapshot, 0) [⟨request, whole.1⟩] whole.2 :=
  read_fragments_sound counted_law (snapshot, 0) handle 2 1 [2, 2]
    (by decide) (by simp) (by decide) (by decide)

example :
    let result := readFragments counted handle (snapshot, 0) 0 1 [0, 2]
    result.reply = none ∧ result.file = (snapshot, 3) ∧
      result.trace.map Exchange.request = [.read handle 0 1, .read handle 1 0, .read handle 1 2] :=
  by decide

example :
    let result := readFragments counted handle (snapshot, 0) 0 1 [0, 2]
    result.trace =
      [⟨.read handle 0 1, .ok [11]⟩, ⟨.read handle 1 0, .error .invalidRange⟩,
       ⟨.read handle 1 2, .ok [22, 33]⟩] := rfl

example :
    let result := readFragments counted handle (snapshot, 0) 0 1 [0, 2]
    Trace.Valid counted (snapshot, 0) result.trace result.file :=
  (read_fragments_trace counted handle (snapshot, 0) 0 1 [0, 2]).1

example :
    (readFragments counted handle (snapshot, 0) 5 1 []).reply = some (.ok [77]) := rfl

example :
    (readFragments counted handle (snapshot, 0) 0 0 []).reply = none := rfl

end Silmaril.Machine.SqliteVfs.ReadSplit.Fragments

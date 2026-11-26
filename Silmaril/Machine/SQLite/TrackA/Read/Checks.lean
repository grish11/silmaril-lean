module

import Silmaril.Formats.Sqlite.File.WriteProfile.Defs
import Silmaril.Machine.SQLite.TrackA.Read.Thms
meta import Silmaril.Machine.SQLite.TrackA.Read.Defs
meta import Silmaril.Formats.Sqlite.File.WriteProfile.Defs

namespace Silmaril.Machine.SQLite.TrackA.Read

open Silmaril.Formats.Sqlite
open Silmaril.Machine.SqliteVfs

private def snapshot : WriteProfile.Snapshot := ⟨[⟨42, 7⟩], by decide⟩
private def cache : PageRead.Cache := fun slot => if slot = 0 then some .vacant else none

private def image? : Option File.Image := do
  let bytes ← (WriteProfile.Image.encode snapshot).toOption
  File.parse? bytes

private def completeRead (exchanges : Trace) (bytes : Bytes) : Bool :=
  match exchanges with
  | [⟨.read handle offset count, .ok reply⟩] =>
      handle == ⟨0⟩ && offset == 512 && count == 512 && reply == bytes
  | _ => false

private def checksLookup (key : Int64) (expected : Option Value) : Bool :=
  match image? with
  | none => false
  | some image =>
    match image.page? 2 with
    | none => false
    | some view =>
      let file : FileState := ⟨image.source.toList, some .readOnly, 0⟩
      let page : PageRead.Page := ⟨⟨0⟩, 2, image.header.pageSize⟩
      let staged := runStaged (readOnly 1024) file cache 0 page key
      let cold := runComposed (readOnly 1024) file cache 0 page key
      let warm := runComposed (readOnly 1024) cold.file cold.cache 0 page key
      let bytes := view.materialize.toList
      lookupValue snapshot.readTable key == expected && staged.result.toOption == some expected &&
        cold.result.toOption == some expected && warm.result.toOption == some expected &&
        completeRead staged.exchanges bytes && completeRead cold.exchanges bytes &&
        warm.exchanges.isEmpty && cold.file == file && warm.file == file &&
        cold.cache 0 == some (.resident page bytes) && warm.cache 0 == cold.cache 0

private def rejectsShortRead : Bool :=
  match image? with
  | none => false
  | some image =>
    let file : FileState := ⟨image.source.toList.take 600, some .readOnly, 0⟩
    let page : PageRead.Page := ⟨⟨0⟩, 2, image.header.pageSize⟩
    let outcome := runComposed (readOnly 1024) file cache 0 page 41
    match outcome.result, outcome.exchanges with
    | .error (.acquire .shortRead), [⟨.read handle offset count, .shortRead reply⟩] =>
        handle == page.handle && offset == 512 && count == 512 &&
          reply == readBytes file.bytes 512 512 && outcome.cache 0 == some .vacant
    | _, _ => false

#guard checksLookup 42 (some (.integer 7))
#guard checksLookup 41 none
#guard rejectsShortRead

#print axioms program_lookup
#print axioms runLeaf_lookup
#print axioms seekLeaf_eq_runLeaf
#print axioms staged_eq_composed
#print axioms composed_trace
#print axioms readOnly_cold_warm_lookup

end Silmaril.Machine.SQLite.TrackA.Read

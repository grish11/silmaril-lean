module

import Batteries.Data.Except
import Silmaril.Formats.Sqlite.File.WriteProfile.Defs
import Silmaril.Machine.SQLite.TrackB.Read.Thms
meta import Silmaril.Formats.Sqlite.File.WriteProfile.Defs
meta import Silmaril.Machine.SQLite.TrackB.Read.Defs

namespace Silmaril.Machine.SQLite.TrackB.Read

open Silmaril.Formats.Sqlite
open Silmaril.Machine.SqliteVfs
open Silmaril.Semantics

private def snapshot : WriteProfile.Snapshot := ⟨[⟨42, 7⟩, ⟨-3, 11⟩], by decide⟩

private def image? : Option File.Image := do
  let bytes ← (WriteProfile.Image.encode snapshot).toOption
  File.parse? bytes

private def entries : List (Int × List Value) :=
  [(-3, [.integer (-3), .integer 11]), (42, [.integer 42, .integer 7])]

private def memory : LeafMemory := leafMemory 2 (BTree.Query.ReadModel.ofList entries)

-- The same payload is checked against the actual encoded leaf below.
example : Page.Run leafModel (pageLookup 2 (-3)) memory []
    (.returned (some [.integer (-3), .integer 11]) memory) :=
  .call (.readDefined (p := 2) rfl) .pure

example : Page.Run leafModel (pageLookup 2 41) memory [] (.returned none memory) :=
  .call (.readDefined (p := 2) rfl) .pure

private def cache : PageRead.Cache := fun slot => if slot = 0 then some .vacant else none

private def onlyRead (page : PageRead.Page) (expected : ReadReply) : Trace → Bool
  | [⟨.read handle offset size, reply⟩] =>
    decide (page.request = .read handle offset size) && decide ((show ReadReply from reply) = expected)
  | _ => false

private def checkRead (key : Int64) (expected : Option Value) : Bool :=
  match image? with
  | none => false
  | some image => (do
    let view ← image.page? 2
    let table ← FileView.VdbeLeaf.table? view 0
    let file : FileState := ⟨image.source.toList, some .readOnly, 0⟩
    let page : PageRead.Page := ⟨⟨0⟩, 2, image.header.pageSize⟩
    let bytes := view.materialize.toList
    let cold := run (readOnly 1024) file cache 0 page key
    let warm := run (readOnly 1024) cold.file cold.cache 0 page key
    pure (decide (table.entries = entries) &&
      decide (lookupLeaf view 2 key = .ok expected) &&
      decide (cold.result = .ok expected) && decide (warm.result = .ok expected) &&
      decide (cold.cache 0 = some (.resident page bytes)) &&
      decide (warm.cache 0 = cold.cache 0) && cold.file == file && warm.file == cold.file &&
      decide (page.request = .read ⟨0⟩ 512 512) &&
      onlyRead page (.ok bytes) cold.exchanges && warm.exchanges.isEmpty)
    : Option Bool).getD false

private def checkShortRead : Bool :=
  match image? with
  | none => false
  | some image =>
    let file : FileState := ⟨image.source.toList.take 600, some .readOnly, 0⟩
    let page : PageRead.Page := ⟨⟨0⟩, 2, image.header.pageSize⟩
    let outcome := run (readOnly 1024) file cache 0 page 41
    decide (outcome.result = .error (.acquire .shortRead)) &&
      onlyRead page (.shortRead (readBytes file.bytes 512 512)) outcome.exchanges &&
      decide (outcome.cache 0 = some .vacant) && outcome.file == file

#guard checkRead (-3) (some (.integer 11))
#guard checkRead 41 none
#guard checkShortRead

#print axioms leaf_valid
#print axioms leaf_represents
#print axioms page_lookup_run_iff
#print axioms leaf_lookup
#print axioms lookupLeaf_eq_seekLeaf
#print axioms lookupLeaf_eq_runLeaf
#print axioms run_eq_staged
#print axioms run_eq_composed
#print axioms finishAcquire_page
#print axioms readOnly_cold_warm_page

end Silmaril.Machine.SQLite.TrackB.Read

module

import Silmaril.Formats.Sqlite.File.WriteProfile.Defs
import Silmaril.Machine.SQLite.TrackA.Read.Checks
import Silmaril.Machine.SQLite.TrackA.Read.Adapter.Thms
meta import Silmaril.Formats.Sqlite.File.WriteProfile.Defs
meta import Silmaril.Machine.SQLite.TrackA.Read.Adapter.Defs
meta import Silmaril.Machine.SQLite.TrackA.Read.Interaction.Defs
meta import Silmaril.Semantics.TrackA.Interaction.Defs

namespace Silmaril.Machine.SQLite.TrackA.Read.Adapter

open Silmaril.Formats.Sqlite
open Silmaril.Machine.SqliteVfs
open Silmaril.Semantics.TrackA.Interaction (Signature ITree Coalgebra)
open Read.Interaction (VfsSignature vfsTree)

-- The fixture evaluates successive transitions of one handled tree.
private def run {S : Signature} {State Result : Type} (tree : ITree S Result)
    (handler : Coalgebra.Handler S State) (initial : State) : Option (Result × State) :=
  let interpreted := tree.unfold.handle (T := VfsSignature) handler
  let rec finish : Nat → tree.State × State → Option (Result × State)
    | 0, state => match interpreted state with
      | .ret result => some (result, state.2)
      | _ => none
    | fuel + 1, state => match interpreted state with
      | .ret result => some (result, state.2)
      | .tau next => finish fuel next
      | _ => none
  finish 2 (tree.root (), initial)

private def countedReadOnly (capacity : Nat) : Handler (FileState × Nat) :=
  fun (file, calls) request =>
    let (reply, after) := readOnly capacity file request
    (reply, after, calls + 1)

private def matchesRead (request : Acquire) (bytes : Bytes) : Exchange → Bool
  | ⟨.read handle offset count, .ok data⟩ =>
      handle == request.page.handle && offset == 512 && count == 512 && data == bytes
  | _ => false

private def caseChecks (key : Int64) (expected : Option Value) : Option Bool := do
  let snapshot : WriteProfile.Snapshot := ⟨[⟨42, 7⟩], by decide⟩
  let source ← (WriteProfile.Image.encode snapshot).toOption
  let image ← File.parse? source
  let view ← image.page? 2
  let file : FileState := ⟨source.toList, some .readOnly, 0⟩
  let request : Acquire := ⟨0, ⟨⟨0⟩, 2, image.header.pageSize⟩⟩
  let bytes := view.materialize.toList
  let vacant : PageRead.Cache := fun slot => if slot = 0 then some .vacant else none
  let backing := countedReadOnly 1024
  let previous : Trace := [⟨.fileSize request.page.handle, .ok file.bytes.length⟩]
  let (result, (after, calls), cache, history) ←
    run (pagerTwice (stagedCall request key)) (handlePager backing) ((file, 1), vacant, previous)
  let (composed, (vfsAfter, vfsCalls), vfsHistory) ←
    run (vfsTree vacant request.target request.page key) (handleVfs backing) ((file, 0), [])
  let resident := some (.resident request.page bytes)
  let returnsExpected (leaf : LeafResult) :=
    leaf.1.toOption == some expected && leaf.2 request.target == resident
  return returnsExpected result.1 && returnsExpected result.2 && returnsExpected composed &&
    after == file && vfsAfter == file && calls == 2 && vfsCalls == 1 &&
    cache request.target == resident &&
    match history, vfsHistory with
    | [⟨.fileSize handle, .ok size⟩, read], [vfsRead] =>
      handle == request.page.handle && size == file.bytes.length &&
        matchesRead request bytes read && matchesRead request bytes vfsRead
    | _, _ => false

#guard (caseChecks 42 (some (.integer 7))) == some true
#guard (caseChecks 41 none) == some true

#print axioms interpretations_agree
#print axioms pagerTwice_agrees
#print axioms pagerTwice_readOnly_cold_warm

end Silmaril.Machine.SQLite.TrackA.Read.Adapter

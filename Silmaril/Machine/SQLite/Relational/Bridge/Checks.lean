module

import Silmaril.Formats.Sqlite.File.WriteProfile.Defs
import Silmaril.Machine.SQLite.Relational.Bridge.Thms
meta import Silmaril.Formats.Sqlite.File.WriteProfile.Defs
meta import Silmaril.Machine.SQLite.Relational.Bridge.Defs

namespace Silmaril.SQLite.Relational.Bridge.Checks

open Silmaril.Formats.Sqlite
open Silmaril.Machine.SqliteVfs
open CatalogExecutor (Names)

private def semantics : TableSemantics SqlValue Affinity Unit where
  evalGenerated _ _ := none
  evalCheck _ _ := none
  keyEqual _ _ a b := decide (a = b)
  foreignEqual _ _ a b := decide (a = b)

private def label (i : Fin 2) : String := if i = 0 then "id" else "amount"

private def schema : TableSchema Affinity Unit where
  mode := .strict
  width := 2
  column i := ⟨label i, .strict .integer, none, true⟩
  uniqueNames := fun {i j} =>
    (by decide : ∀ a b : Fin 2, label a = label b → a = b) i j
  organization := .rowid (some 0)
  generation _ := none
  suppliedExists := ⟨0, rfl⟩
  inputsSupplied := by simp
  primaryKey := some ⟨0, []⟩
  primaryKeySupplied := by simp
  organizationKey := ⟨rfl, ⟨⟨0, []⟩, rfl, rfl⟩⟩

private def rowValue (i : Fin 2) : SqlValue := .integer (if i = 0 then 42 else 7)

private def row : TableRow ValueModel.sqlValue schema :=
  TableRow.ofCells (schema := schema) (42 : Int64) fun i => ⟨rowValue i, rfl⟩

private def catalog : CatalogExecutor.SqlSnapshot semantics where
  tables name := if name = "sample" then
    (CheckedTable.check [row]).map fun checked => ⟨schema, checked⟩
    else none
  objects := {}

private def call (key : Int64) : Invocation Names := ⟨⟨⟨"sample", "amount"⟩⟩, some (1, key)⟩

private def page : PageRead.Page := ⟨⟨0⟩, 2, 512⟩
private def locate : Locate semantics := fun _ => ⟨0, page⟩

private def connection (bytes : Bytes) : Connection (profile semantics FileState) where
  catalog := catalog
  backing := ⟨bytes, some .readOnly, 0⟩
  cache slot := if slot = 0 then some .vacant else none
  exchanges := [⟨.fileSize page.handle, .ok bytes.length⟩]
  session := ⟨false, 2, 9, -4⟩

private def imageBytes : Option Bytes :=
  ((WriteProfile.Image.encode ⟨[⟨42, 7⟩], by decide⟩).toOption).map fun bytes => bytes.toList

private def checkExchange (fileSize : Nat) (response : ReadReply) : Trace → Bool
  | [⟨.fileSize handle, .ok size⟩, ⟨.read actual offset count, reply⟩] =>
    let actualReply : ReadReply := reply
    handle == page.handle && actual == page.handle && offset == 512 && count == 512 &&
      size == fileSize && decide (actualReply = response)
  | _ => false

private def coldWarmCheck (key : Int64) (cell : Option SqlValue) : Bool :=
  match imageBytes with
  | none => false
  | some bytes =>
    let db := connection bytes
    let out := (executor (readOnly 1024) locate).executeBatch db [call key, call key]
    let payload := readBytes bytes 512 512
    let expected : SelectResult SqlValue := ⟨"amount", cell⟩
    let checkState (after : Connection (profile semantics FileState)) :=
      after.backing == db.backing && after.cache 0 == some (.resident page payload) &&
        after.cache 1 == none && after.session == db.session &&
        checkExchange 1024 (.ok payload) after.exchanges
    let projected := CatalogExecutor.execute semantics (forgetStorage db) (call key)
    match out.1.completed, out.1.failure, projected.1 with
    | [(first, cold), (second, warm)], none, .statement (.ok result) =>
      decide (first = expected) && decide (second = expected) && decide (result = expected) &&
        checkState cold && checkState warm && checkState out.2 &&
        projected.2.session == out.2.session && projected.2.exchanges.isEmpty
    | _, _, _ => false

-- The backing retires the handle when handling the read. A short read must
-- keep that poststate and can neither install a slot nor enter a second call.
private def retireAfterRead : Handler FileState := fun state request =>
  match request with
  | .read handle offset count =>
    let (reply, after) := readOnly 1024 state (.read handle offset count)
    (reply, { after with openMode := none, generation := after.generation + 1 })
  | request => readOnly 1024 state request

private def shortReadCheck : Bool :=
  match imageBytes with
  | none => false
  | some bytes =>
    let db := connection (bytes.take 600)
    let out := (executor retireAfterRead locate).executeBatch db [call 42, call 42]
    match out.1.completed, out.1.failure with
    | [], some (.run (.trackA (.acquire .shortRead))) =>
      out.2.backing == { db.backing with openMode := none, generation := 1 } &&
        out.2.cache 0 == some .vacant && out.2.session == db.session &&
        checkExchange 600 (.shortRead (readBytes db.backing.bytes 512 512)) out.2.exchanges
    | _, _ => false

#guard coldWarmCheck 42 (some (.integer 7))
#guard coldWarmCheck 41 none
#guard shortReadCheck

example : transferResult (.ok (some .null)) = .ok (some .null) := rfl
example : transferCell (.real 0x7ff8000000000000) = .error (.nanReal 0x7ff8000000000000) := rfl

example : execute retireAfterRead locate (connection []) { call 42 with binding := none } =
    (.statement (.ok ⟨"amount", none⟩), connection []) := rfl

example : execute retireAfterRead locate (connection []) { call 42 with binding := some (2, 42) } =
    (.statement (.error (.bind .range)), connection []) := rfl

-- Distinct files and completed size exchanges collapse to the same catalog observation.
example : connection [] ≠ connection [0] := by
  intro same
  have sameSize := congrArg (fun db => db.backing.bytes.length) same
  cases sameSize

example : forgetStorage (connection []) = forgetStorage (connection [0]) := rfl

example : CatalogExecutor.execute semantics (forgetStorage (connection [0])) (call 42) =
    (.statement (.ok ⟨"amount", some (.integer 7)⟩), forgetStorage (connection [])) := rfl

#print axioms execute_corresponds
#print axioms execute_cold_warm

end Silmaril.SQLite.Relational.Bridge.Checks

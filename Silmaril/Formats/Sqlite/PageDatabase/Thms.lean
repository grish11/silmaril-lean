module

public import Silmaril.Formats.Sqlite.PageDatabase.Defs
public import Silmaril.Semantics.BTreePages.Trace.Thms
import Silmaril.Proofs.Formats.Sqlite.PageDatabase.Laws

public section
namespace Silmaril.Formats.Sqlite.PageDatabase

open Silmaril.Semantics

variable {Key Kind Content : Type} {Cell : Kind → Type}
variable {n : Nat} {initial final : Page.UndefArray n Content} {trace : ReadWrite.Trace Nat Content}

theorem Table.readModel_rows [DecidableEq Key] (table : Table Key Kind Cell Content) :
    table.readModel.rows = table.rows :=
  rfl

variable [LinearOrder Key]

/-- The SQL read interface and the routed B-tree agree on a represented table. -/
theorem Table.readModel_get (table : Table Key Kind Cell Content)
    (rep : table.Represents initial) (key : Key) :
    table.readModel.get key = table.tree.lookup? key :=
  Proofs.Formats.Sqlite.PageDatabase.readModel_get table rep key

theorem Table.replays_frame {table : Table Key Kind Cell Content}
    (rep : table.Represents initial) (run : trace.Replays (Page.UndefArray.access n Content) initial final)
    (disjoint : ∀ p, table.Footprint p → ¬ trace.Defs p) :
    table.Represents final :=
  Proofs.Formats.Sqlite.PageDatabase.table_frame rep run disjoint

theorem Database.replays_frame {db : Database Key Kind Cell Content}
    (rep : db.Represents initial) (run : trace.Replays (Page.UndefArray.access n Content) initial final)
    (disjoint : ∀ p, db.Footprint p → ¬ trace.Defs p) :
    db.Represents final :=
  Proofs.Formats.Sqlite.PageDatabase.database_frame rep run disjoint

end Silmaril.Formats.Sqlite.PageDatabase

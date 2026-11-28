module

public import Silmaril.Semantics.BTreePages.Trace.Defs
public import Silmaril.Semantics.Relational.Table.Defs
public import Silmaril.Formats.Sqlite.BTree.Query.ReadModel.Defs

/-! Rooted, keyed SQLite table views over a shared fixed-size page array. -/

@[expose] public section
namespace Silmaril.Formats.Sqlite.PageDatabase

open Silmaril.Semantics

variable {Key Kind Content : Type} {Cell : Kind → Type}

/-- A named table's data is a leaf-oriented B-tree of typed rows. Placement and
page interpretation are supplied by the layout. The decoder can depend on
the address, for instance to account for a page-specific header. -/
structure Table (Key Kind : Type) (Cell : Kind → Type) (Content : Type) where
  schema : Silmaril.Relational.PositionalSchema Kind
  tree : BTree.Tree Key (Silmaril.Relational.Row schema.kind Cell)
  layout : BTreePages.Layout Nat
  decode : Nat → Content → Option (BTreePages.PageData Key (Silmaril.Relational.Row schema.kind Cell) Nat)

namespace Table

def rows (table : Table Key Kind Cell Content) : Silmaril.Relational.Table table.schema.kind Cell :=
  table.tree.entries.map Prod.snd

def readModel [DecidableEq Key] (table : Table Key Kind Cell Content) :
    BTree.Query.ReadModel Key (Silmaril.Relational.Row table.schema.kind Cell) :=
  .ofList table.tree.entries

def Footprint (table : Table Key Kind Cell Content) : Nat → Prop :=
  BTreePages.Footprint table.layout table.tree

/-- Preserve the allocation domain. An allocated page with no decodable node
has no defined observation in this table's decoded view. -/
def decodedMemory {n : Nat} (table : Table Key Kind Cell Content)
    (pages : Page.UndefArray n Content) :
    Page.MapMemory Nat (BTreePages.PageData Key (Silmaril.Relational.Row table.schema.kind Cell) Nat) :=
  fun page => match pages.toMemory page with
    | .absent => .absent
    | .undef => .undef
    | .defined data => match table.decode page data with
      | none => .undef
      | some node => .defined node

def Represents [LinearOrder Key] {n : Nat} (table : Table Key Kind Cell Content)
    (pages : Page.UndefArray n Content) : Prop :=
  BTreePages.Represents (Page.mapStore Nat _) table.layout table.tree (table.decodedMemory pages)

def Validates [LinearOrder Key] (before after : Table Key Kind Cell Content) (n : Nat)
    (trace : ReadWrite.Trace Nat Content) : Prop :=
  trace.Validates (Page.UndefArray.access n Content) before.Represents after.Represents

end Table

/-- A logical catalogue of table roots over the same array. The catalogue
is supplied as metadata. Each table may have its own schema and decoder. -/
structure Database (Key Kind : Type) (Cell : Kind → Type) (Content : Type) where
  tables : List (String × Table Key Kind Cell Content)

namespace Database

def find? (db : Database Key Kind Cell Content) (name : String) : Option (Table Key Kind Cell Content) :=
  db.tables.lookup name

/-- Represent each named table, with distinct names and disjoint live table
pages. Unclaimed pages are unrestricted. -/
def Represents [LinearOrder Key] {n : Nat} (db : Database Key Kind Cell Content)
    (pages : Page.UndefArray n Content) : Prop :=
  (db.tables.map Prod.fst).Nodup ∧
  db.tables.Pairwise (fun left right => ∀ p, left.2.Footprint p → ¬ right.2.Footprint p) ∧
  ∀ entry ∈ db.tables, entry.2.Represents pages

def Footprint (db : Database Key Kind Cell Content) (page : Nat) : Prop :=
  ∃ entry ∈ db.tables, entry.2.Footprint page

def Validates [LinearOrder Key] (before after : Database Key Kind Cell Content) (n : Nat)
    (trace : ReadWrite.Trace Nat Content) : Prop :=
  trace.Validates (Page.UndefArray.access n Content) before.Represents after.Represents

end Database

end Silmaril.Formats.Sqlite.PageDatabase

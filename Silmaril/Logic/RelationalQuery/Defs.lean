module

public import Silmaril.Semantics.Relational.Database.Defs

/-! Read-only Boolean queries over typed list tables and schema-indexed databases. -/

@[expose] public section

namespace Silmaril.Relational

open CategoryTheory

universe u v w

/-- A table signature with an arbitrary type of column indices and a kind at each index. -/
structure QuerySchema (Kind : Type v) where
  Index : Type u
  kind : Index → Kind

namespace QuerySchema

variable {Kind : Type v}

instance : Category (QuerySchema.{u, v} Kind) where
  Hom s t := ColumnMap s.kind t.kind
  id s := ColumnMap.id s.kind
  comp := ColumnMap.comp
  id_comp _ := ColumnMap.ext rfl
  comp_id _ := ColumnMap.ext rfl
  assoc _ _ _ := ColumnMap.ext rfl

/-- Use the existing finite positional schema and its kind-preserving position maps. -/
def ofPositional : PositionalSchema Kind ⥤ QuerySchema.{0, v} Kind where
  obj s := ⟨Fin s.width, s.kind⟩
  map f := f

/-- Use occupied names as indices. Arrows from the named API still preserve names. -/
def ofNamed (Name : Type u) : NamedSchema Name Kind ⥤ QuerySchema.{u, v} Kind where
  obj s := ⟨s.Index, s.kind⟩
  map f := ⟨f.index, fun i => congrArg Prod.snd (f.label_eq i)⟩
  map_id _ := ColumnMap.ext rfl
  map_comp _ _ := ColumnMap.ext rfl

end QuerySchema

/-- Boolean closure of a language of row-existence tests. -/
inductive BooleanQuery (Atom : Type u) where
  | atom (test : Atom)
  | truth (value : Bool)
  | not (query : BooleanQuery Atom)
  | and (left right : BooleanQuery Atom)
  | or (left right : BooleanQuery Atom)

namespace BooleanQuery

variable {A B : Type*}

def map (f : A → B) : BooleanQuery A → BooleanQuery B
  | .atom test => .atom (f test)
  | .truth value => .truth value
  | .not query => .not (query.map f)
  | .and left right => .and (left.map f) (right.map f)
  | .or left right => .or (left.map f) (right.map f)

def eval (test : A → Bool) : BooleanQuery A → Bool
  | .atom predicate => test predicate
  | .truth value => value
  | .not query => !(query.eval test)
  | .and left right => left.eval test && right.eval test
  | .or left right => left.eval test || right.eval test

end BooleanQuery

namespace TableQuery

variable {Kind : Type v} {Cell : Kind → Type w} {S T : QuerySchema.{u, v} Kind}

abbrev Sentence (Cell : Kind → Type w) (S : QuerySchema.{u, v} Kind) :=
  BooleanQuery (Row S.kind Cell → Bool)

/-- Translation runs the source test on the target row pulled back along the column map. -/
def translate (f : S ⟶ T) (q : Sentence Cell S) : Sentence Cell T :=
  q.map fun test => test ∘ f.pullRow id

/-- Pull back each row in place, preserving the list length and its positions. -/
def reduct (f : S ⟶ T) (table : Table T.kind Cell) : Table S.kind Cell :=
  table.map (f.pullRow id)

def eval (table : Table S.kind Cell) (q : Sentence Cell S) : Bool :=
  q.eval table.any

/-- Column-oriented evaluation uses the native aligned-columns readback. -/
def evalColumns (columns : AlignedColumns S.kind Cell) (q : Sentence Cell S) : Bool :=
  eval columns.toRows q

/-- The same reduct on aligned columns, retaining the row count even at width zero. -/
def reductColumns (f : S ⟶ T) (columns : AlignedColumns T.kind Cell) :
    AlignedColumns S.kind Cell :=
  AlignedColumns.ofRows (reduct f columns.toRows)

end TableQuery

/-- A database signature assigns a table signature to each occupied table index. -/
structure QueryCatalog (Kind : Type v) where
  Index : Type u
  schema : Index → QuerySchema.{u, v} Kind

namespace QueryCatalog

variable {Kind : Type v}

/-- A source table picks a target table and a kind-preserving column map into it. -/
structure Hom (S T : QueryCatalog.{u, v} Kind) where
  index : S.Index → T.Index
  columns : (i : S.Index) → S.schema i ⟶ T.schema (index i)

instance : Category (QueryCatalog.{u, v} Kind) where
  Hom := Hom
  id S := ⟨id, fun i => 𝟙 (S.schema i)⟩
  comp f g := ⟨g.index ∘ f.index, fun i => f.columns i ≫ g.columns (f.index i)⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- A native database over the occupied indices. Every index has a typed payload. -/
abbrev Model (Cell : Kind → Type w) (S : QueryCatalog.{u, v} Kind) :=
  Database.Over (fun i => some (S.schema i)) (fun s => Table s.kind Cell)

/-- Read a partial map at an occupied name. -/
def entryAt {Name : Type u} {Entry : Type*} (db : Database.Partial Name Entry)
    (i : Database.Support db) : Entry :=
  (db i.val).get (Option.ne_none_iff_isSome.mp i.property)

/-- Restrict a native partial catalog to its occupied names. -/
def ofCatalog {Name : Type u} {Schema : Type*} (catalog : Database.Catalog Name Schema)
    (schema : Schema → QuerySchema.{u, v} Kind) : QueryCatalog.{u, v} Kind where
  Index := Database.Support catalog
  schema i := schema (entryAt catalog i)

/-- Read the native typed payload at each occupied name, with a client-supplied row view. -/
def modelOfOver {Name : Type u} {Schema : Type*} {Tables : Schema → Type*}
    {catalog : Database.Catalog Name Schema} {schema : Schema → QuerySchema.{u, v} Kind}
    {Cell : Kind → Type w} (rows : (s : Schema) → Tables s → Table (schema s).kind Cell)
    (db : Database.Over catalog Tables) : Model Cell (ofCatalog catalog schema) :=
  fun i => rows _ (db.lookup i.val (Option.some_get _).symm)

/-- The packed form already contains the schema and its typed payload together. -/
def ofPacked {Name : Type u} {Schema : Type*} {Tables : Schema → Type*}
    (db : Database.Packed Name Tables) (schema : Schema → QuerySchema.{u, v} Kind) :
    QueryCatalog.{u, v} Kind :=
  ofCatalog db (schema ∘ Sigma.fst)

/-- Use the packed payload directly. No lookup cast or default table is required. -/
def modelOfPacked {Name : Type u} {Schema : Type*} {Tables : Schema → Type*}
    {db : Database.Packed Name Tables} {schema : Schema → QuerySchema.{u, v} Kind}
    {Cell : Kind → Type w} (rows : (s : Schema) → Tables s → Table (schema s).kind Cell) :
    Model Cell (ofPacked db schema) :=
  fun i =>
    let entry := entryAt db i
    rows entry.fst entry.snd

/-- Regard a table signature as a one-table catalog, functorially. -/
def singleton : QuerySchema.{u, v} Kind ⥤ QueryCatalog.{u, v} Kind where
  obj S := ⟨PUnit, fun _ => S⟩
  map f := ⟨id, fun _ => f⟩

/-- A table and the native database over its singleton signature carry the same data. -/
def singletonModel (Cell : Kind → Type w) (S : QuerySchema.{u, v} Kind) :
    Table S.kind Cell ≃ Model Cell (singleton.obj S) where
  toFun table _ := table
  invFun db := db PUnit.unit
  left_inv _ := rfl
  right_inv db := funext fun i => by cases i; rfl

end QueryCatalog

namespace DatabaseQuery

variable {Kind : Type v} {Cell : Kind → Type w} {S T : QueryCatalog.{u, v} Kind}

abbrev Sentence (Cell : Kind → Type w) (S : QueryCatalog.{u, v} Kind) :=
  BooleanQuery ((i : S.Index) × (Row (S.schema i).kind Cell → Bool))

/-- Rename the selected table and translate its row test along the corresponding column map. -/
def translate (f : S ⟶ T) (q : Sentence Cell S) : Sentence Cell T :=
  q.map fun ⟨i, test⟩ => ⟨f.index i, test ∘ (f.columns i).pullRow id⟩

def reduct (f : S ⟶ T) (db : QueryCatalog.Model Cell T) : QueryCatalog.Model Cell S :=
  fun i => TableQuery.reduct (f.columns i) (db (f.index i))

def eval (db : QueryCatalog.Model Cell S) (q : Sentence Cell S) : Bool :=
  q.eval fun ⟨i, test⟩ => (db i).any test

/-- Run a table sentence at a selected database component. -/
def select (i : S.Index) (q : TableQuery.Sentence Cell (S.schema i)) : Sentence Cell S :=
  q.map fun test => ⟨i, test⟩

end DatabaseQuery
end Silmaril.Relational

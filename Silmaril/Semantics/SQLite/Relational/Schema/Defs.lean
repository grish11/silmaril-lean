module

public import Silmaril.Semantics.Relational.Table.Thms

/-! Resolved SQLite table declarations and the value operations required by D2. -/

@[expose] public section

namespace Silmaril.SQLite.Relational

inductive TypingMode where
  | dynamic
  | strict
  deriving DecidableEq, Repr

/-- The six STRICT type names. INT and INTEGER have the same storage type but
different implications when resolving a ROWID alias. -/
inductive StrictTypeName where
  | int
  | integer
  | real
  | text
  | blob
  | any
  deriving DecidableEq, Repr

inductive DeclaredColumnType (Affinity : Type) : TypingMode → Type where
  | dynamic (declaration : Option String) (affinity : Affinity) : DeclaredColumnType Affinity .dynamic
  | dynamicAny : DeclaredColumnType Affinity .dynamic
  | strict (type : StrictTypeName) : DeclaredColumnType Affinity .strict

/-- Operations provided by the value model. `strictMatches` recognizes the
logical stored type of a non-NULL value. `coerceStrict` can reject an input.
D2 handles NULL and STRICT ANY without calling either strict type operation. -/
structure ValueModel (Value Affinity : Type) where
  isNull : Value → Bool
  asRowId : Value → Option Int64
  applyAffinity : Affinity → Value → Option Value
  numericAffinity : Affinity
  strictMatches : StrictTypeName → Value → Bool
  coerceStrict : StrictTypeName → Value → Option Value

namespace DeclaredColumnType

variable {Value Affinity : Type} {mode : TypingMode}

def accepts (model : ValueModel Value Affinity) : DeclaredColumnType Affinity mode → Value → Bool
  | .dynamic .., _ | .dynamicAny, _ | .strict .any, _ => true
  | .strict type, value => model.isNull value || model.strictMatches type value

abbrev Cell (model : ValueModel Value Affinity) (type : DeclaredColumnType Affinity mode) :=
  {value : Value // type.accepts model value = true}

/-- Resolved ROWID aliases require the declared type name INTEGER. -/
def canAliasRowId : DeclaredColumnType Affinity mode → Bool
  | .dynamic declaration _ => declaration.any (fun name => name.toUpper == "INTEGER")
  | .strict .integer => true
  | _ => false

def coerce (model : ValueModel Value Affinity) : DeclaredColumnType Affinity mode → Value → Option Value
  | .dynamic _ affinity, input => model.applyAffinity affinity input
  | .dynamicAny, input => model.applyAffinity model.numericAffinity input
  | .strict .any, input => some input
  | .strict strictType, input => if model.isNull input then some input else model.coerceStrict strictType input

/-- Apply write coercion, then check the stored-type contract supplied by the model. -/
def store (model : ValueModel Value Affinity) (type : DeclaredColumnType Affinity mode) (input : Value) :
    Option (type.Cell model) := do
  let value ← type.coerce model input
  if h : type.accepts model value = true then some ⟨value, h⟩ else none

end DeclaredColumnType

inductive TableOrganization (Column : Type) where
  | rowid (aliasColumn : Option Column)
  | withoutRowid

def TableOrganization.RowId {Column : Type} : TableOrganization Column → Type
  | .rowid _ => Int64
  | .withoutRowid => PUnit

def TableOrganization.rowId? {Column : Type} : (org : TableOrganization Column) → org.RowId → Option Int64
  | .rowid _, id => some id
  | .withoutRowid, _ => none

inductive GeneratedStorage where
  | virtual
  | stored
  deriving DecidableEq, Repr

structure Generation (Expr Column : Type) where
  storage : GeneratedStorage
  expression : Expr
  inputs : List Column

/-- A nonempty sequence of key columns, in declaration order. -/
structure Key (Column : Type) where
  first : Column
  rest : List Column

def Key.columns {Column : Type} (key : Key Column) : List Column :=
  key.first :: key.rest

/-- A resolved child key and an explicit sequence of parent column names. -/
structure ForeignKey (Column : Type) where
  child : Key Column
  parentTable : String
  parentColumns : Key String

structure Column (Affinity : Type) (mode : TypingMode) where
  name : String
  type : DeclaredColumnType Affinity mode
  collation : Option String := none
  notNull : Bool := false

/-- Resolved declarations for ordinary tables in one database. Column names
use exact equality on already normalized names. Expression handles are
interpreted separately. Generated expressions may depend on supplied columns. -/
structure TableSchema (Affinity Expr : Type) where
  mode : TypingMode
  width : Nat
  column : Fin width → Column Affinity mode
  uniqueNames : Function.Injective (fun i => (column i).name)
  organization : TableOrganization (Fin width)
  generation : Fin width → Option (Generation Expr (Fin width))
  suppliedExists : ∃ i, generation i = none
  inputsSupplied : ∀ i spec, generation i = some spec → ∀ j ∈ spec.inputs, generation j = none
  primaryKey : Option (Key (Fin width)) := none
  primaryKeySupplied : ∀ key, primaryKey = some key → ∀ i ∈ key.columns, generation i = none
  organizationKey : match organization with
    | .rowid none => True
    | .rowid (some i) =>
      (column i).type.canAliasRowId = true ∧ ∃ key, primaryKey = some key ∧ key.columns = [i]
    | .withoutRowid => primaryKey.isSome = true
  uniqueKeys : List (Key (Fin width)) := []
  checks : List Expr := []
  foreignKeys : List (ForeignKey (Fin width)) := []

namespace TableSchema

variable {Affinity Expr : Type} (schema : TableSchema Affinity Expr)

abbrev Index := Fin schema.width

def name (i : schema.Index) : String := (schema.column i).name

def kind (i : schema.Index) : DeclaredColumnType Affinity schema.mode := (schema.column i).type

def findColumn (name : String) : Option schema.Index :=
  (List.finRange schema.width).find? fun i => schema.name i == name

noncomputable def named : Silmaril.Relational.NamedSchema String (DeclaredColumnType Affinity schema.mode) where
  present name := ∃ i, schema.name i = name
  kind name := schema.kind (Classical.choose name.property)

noncomputable def namedPositional : Silmaril.Relational.NamedPositionalSchema String (DeclaredColumnType Affinity schema.mode) where
  named := schema.named
  width := schema.width
  column :=
    { toFun := fun i => ⟨schema.name i, i, rfl⟩
      invFun := fun name => Classical.choose name.property
      left_inv := fun i => schema.uniqueNames (Classical.choose_spec
        (p := fun j => schema.name j = schema.name i) (show ∃ j, schema.name j = schema.name i from ⟨i, rfl⟩))
      right_inv := fun name => Subtype.ext (Classical.choose_spec name.property) }

abbrev Supplied := {i : schema.Index // schema.generation i = none}

/-- The generation specification and its position, with a proof that the pair
comes from this declaration. -/
abbrev Generated := {entry : schema.Index × Generation Expr schema.Index //
  schema.generation entry.1 = some entry.2}

def requiresPrimaryKeyNotNull : Bool :=
  match schema.organization, schema.mode with
  | .withoutRowid, _ | _, .strict => true
  | .rowid _, .dynamic => false

abbrev RowId := schema.organization.RowId

abbrev rowId? := schema.organization.rowId?

end TableSchema

end Silmaril.SQLite.Relational

module

public import Silmaril.Logic.RelationalQuery.Defs
public import Silmaril.Logic.Institution.Morphism
public import Mathlib.CategoryTheory.Discrete.Basic
import Silmaril.Proofs.Logic.RelationalQuery.Laws

@[expose] public section

namespace Silmaril.Relational

open CategoryTheory Silmaril.Logic.Institution

universe u v w

namespace TableQuery

variable {Kind : Type v} {Cell : Kind → Type w} {S T U : QuerySchema.{u, v} Kind}

@[simp] theorem translate_id (q : Sentence Cell S) : translate (𝟙 S) q = q :=
  QueryProofs.Table.translate_id q

theorem translate_comp (f : S ⟶ T) (g : T ⟶ U) (q : Sentence Cell S) :
    translate (f ≫ g) q = translate g (translate f q) :=
  QueryProofs.Table.translate_comp f g q

@[simp] theorem reduct_id (table : Table S.kind Cell) : reduct (𝟙 S) table = table :=
  List.map_id table

theorem reduct_comp (f : S ⟶ T) (g : T ⟶ U) (table : Table U.kind Cell) :
    reduct (f ≫ g) table = reduct f (reduct g table) :=
  QueryProofs.Table.reduct_comp f g table

theorem eval_translate (f : S ⟶ T) (table : Table T.kind Cell) (q : Sentence Cell S) :
    eval table (translate f q) = eval (reduct f table) q :=
  QueryProofs.Table.eval_translate f table q

/-- Existence sentences depend only on row membership. -/
theorem eval_eq_of_mem_iff {left right : Table S.kind Cell}
    (h : ∀ row, row ∈ left ↔ row ∈ right) (q : Sentence Cell S) : eval left q = eval right q := by
  apply congrArg (fun test => q.eval test)
  funext test
  exact Bool.eq_iff_iff.mpr (by simp only [List.any_eq_true, h])

@[simp] theorem evalColumns_ofRows (table : Table S.kind Cell) (q : Sentence Cell S) :
    evalColumns (AlignedColumns.ofRows table) q = eval table q := by
  simp [evalColumns]

@[simp] theorem toRows_reductColumns (f : S ⟶ T) (columns : AlignedColumns T.kind Cell) :
    (reductColumns f columns).toRows = reduct f columns.toRows :=
  AlignedColumns.toRows_ofRows _

@[simp] theorem reductColumns_ofRows (f : S ⟶ T) (table : Table T.kind Cell) :
    reductColumns f (AlignedColumns.ofRows table) = AlignedColumns.ofRows (reduct f table) := by
  simp [reductColumns]

@[simp] theorem reductColumns_rowCount (f : S ⟶ T) (columns : AlignedColumns T.kind Cell) :
    (reductColumns f columns).rowCount = columns.rowCount := by
  simp [reductColumns, AlignedColumns.ofRows, reduct]

@[simp] theorem reductColumns_id (columns : AlignedColumns S.kind Cell) :
    reductColumns (𝟙 S) columns = columns := by
  simp [reductColumns]

theorem reductColumns_comp (f : S ⟶ T) (g : T ⟶ U) (columns : AlignedColumns U.kind Cell) :
    reductColumns (f ≫ g) columns = reductColumns f (reductColumns g columns) := by
  simp [reductColumns, reduct_comp]

theorem evalColumns_translate (f : S ⟶ T) (columns : AlignedColumns T.kind Cell)
    (q : Sentence Cell S) : evalColumns columns (translate f q) = evalColumns (reductColumns f columns) q := by
  simp [evalColumns, eval_translate f]

variable (Cell)

/-- The models are the actual list tables, with discrete model morphisms. -/
def room (S : QuerySchema.{u, v} Kind) : Room.{max u w, max u w, max u w} :=
  ⟨Sentence Cell S, Cat.of (Discrete (Table S.kind Cell)), fun table q => eval table.as q = true⟩

def corridor (f : S ⟶ T) : room Cell S ⟶ room Cell T :=
  ⟨translate f, Discrete.functor fun table => Discrete.mk (reduct f table),
    fun table q => Iff.of_eq (congrArg (· = true) (eval_translate f table.as q))⟩

/-- The institution of Boolean queries over a single typed table. -/
def institution : Inst.{max (u + 1) v, u, max u w, max u w, max u w} where
  Sign := QuerySchema.{u, v} Kind
  I := {
    obj := room Cell
    map := corridor Cell
    map_id s := by
      apply Room.hom_ext (funext translate_id)
      exact QueryProofs.discreteFunctor_ext fun t => congrArg Discrete.mk (reduct_id (S := s) t.as)
    map_comp f g := by
      apply Room.hom_ext (funext (translate_comp f g))
      exact QueryProofs.discreteFunctor_ext fun t => congrArg Discrete.mk (reduct_comp f g t.as) }

end TableQuery

namespace DatabaseQuery

variable {Kind : Type v} {Cell : Kind → Type w} {S T U : QueryCatalog.{u, v} Kind}

@[simp] theorem translate_id (q : Sentence Cell S) : translate (𝟙 S) q = q :=
  QueryProofs.Database.translate_id q

theorem translate_comp (f : S ⟶ T) (g : T ⟶ U) (q : Sentence Cell S) :
    translate (f ≫ g) q = translate g (translate f q) :=
  QueryProofs.Database.translate_comp f g q

@[simp] theorem reduct_id (db : QueryCatalog.Model Cell S) : reduct (𝟙 S) db = db :=
  funext fun i => TableQuery.reduct_id (db i)

theorem reduct_comp (f : S ⟶ T) (g : T ⟶ U) (db : QueryCatalog.Model Cell U) :
    reduct (f ≫ g) db = reduct f (reduct g db) :=
  funext fun i => TableQuery.reduct_comp (f.columns i) (g.columns (f.index i)) (db (g.index (f.index i)))

theorem eval_translate (f : S ⟶ T) (db : QueryCatalog.Model Cell T) (q : Sentence Cell S) :
    eval db (translate f q) = eval (reduct f db) q :=
  QueryProofs.Database.eval_translate f db q

/-- Selecting one component commutes with evaluation. -/
theorem eval_select (db : QueryCatalog.Model Cell S) (i : S.Index)
    (q : TableQuery.Sentence Cell (S.schema i)) : eval db (select i q) = TableQuery.eval (db i) q :=
  QueryProofs.Database.eval_select db i q

/-- Selecting one component commutes with translation and the corresponding column map. -/
theorem translate_select (f : S ⟶ T) (i : S.Index) (q : TableQuery.Sentence Cell (S.schema i)) :
    translate f (select i q) = select (f.index i) (TableQuery.translate (f.columns i) q) :=
  QueryProofs.Database.translate_select f i q

/-- Taking a component of a reduced database is the corresponding table reduct. -/
theorem reduct_component (f : S ⟶ T) (db : QueryCatalog.Model Cell T) (i : S.Index) :
    reduct f db i = TableQuery.reduct (f.columns i) (db (f.index i)) := rfl

variable (Cell)

/-- The models are native databases over the occupied table indices. -/
def room (S : QueryCatalog.{u, v} Kind) : Room.{max u w, max u w, max u w} :=
  ⟨Sentence Cell S, Cat.of (Discrete (QueryCatalog.Model Cell S)), fun db q => eval db.as q = true⟩

def corridor (f : S ⟶ T) : room Cell S ⟶ room Cell T :=
  ⟨translate f, Discrete.functor fun db => Discrete.mk (reduct f db),
    fun db q => Iff.of_eq (congrArg (· = true) (eval_translate f db.as q))⟩

/-- The institution of Boolean queries over typed databases. -/
def institution : Inst.{max (u + 1) v, u, max u w, max u w, max u w} where
  Sign := QueryCatalog.{u, v} Kind
  I := {
    obj := room Cell
    map := corridor Cell
    map_id s := by
      apply Room.hom_ext (funext translate_id)
      exact QueryProofs.discreteFunctor_ext fun db => congrArg Discrete.mk (reduct_id (S := s) db.as)
    map_comp f g := by
      apply Room.hom_ext (funext (translate_comp f g))
      exact QueryProofs.discreteFunctor_ext fun db => congrArg Discrete.mk (reduct_comp f g db.as) }

/-- Selecting a table translates its sentences into the database and projects its models out. -/
def componentCorridor (i : S.Index) : TableQuery.room Cell (S.schema i) ⟶ room Cell S :=
  ⟨select i, Discrete.functor fun db => Discrete.mk (db i),
    fun db q => Iff.of_eq (congrArg (· = true) (eval_select db.as i q))⟩

theorem componentCorridor_comm (f : S ⟶ T) (i : S.Index) :
    componentCorridor Cell i ≫ corridor Cell f =
      TableQuery.corridor Cell (f.columns i) ≫ componentCorridor Cell (f.index i) := by
  apply Room.hom_ext (funext (translate_select f i))
  exact QueryProofs.discreteFunctor_ext fun _ => rfl

/-- The singleton embedding translates table sentences and reads back singleton models. -/
def singletonComorphism : Inst.CoHom
    (TableQuery.institution.{u, v, w} Cell) (institution.{u, v, w} Cell) where
  Φ := QueryCatalog.singleton
  ρ := {
    app := fun s => componentCorridor Cell (S := QueryCatalog.singleton.obj s) PUnit.unit
    naturality := fun _ _ f => (componentCorridor_comm Cell (QueryCatalog.singleton.map f) PUnit.unit).symm }

end DatabaseQuery
end Silmaril.Relational

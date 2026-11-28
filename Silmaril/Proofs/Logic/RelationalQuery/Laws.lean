module

public import Silmaril.Logic.RelationalQuery.Defs
public import Mathlib.CategoryTheory.Discrete.Basic

public section

namespace Silmaril.Relational.QueryProofs

open CategoryTheory

universe u v w

theorem discreteFunctor_ext {C M : Type*} [Category C] {F G : C ⥤ Discrete M}
    (h : ∀ x, F.obj x = G.obj x) : F = G :=
  CategoryTheory.Functor.ext h (fun _ _ _ => Subsingleton.elim _ _)

namespace BooleanQuery

variable {A B C : Type*}

theorem map_id (q : BooleanQuery A) : q.map id = q := by
  induction q <;> simp [Relational.BooleanQuery.map, *]

theorem map_map (f : A → B) (g : B → C) (q : BooleanQuery A) :
    (q.map f).map g = q.map (g ∘ f) := by
  induction q <;> simp [Relational.BooleanQuery.map, *]

theorem eval_map (f : A → B) (test : B → Bool) (q : BooleanQuery A) :
    (q.map f).eval test = q.eval (test ∘ f) := by
  induction q <;> simp [Relational.BooleanQuery.map, Relational.BooleanQuery.eval, *]

end BooleanQuery

namespace Table

open TableQuery

variable {Kind : Type v} {Cell : Kind → Type w} {S T U : QuerySchema.{u, v} Kind}

theorem translate_id (q : Sentence Cell S) : translate (𝟙 S) q = q :=
  BooleanQuery.map_id q

theorem translate_comp (f : S ⟶ T) (g : T ⟶ U) (q : Sentence Cell S) :
    translate (f ≫ g) q = translate g (translate f q) := by
  unfold translate
  rw [BooleanQuery.map_map]
  congr
  funext test row
  exact congrArg test (ColumnMap.pullRow_comp id f g row)

theorem reduct_comp (f : S ⟶ T) (g : T ⟶ U) (table : Relational.Table U.kind Cell) :
    reduct (f ≫ g) table = reduct f (reduct g table) := by
  simp only [reduct, List.map_map]
  congr
  funext row
  exact ColumnMap.pullRow_comp id f g row

theorem eval_translate (f : S ⟶ T) (table : Relational.Table T.kind Cell)
    (q : Sentence Cell S) : eval table (translate f q) = eval (reduct f table) q := by
  unfold eval translate reduct
  rw [BooleanQuery.eval_map]
  apply congrArg (fun run => q.eval run)
  funext test
  exact List.any_map.symm

end Table

namespace Database

open DatabaseQuery

variable {Kind : Type v} {Cell : Kind → Type w} {S T U : QueryCatalog.{u, v} Kind}

theorem translate_id (q : Sentence Cell S) : translate (𝟙 S) q = q := by
  unfold translate
  refine Eq.trans ?_ (BooleanQuery.map_id q)
  apply congrArg (fun f => q.map f)
  funext a
  cases a
  rfl

theorem translate_comp (f : S ⟶ T) (g : T ⟶ U) (q : Sentence Cell S) :
    translate (f ≫ g) q = translate g (translate f q) := by
  unfold translate
  rw [BooleanQuery.map_map]
  apply congrArg (fun f => q.map f)
  funext atom
  rcases atom with ⟨i, test⟩
  apply congrArg (Sigma.mk (β := fun j => Row (U.schema j).kind Cell → Bool) (g.index (f.index i)))
  funext row
  exact congrArg test (ColumnMap.pullRow_comp id (f.columns i) (g.columns (f.index i)) row)

theorem eval_translate (f : S ⟶ T) (db : QueryCatalog.Model Cell T) (q : Sentence Cell S) :
    eval db (translate f q) = eval (reduct f db) q := by
  unfold eval translate reduct
  rw [BooleanQuery.eval_map]
  apply congrArg (fun run => q.eval run)
  funext atom
  rcases atom with ⟨i, test⟩
  exact List.any_map.symm

theorem eval_select (db : QueryCatalog.Model Cell S) (i : S.Index)
    (q : TableQuery.Sentence Cell (S.schema i)) : eval db (select i q) = TableQuery.eval (db i) q :=
  BooleanQuery.eval_map _ _ _

theorem translate_select (f : S ⟶ T) (i : S.Index) (q : TableQuery.Sentence Cell (S.schema i)) :
    translate f (select i q) = select (f.index i) (TableQuery.translate (f.columns i) q) := by
  unfold translate select TableQuery.translate
  rw [BooleanQuery.map_map, BooleanQuery.map_map]
  rfl

end Database
end Silmaril.Relational.QueryProofs

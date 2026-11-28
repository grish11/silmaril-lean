module

import Silmaril.Logic.RelationalQuery.Thms

namespace Silmaril.Relational.QueryChecks

open CategoryTheory

private def narrow : QuerySchema Type := ⟨Unit, fun _ => Nat⟩

private def wide : QuerySchema Type := ⟨Bool, fun i => if i then Bool else Nat⟩

private def pickNumber : narrow ⟶ wide := ⟨fun _ => false, fun _ => rfl⟩

private def wideRow (n : Nat) : Row wide.kind id
  | false => n
  | true => true

private def wideRows : Table wide.kind id := [wideRow 7, wideRow 3, wideRow 7]

private def numberQuery : TableQuery.Sentence id narrow :=
  .and (.atom fun row => Nat.beq (row ()) 7) (.not (.atom fun row => Nat.beq (row ()) 8))

example : TableQuery.eval wideRows (TableQuery.translate pickNumber numberQuery) = true := rfl

example : (TableQuery.reduct pickNumber wideRows).map (fun row => (row () : Nat)) = [7, 3, 7] := rfl

private def zero : QuerySchema Type :=
  QuerySchema.ofPositional.obj ⟨0, Fin.elim0⟩

private def forgetAll : zero ⟶ wide := ⟨Fin.elim0, fun i => Fin.elim0 i⟩

example : (TableQuery.reductColumns forgetAll (AlignedColumns.ofRows wideRows)).rowCount = 3 := rfl

example : TableQuery.evalColumns (TableQuery.reductColumns forgetAll (AlignedColumns.ofRows wideRows))
    (.atom fun _ => true) = true := rfl

private def twoTables : QueryCatalog Type := ⟨Bool, fun _ => wide⟩

private def model : QueryCatalog.Model id twoTables
  | false => []
  | true => wideRows

private def selectNonempty : QueryCatalog.singleton.obj narrow ⟶ twoTables :=
  ⟨fun _ => true, fun _ => pickNumber⟩

example : DatabaseQuery.eval model
    (DatabaseQuery.translate selectNonempty (DatabaseQuery.select PUnit.unit numberQuery)) = true := rfl

example : DatabaseQuery.eval model (.and (.atom ⟨true, fun _ => true⟩)
    (.not (.atom ⟨false, fun _ => true⟩))) = true := rfl

private def catalog : Database.Catalog Bool (QuerySchema Type)
  | false => some narrow
  | true => none

private def db : Database.Over catalog (fun s => Table s.kind id)
  | false => []
  | true => PUnit.unit

private def catalogIndex : (QueryCatalog.ofCatalog catalog id).Index := ⟨false, by decide⟩

example : DatabaseQuery.eval (QueryCatalog.modelOfOver (schema := id) (fun _ rows => rows) db)
    (.atom ⟨catalogIndex, fun _ => true⟩) = false := rfl

end Silmaril.Relational.QueryChecks

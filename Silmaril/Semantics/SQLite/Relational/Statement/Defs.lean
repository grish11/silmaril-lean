module

public import Silmaril.Semantics.Relational.Query.Result

@[expose] public section

namespace Silmaril.SQLite.Relational

/-- The catalog layer supplies the reference for the single projection in
`SELECT column FROM table WHERE rowid = ?1`. -/
structure Statement (Ref : Type) where
  source : Ref

/-- The backend target and the column label exposed by preparation. -/
structure Plan (Target : Type) where
  target : Target
  label : String

/-- The one-slot plan is initially unbound, which SQLite interprets as NULL. -/
structure Prepared (Target : Type) where
  plan : Plan Target
  key : Option Int64 := none

inductive BindError where
  | range
  deriving DecidableEq, Repr

/-- An out-of-range index returns the previous bindings along with the error. -/
def Prepared.bindInt64 {Target : Type} (stmt : Prepared Target) (index : Int32)
    (key : Int64) : Except BindError Unit × Prepared Target :=
  if index = 1 then (.ok (), { stmt with key := some key })
  else (.error .range, stmt)

/-- One fresh use of the plan, with either an unset parameter or one bind call. -/
structure Invocation (Ref : Type) where
  statement : Statement Ref
  binding : Option (Int32 × Int64) := none

inductive StatementError (PrepareError ReadError : Type) where
  | prepare (error : PrepareError)
  | bind (error : BindError)
  | run (error : ReadError)
  deriving DecidableEq, Repr

/-- A zero-or-one-row result. A present cell can itself be SQL NULL. The
column label is available even if no row is returned. -/
structure SelectResult (Value : Type) where
  label : String
  cell : Option Value
  deriving DecidableEq, Repr

/-- Materialize the point result as a Track C row collection. -/
def SelectResult.toOutput {Value : Type} (result : SelectResult Value) :
    Silmaril.Relational.Output Value Empty String Unit :=
  .rows ⟨result.label, ()⟩ (.ordered result.cell.toList)

end Silmaril.SQLite.Relational

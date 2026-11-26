module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Defs
public import Silmaril.Numeric.Ieee754.CoreFloat
import Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.ClosedGuard

public section
namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions.ClosedGuard

open Silmaril.Numeric.Ieee754 (F64)

theorem select_iff (operator : Source.BooleanOperator) (first : Value)
    (rest : List Value) (result : Value) :
    select operator first rest = result ↔ Selects operator first rest result :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.ClosedGuard.select_iff operator first rest result

theorem checkedLinks_iff (left : Value) (links : List (Source.Comparison × Value)) (results : List Bool) :
    checkedLinks left links = some results ↔ ChecksLinks left links results :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.ClosedGuard.checkedLinks_iff left links results

theorem add_float_result {left right result : F64.Finite}
    (checked : binary? .add (.float left) (.float right) = some (.float result)) :
    result.val = F64.ofFloat (left.val.toFloat + right.val.toFloat) :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.ClosedGuard.add_float_result checked

theorem testFloat_runtime (operator : ScalarComparison) (left right : F64) :
    testFloat operator left right = (match operator with
      | .eq => left.toFloat == right.toFloat
      | .ne => !(left.toFloat == right.toFloat)
      | .lt => left.toFloat.lt right.toFloat
      | .le => left.toFloat.le right.toFloat
      | .gt => right.toFloat.lt left.toFloat
      | .ge => right.toFloat.le left.toFloat) :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.ClosedGuard.testFloat_runtime operator left right

theorem selected_pass {condition yes no value} (checked : Omitted (.if_ condition yes no) value) :
    ∀ statement ∈ (if value.truth then yes else no), statement = .pass :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.ClosedGuard.selected_pass checked

theorem ordinaryIf_omitted_none {scope : Source.Scope} {condition yes no actions}
    (checked : ModuleEntry.Translation scope [.if_ condition yes no] actions) :
    omitted? (.if_ condition yes no) = none := by
  cases checked with
  | assign binding _ _ => cases binding
  | literalIf arms _ _ _ _ => simp [omitted?, arms]

theorem lowerPlan_omitted {tree : Source.ScopeTree} {index : Nat}
    {condition : Source.Expr} {yes no rest : List Source.Stmt}
    {witness} (checked : omitted? (.if_ condition yes no) = some witness) :
    (lowerPlan tree index (.if_ condition yes no :: rest)).toOption.map Subtype.val =
      (lowerPlan tree index rest).toOption.map Subtype.val :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.ClosedGuard.lowerPlan_omitted checked

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.ClosedGuard

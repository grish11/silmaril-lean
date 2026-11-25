module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Defs

public section
namespace Silmaril.Proofs.Languages.Python.Compile.ModuleEntry

open Silmaril.Languages.Python
open Silmaril.Languages.Python.Compile.ModuleEntry

theorem global_reference {scope : Source.Scope} {name : Source.Name}
    (reference : GlobalReference scope name) : globalReference? scope name = some reference := by
  obtain ⟨_, resolved, moduleName | declared⟩ := reference
  · subst moduleName
    simp [globalReference?, resolved]
  · subst declared
    simp [globalReference?, resolved]

private theorem operand_complete {scope : Source.Scope} {source : Source.Expr} {operand : Operand scope}
    (translated : OperandTranslation scope source operand) :
    lowerOperand scope source = .ok ⟨operand, translated⟩ := by
  cases translated with
  | integer => rfl
  | read _ witness => simp [lowerOperand, global_reference witness] <;> rfl

theorem statements_complete {scope : Source.Scope} {source : List Source.Stmt} {actions : List (Action scope)}
    (translated : Translation scope source actions) : lowerStatements scope source = .ok ⟨actions, translated⟩ := by
  induction translated with
  | done => rfl
  | @assign statement name expression reference value rest next binding operand _ tail =>
    cases binding <;> simp [lowerStatements, binding?, global_reference reference, operand_complete operand, tail] <;> rfl
  | assertion operand _ tail => simp [lowerStatements, operand_complete operand, tail] <;> rfl
  | globals _ tail => simp [lowerStatements, tail] <;> rfl
  | pass _ tail => simp [lowerStatements, tail] <;> rfl

theorem check_complete {source : Source.Module} {tree : Source.ScopeTree}
    {actions : List (Action tree.scope)} (analyzed : Source.analyze source = .ok tree)
    (moduleScope : tree.scope.context.kind = .module_) (translated : Translation tree.scope source.body actions) :
    check source = .ok ⟨tree, analyzed, moduleScope, actions, translated⟩ := by
  unfold check
  split
  · rename_i _ rejected
    rw [analyzed] at rejected
    contradiction
  · rename_i other accepted
    have same := Except.ok.inj (accepted.symm.trans analyzed)
    subst other
    simp [moduleScope, statements_complete translated] <;> rfl

end Silmaril.Proofs.Languages.Python.Compile.ModuleEntry

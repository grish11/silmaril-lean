module

public import Silmaril.Languages.Starlark.Modules.Resolve.Operational.Defs
import all Silmaril.Languages.Starlark.Modules.Resolve.Defs
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Eval

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve

/-- A successful elaboration has the collected globals in source order,
direct commands without scratch locals, and passes resolved validation. -/
theorem checked_of_resolve {commands : List Command} {linked : Functions.Program} {resolved : ResolvedModule}
    (h : resolve commands linked = .ok resolved) :
    elaborateCommands commands linked = .ok (resolved.source.commands, resolved.program) ∧
      resolved.source.globals = globalNames commands ∧ resolved.source.temporaryNames = [] ∧
      validateSource resolved.program resolved.source = .ok () :=
  Proofs.Languages.Starlark.Modules.Resolve.checked_of_resolve h

/-- Exact adequacy after checked elaboration, including static rejection,
runtime errors, the final state and publication. -/
theorem initializes_iff_runModule (commands : List Command) (host : Catalog)
    (caller : Lists.State) (linked : Functions.Program) (out : Result) :
    Initializes commands host caller linked out ↔ runModule commands host caller linked = out :=
  ⟨Proofs.Languages.Starlark.Modules.Resolve.eq_runModule_of_initializes,
    fun h => h ▸ Proofs.Languages.Starlark.Modules.Resolve.initializes_runModule commands host caller linked⟩

open Functions Lowering.Resolve in
/-- A branch resolves its test in the collected block and compiles both suites
in order. The test introduces no declarations. -/
theorem compileBody_plainBranch (block : BlockContext) (test : Lowering.Resolve.SourceExpr)
    (yes no : Statement) (program middle final : Program) (condition : Lowering.Expr)
    (reads : List Binding) (consequent alternative : ResolvedBody)
    (operand : resolveTracked block.reads test = .ok (condition, reads))
    (compiledYes : compileBody block yes program = .ok (consequent, middle))
    (compiledNo : compileBody block no middle = .ok (alternative, final)) :
    compileBody block (.branch test yes no) program =
      .ok (⟨.branchExpr condition consequent.code alternative.code,
        reads ++ consequent.reads ++ alternative.reads⟩, final) := by
  simp [compileBody, readExpr, operand, compiledYes, compiledNo, Except.mapError,
    bind, StateT.bind, Except.bind, lift_ok, pure, StateT.pure, Except.pure]

end Silmaril.Languages.Starlark.Modules.Resolve

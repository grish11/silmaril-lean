module

public import Silmaril.Languages.Python.Core.Module.Functions.Defs
public import Silmaril.Languages.Python.Core.Closure.Executor.Thms
import Silmaril.Proofs.Languages.Python.Core.Module.Functions.Correspondence

public section

namespace Silmaril.Languages.Python.Core.Module.Functions

open Core.Closure

theorem Session.bind_lookup (session : Session) (name : GlobalName) (value : Closure.Value) :
    (session.bindGlobal name value).globals name = some value := by simp [Session.bindGlobal]

theorem Session.bind_other (session : Session) {name query : GlobalName}
    (value : Closure.Value) (different : query ≠ name) :
    (session.bindGlobal name value).globals query = session.globals query := by simp [Session.bindGlobal, different]

theorem Session.unbind_lookup (session : Session) (name : GlobalName) :
    (session.unbindGlobal name).globals name = none := by simp [Session.unbindGlobal]

theorem Session.unbind_other (session : Session) {name query : GlobalName} (different : query ≠ name) :
    (session.unbindGlobal name).globals query = session.globals query := by
  simp [Session.unbindGlobal, different]

theorem Session.publish_iff {session updated : Session} {table : Executor.CodeTable} {name : GlobalName}
    {function : TopFunction} : session.publish table name function = .ok updated ↔
      (∃ definition, Dispatch.Resolves table function.ref definition) ∧
        updated = session.bindGlobal name function.value :=
  Proofs.Languages.Python.Core.Module.Functions.publish_iff

theorem Session.prepare_globals (session : Session) (destination : Destination) (callee : Operand)
    (arguments : List Operand) : (session.prepareCall destination callee arguments).globals = session.globals :=
  rfl

theorem Session.prepare_lists (session : Session) (destination : Destination) (callee : Operand)
    (arguments : List Operand) : (session.prepareCall destination callee arguments).lists = session.lists :=
  rfl

theorem Invocation.run_globals (invocation : Invocation) (table : Executor.CodeTable) (fuel : Nat) :
    (invocation.runPrefix table fuel).2.globals = invocation.globals := rfl

theorem Invocation.run_path (invocation : Invocation) (table : Executor.CodeTable) (fuel : Nat) :
    (Executor.labelledIn table invocation.globals).Path invocation.state
      (invocation.runPrefix table fuel).1 (invocation.runPrefix table fuel).2.state :=
  Executor.runIn_path table invocation.globals fuel invocation.state

theorem Invocation.finish_iff {invocation : Invocation} {observation : Observation} :
    invocation.finish? = some observation ↔
      Settles invocation.globals invocation.lists invocation.destination invocation.state observation :=
  Proofs.Languages.Python.Core.Module.Functions.finish_iff

theorem Invocation.finish_lists {invocation : Invocation} {observation : Observation}
    (finished : invocation.finish? = some observation) :
    observation.residual.lists = invocation.lists := by
  obtain ⟨globals, destination, state, lists⟩ := invocation
  cases Invocation.finish_iff.mp finished <;> rfl

end Silmaril.Languages.Python.Core.Module.Functions

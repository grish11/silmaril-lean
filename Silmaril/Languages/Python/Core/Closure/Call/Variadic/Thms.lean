module

public import Silmaril.Languages.Python.Core.Closure.Call.Variadic.Defs
public import Silmaril.Languages.Python.Core.Closure.Call.Thms
import Silmaril.Proofs.Languages.Python.Core.Closure.Call.Variadic.Binding

public section
namespace Silmaril.Languages.Python.Core.Closure.Call

theorem collectPositionals_iff {Operand State : Type} {read : ReadOperand Operand State}
    {parts : List (PositionalOperand Operand)} {state : State} {result} :
    collectPositionals read parts state = result ↔ CollectsPositionals read parts state result :=
  Proofs.Languages.Python.Core.Closure.Call.Variadic.collect_iff

theorem prepare_callee_failure {Operand State : Type} {read : ReadOperand Operand State}
    {callee : Operand} {parts : List (PositionalOperand Operand)} {state reached : State} {failure : Failure}
    (selected : read callee state = (.error failure, reached)) :
    preparePositionalCall read callee parts state = (.error (.operand failure), reached) := by
  simp [preparePositionalCall, selected]

theorem prepare_saved_callee {Operand State : Type} {read : ReadOperand Operand State}
    {callee : Operand} {parts : List (PositionalOperand Operand)} {state reached final : State}
    {value : Value} {values : List Value}
    (selected : read callee state = (.ok value, reached))
    (supplied : CollectsPositionals read parts reached (.ok values, final)) :
    preparePositionalCall read callee parts state = (.ok (value, values), final) := by
  simp [preparePositionalCall, selected, collectPositionals_iff.mpr supplied, Except.map]

namespace VariadicParameters

variable {layout : Layout} {parameters : VariadicParameters layout}
  {supplied completed : List Value} {before after : Environment layout}

theorem complete_iff :
    parameters.complete supplied = .ok completed ↔
      parameters.fixed.slots.length ≤ supplied.length ∧
      ∃ items : List Core.Module.Value,
        (supplied.drop parameters.fixed.slots.length).mapM Value.scalar? = some items ∧
        completed = supplied.take parameters.fixed.slots.length ++ [.tuple (items.map .scalar)] :=
  Proofs.Languages.Python.Core.Closure.Call.Variadic.complete_iff

theorem complete_length (done : parameters.complete supplied = .ok completed) :
    completed.length = parameters.destinations.slots.length :=
  Proofs.Languages.Python.Core.Closure.Call.Variadic.complete_length done

theorem complete_exact (arity : supplied.length = parameters.fixed.slots.length) :
    parameters.complete supplied = .ok (supplied ++ [.tuple []]) := by
  apply complete_iff.mpr
  exact ⟨arity.ge, [], by simp [← arity]⟩

theorem bind_iff :
    parameters.bind supplied before = .ok after ↔
      ∃ values, parameters.complete supplied = .ok values ∧
        Writes (parameters.destinations.slots.zip values) before after :=
  Proofs.Languages.Python.Core.Closure.Call.Variadic.bind_iff

theorem bind_too_few (short : supplied.length < parameters.fixed.slots.length) :
    parameters.bind supplied before = .error (.defined (.positionalArity parameters.fixed.slots.length supplied.length)) := by
  simp [bind, complete, short, Except.bind]

theorem bind_fixed {slot : ParameterSlot layout} {value : Value}
    (bound : parameters.bind supplied before = .ok after)
    (member : (slot, value) ∈ parameters.fixed.slots.zip (supplied.take parameters.fixed.slots.length))
    (unique : Function.Injective before.2.owned) :
    after.2.read after.1 slot.slot = .ok value :=
  Proofs.Languages.Python.Core.Closure.Call.Variadic.bind_fixed bound member unique

theorem bind_rest {items : List Core.Module.Value}
    (bound : parameters.bind supplied before = .ok after)
    (packed : (supplied.drop parameters.fixed.slots.length).mapM Value.scalar? = some items)
    (unique : Function.Injective before.2.owned) :
    after.2.read after.1 parameters.rest.slot = .ok (.tuple (items.map .scalar)) :=
  Proofs.Languages.Python.Core.Closure.Call.Variadic.bind_rest bound packed unique

variable {Continuation : Layout → Type} {fn : Function}
  {parameters : VariadicParameters fn.code.layout} {heap : Heap} {caller : Saved Continuation}
  {stack : List (Saved Continuation)} {callee : Entered Continuation fn.code.layout}

theorem enter_spec (entered : parameters.enter fn supplied heap caller stack = .ok callee) :
    ∃ values, parameters.complete supplied = .ok values ∧
      Call.enter fn parameters.destinations values heap caller stack = .ok callee :=
  Proofs.Languages.Python.Core.Closure.Call.Variadic.enter_spec entered

theorem enter_preserves_cell (entered : parameters.enter fn supplied heap caller stack = .ok callee)
    {identity : CellId} (live : identity.address < heap.next) :
    callee.environment.1.lookup identity = heap.lookup identity := by
  obtain ⟨_, _, enteredFixed⟩ := enter_spec entered
  exact Call.enter_preserves_cell enteredFixed live

theorem finish_after_enter (entered : parameters.enter fn supplied heap caller stack = .ok callee)
    (residual : Heap) (result : Result) :
    finish residual callee.stack result = ⟨residual, stack, .resume caller result⟩ := by
  obtain ⟨_, _, enteredFixed⟩ := enter_spec entered
  exact Call.finish_after_enter enteredFixed residual result

end VariadicParameters
end Silmaril.Languages.Python.Core.Closure.Call

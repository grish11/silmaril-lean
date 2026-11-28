module

public import Silmaril.Languages.Python.Core.Closure.Call.Variadic.Defs
public import Silmaril.Languages.Python.Core.Closure.Call.Thms

public section
namespace Silmaril.Proofs.Languages.Python.Core.Closure.Call.Variadic

open Silmaril.Languages.Python.Core.Closure
open Silmaril.Languages.Python.Core.Closure.Call

theorem collect_iff {Operand State : Type} {read : ReadOperand Operand State}
    {parts : List (PositionalOperand Operand)} {state : State} {result} :
    collectPositionals read parts state = result ↔ CollectsPositionals read parts state result := by
  constructor
  · intro same
    subst result
    induction parts generalizing state with
    | nil => exact .nil state
    | cons head tail ih =>
      cases evaluated : head.evaluate read state with
      | mk result reached =>
        cases result with
        | error failure =>
          simpa only [collectPositionals, evaluated] using
            (CollectsPositionals.stop (tail := tail) evaluated)
        | ok values =>
          have remaining := ih (state := reached)
          cases collected : collectPositionals read tail reached with
          | mk result final =>
            rw [collected] at remaining
            simpa only [collectPositionals, evaluated, collected] using
              (CollectsPositionals.next evaluated remaining)
  · intro derivation
    induction derivation with
    | nil => rfl
    | stop evaluated => simp [collectPositionals, evaluated]
    | next evaluated _ tail => simp [collectPositionals, evaluated, tail]

variable {layout : Layout} {parameters : VariadicParameters layout} {supplied completed : List Value}

theorem complete_iff :
    parameters.complete supplied = .ok completed ↔
      parameters.fixed.slots.length ≤ supplied.length ∧
      ∃ items : List Silmaril.Languages.Python.Core.Module.Value,
        (supplied.drop parameters.fixed.slots.length).mapM Value.scalar? = some items ∧
        completed = supplied.take parameters.fixed.slots.length ++ [.tuple (items.map .scalar)] := by
  simp only [VariadicParameters.complete]
  split
  · rename_i short
    simp [Nat.not_le.mpr short]
  · rename_i enough
    cases (supplied.drop parameters.fixed.slots.length).mapM Value.scalar? with
    | none => simp
    | some items => simp [Nat.le_of_not_lt enough, eq_comm]

theorem complete_length (done : parameters.complete supplied = .ok completed) :
    completed.length = parameters.destinations.slots.length := by
  obtain ⟨enough, _, _, rfl⟩ := complete_iff.mp done
  simp [VariadicParameters.destinations, List.length_take, Nat.min_eq_left enough]

theorem bind_iff {before after : Environment layout} :
    parameters.bind supplied before = .ok after ↔
      ∃ completed, parameters.complete supplied = .ok completed ∧
        Writes (parameters.destinations.slots.zip completed) before after := by
  cases checked : parameters.complete supplied with
  | error failure => simp [VariadicParameters.bind, checked, Except.bind]
  | ok values =>
    simp [VariadicParameters.bind, checked, Except.bind, Call.bind_iff, complete_length checked]

theorem bind_fixed {before after : Environment layout} {slot : ParameterSlot layout} {value : Value}
    (bound : parameters.bind supplied before = .ok after)
    (member : (slot, value) ∈ parameters.fixed.slots.zip (supplied.take parameters.fixed.slots.length))
    (unique : Function.Injective before.2.owned) :
    after.2.read after.1 slot.slot = .ok value := by
  obtain ⟨values, completed, writes⟩ := bind_iff.mp bound
  obtain ⟨enough, items, _, rfl⟩ := complete_iff.mp completed
  have length : parameters.fixed.slots.length = (supplied.take parameters.fixed.slots.length).length := by
    simp [List.length_take, Nat.min_eq_left enough]
  apply bind_read (Call.bind_iff.mpr ⟨complete_length completed, writes⟩) unique
  simp only [VariadicParameters.destinations, List.zip_append length, List.mem_append]
  exact Or.inl member

theorem bind_rest {before after : Environment layout} {items : List Silmaril.Languages.Python.Core.Module.Value}
    (bound : parameters.bind supplied before = .ok after)
    (packed : (supplied.drop parameters.fixed.slots.length).mapM Value.scalar? = some items)
    (unique : Function.Injective before.2.owned) :
    after.2.read after.1 parameters.rest.slot = .ok (.tuple (items.map .scalar)) := by
  obtain ⟨values, completed, writes⟩ := bind_iff.mp bound
  obtain ⟨enough, actual, checked, rfl⟩ := complete_iff.mp completed
  have same : actual = items := Option.some.inj (checked.symm.trans packed)
  subst actual
  have length : parameters.fixed.slots.length = (supplied.take parameters.fixed.slots.length).length := by
    simp [List.length_take, Nat.min_eq_left enough]
  have member : (parameters.rest, Value.tuple (items.map .scalar)) ∈ parameters.destinations.slots.zip
      (supplied.take parameters.fixed.slots.length ++ [.tuple (items.map .scalar)]) := by
    simp [VariadicParameters.destinations, List.zip_append length]
  exact bind_read (Call.bind_iff.mpr ⟨complete_length completed, writes⟩) unique member

theorem enter_spec {Continuation : Layout → Type} {fn : Function}
    {parameters : VariadicParameters fn.code.layout} {heap : Heap} {caller : Saved Continuation}
    {stack : List (Saved Continuation)} {callee : Entered Continuation fn.code.layout}
    (entered : parameters.enter fn supplied heap caller stack = .ok callee) :
    ∃ values, parameters.complete supplied = .ok values ∧
      Call.enter fn parameters.destinations values heap caller stack = .ok callee := by
  cases valid : firstDangling fn heap with
  | some cell => simp [VariadicParameters.enter, valid] at entered
  | none =>
    cases completed : parameters.complete supplied with
    | error failure => simp [VariadicParameters.enter, valid, completed, Except.bind] at entered
    | ok values =>
      exact ⟨values, rfl, by
        simpa [VariadicParameters.enter, valid, completed, Except.bind] using entered⟩

end Silmaril.Proofs.Languages.Python.Core.Closure.Call.Variadic

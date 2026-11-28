module

public import Silmaril.Logic.Temporal.TLA.DataElab.Sequences.Defs
public import Silmaril.Logic.Temporal.TLA.DataElab.Tagged.Thms
import all Silmaril.Logic.Temporal.TLA.DataElab.Sequences.Defs

public section

namespace Silmaril.Logic.Temporal.TLA.DataElab.Sequences

open Resolution Data.Tagged
open DataElab.Tagged (Policy)

universe u

variable (policy : Policy.{u}) (invalid : SequencePolicy.{u})

theorem external_apply {id : BindingId} {op : Operator} {arity : Nat}
    (found : operatorAt id = some op) (admitted : signature id = some arity) (args : List Value.{u}) :
    (external policy invalid id arity admitted).apply args = (primitive policy invalid op).apply args := by
  revert admitted
  unfold signature external
  rw [found]
  exact fun admitted => by cases Option.some.inj admitted; rfl

@[simp] theorem numeric_apply (op : Tagged.NumericPrimitive) (args : List Value.{u}) :
    (primitive policy invalid (.inl op)).apply args = (policy.primitive op).apply args := by rfl

@[simp] theorem seq_apply (s : Value.{u}) :
    (primitive policy invalid (.inr .seq)).apply [s] = s.seq invalid := by rfl

@[simp] theorem len_apply (s : Value.{u}) :
    (primitive policy invalid (.inr .len)).apply [s] = s.len invalid := by rfl

@[simp] theorem append_apply (s e : Value.{u}) :
    (primitive policy invalid (.inr .append)).apply [s, e] = s.append invalid e := by rfl

@[simp] theorem head_apply (s : Value.{u}) :
    (primitive policy invalid (.inr .head)).apply [s] = s.head invalid := by rfl

@[simp] theorem tail_apply (s : Value.{u}) :
    (primitive policy invalid (.inr .tail)).apply [s] = s.tail invalid := by rfl

end Silmaril.Logic.Temporal.TLA.DataElab.Sequences

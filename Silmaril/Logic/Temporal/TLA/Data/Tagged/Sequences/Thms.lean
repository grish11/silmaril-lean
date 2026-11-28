module

public import Silmaril.Logic.Temporal.TLA.Data.Tagged.Sequences.Defs
public import Silmaril.Logic.Temporal.TLA.Data.Tagged.Collections.Thms
import Silmaril.Proofs.Logic.Temporal.TLA.Data.Tagged.Sequences

public section

namespace Silmaril.Logic.Temporal.TLA.Data.Tagged

universe u

theorem Graph.tuple_of_domain {g : Graph.{u}} {n : Nat} (hd : g.domain = SetData.intRange 1 n) :
    ∃ xs : List Value.{u}, xs.length = n ∧ Graph.tuple xs = g :=
  SequenceProofs.tuple_of_domain hd

theorem SetData.mem_sequences {s : SetData.{u}} {v : Value.{u}} :
    s.sequences.mem v ↔ ∃ n : Nat, ((SetData.intRange 1 n).functionSet s).mem v :=
  SequenceProofs.mem_sequences

theorem SetData.mem_sequences_iff_tuple {s : SetData.{u}} {v : Value.{u}} :
    s.sequences.mem v ↔ ∃ xs : List Value.{u}, Value.tuple xs = v ∧ ∀ x ∈ xs, s.mem x :=
  SequenceProofs.mem_sequences_iff_tuple

namespace Value

theorem tuple_injective : Function.Injective tuple.{u} :=
  function_injective.comp Graph.tuple_injective

end Value

theorem SetData.tuple_mem_sequences {s : SetData.{u}} {xs : List Value.{u}} :
    s.sequences.mem (Value.tuple xs) ↔ ∀ x ∈ xs, s.mem x := by
  simp [SetData.mem_sequences_iff_tuple, Value.tuple_injective.eq_iff]

namespace Value

theorem asSequence_eq_some {s : Value.{u}} {xs : List Value.{u}} :
    s.asSequence = some xs ↔ tuple xs = s :=
  decode_eq_some tuple_injective

theorem asSequence_eq_none {s : Value.{u}} :
    s.asSequence = none ↔ ¬ ∃ g : Graph.{u}, function g = s ∧
      ∃ n : Nat, g.domain = SetData.intRange 1 n :=
  SequenceProofs.asSequence_eq_none

@[simp] theorem asSequence_tuple (xs : List Value.{u}) : (tuple xs).asSequence = some xs :=
  asSequence_eq_some.mpr rfl

variable (invalid : SequencePolicy.{u}) {s e x : Value.{u}}

@[simp] theorem seq_set (s : SetData.{u}) : seq invalid (set s) = set s.sequences := by
  simp [seq]

theorem seq_nonset (h : s.asSet = none) : seq invalid s = invalid .seq [s] := by
  simp [seq, h]

@[simp] theorem len_tuple (xs : List Value.{u}) : len invalid (tuple xs) = integer xs.length := by
  simp [len]

theorem len_nonsequence (h : s.asSequence = none) : len invalid s = invalid .len [s] := by
  simp [len, h]

@[simp] theorem append_tuple (xs : List Value.{u}) (e : Value.{u}) :
    append invalid (tuple xs) e = tuple (xs ++ [e]) := by
  simp [append]

theorem append_nonsequence (h : s.asSequence = none) : append invalid s e = invalid .append [s, e] := by
  simp [append, h]

theorem head_function {g : Graph.{u}} (h : g.relates (.integer 1) x) :
    head invalid (function g) = x :=
  apply_function _ h

theorem head_missing {g : Graph.{u}} (h : ¬ g.domain.mem (.integer 1)) :
    head invalid (function g) = invalid .head [function g] :=
  apply_missing _ h

theorem head_nonfunction (h : s.asFunction = none) : head invalid s = invalid .head [s] :=
  apply_nonfunction _ h

@[simp] theorem head_cons (x : Value.{u}) (xs : List Value.{u}) :
    head invalid (tuple (x :: xs)) = x :=
  head_function invalid (Graph.lookup_eq_some.mp (Graph.lookup_tuple (x :: xs) (i := 0) (by simp)))

@[simp] theorem head_empty : head invalid (tuple []) = invalid .head [tuple []] :=
  head_missing invalid (by simp [SetData.mem_intRange, integer_injective.eq_iff])

@[simp] theorem tail_cons (x : Value.{u}) (xs : List Value.{u}) :
    tail invalid (tuple (x :: xs)) = tuple xs := by
  simp [tail]

@[simp] theorem tail_empty : tail invalid (tuple []) = invalid .tail [tuple []] := by
  simp [tail]

theorem tail_nonsequence (h : s.asSequence = none) : tail invalid s = invalid .tail [s] := by
  simp [tail, h]

end Value
end Silmaril.Logic.Temporal.TLA.Data.Tagged

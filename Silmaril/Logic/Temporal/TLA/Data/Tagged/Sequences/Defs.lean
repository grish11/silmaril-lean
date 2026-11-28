module

public import Silmaril.Logic.Temporal.TLA.Data.Tagged.Collections.Defs

/-! # Standard TLA+ finite sequences on tagged graphs -/

@[expose] public section

namespace Silmaril.Logic.Temporal.TLA.Data.Tagged

universe u

/-- The reference `UNION {[1..n -> S] : n \in Nat}`, with no length bound. -/
noncomputable def SetData.sequences (s : SetData.{u}) : SetData.{u} :=
  ⟨(ZFSet.range fun n : Nat => ((intRange 1 n).functionSet s).codes).sUnion⟩

/-- Recognize exactly graphs with domain `1..n` for some natural `n`.
The tuple map represents those graphs by their ordered outputs. -/
noncomputable def Value.asSequence (s : Value.{u}) : Option (List Value.{u}) :=
  decode Value.tuple s

inductive SequenceOp where
  | seq | len | append | head | tail
  deriving DecidableEq, Repr

def SequenceOp.arity : SequenceOp → Nat
  | .append => 2
  | _ => 1

/-- Fix one unspecified-value policy across valuations, preserving operand order. -/
abbrev SequencePolicy := SequenceOp → List Value.{u} → Value.{u}

noncomputable def Value.seq (invalid : SequencePolicy.{u}) (s : Value.{u}) : Value.{u} :=
  match s.asSet with
  | some set => .set set.sequences
  | none => invalid .seq [s]

noncomputable def Value.len (invalid : SequencePolicy.{u}) (s : Value.{u}) : Value.{u} :=
  match s.asSequence with
  | some xs => .integer xs.length
  | none => invalid .len [s]

noncomputable def Value.append (invalid : SequencePolicy.{u}) (s e : Value.{u}) : Value.{u} :=
  match s.asSequence with
  | some xs => .tuple (xs ++ [e])
  | none => invalid .append [s, e]

/-- The standard body is `s[1]`. Any recognized graph with that key supplies
the result. A missing key or non-function uses the fixed Head policy. -/
noncomputable def Value.head (invalid : SequencePolicy.{u}) (s : Value.{u}) : Value.{u} :=
  apply (fun _ _ => invalid .head [s]) s (.integer 1)

noncomputable def Value.tail (invalid : SequencePolicy.{u}) (s : Value.{u}) : Value.{u} :=
  match s.asSequence with
  | some (_ :: xs) => .tuple xs
  | _ => invalid .tail [s]

end Silmaril.Logic.Temporal.TLA.Data.Tagged

module

public import Silmaril.Logic.Operational.SOS.Thms
public import Silmaril.Wasm.Execution.Runtime

/-!
# Flat scalar local instructions

The shared state retains the numeric locals and flat administrative code.
Native adapters supply the store and module instance and retain them across
the local effects. The type guard checks the declared numeric local types and
the operand stack of the entire flat sequence.

The rules follow the local reduction clauses of Wasm 1.0 and Core 3.0 in the
pinned public manifests. A tee duplicates its top operand and installs a
pending set. The set, when reduced, performs the write.
-/

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Locals

open Silmaril.Logic.Operational Silmaril.Logic.Operational.SOS Silmaril.Semantics.SOS
open Silmaril.Wasm.Execution.Runtime (Value)

inductive Op where
  | value (v : Value)
  | get (i : LocalIdx)
  | set (i : LocalIdx)
  | tee (i : LocalIdx)
  deriving DecidableEq

structure State where
  locals : List Value
  code : List Op

abbrev Judgment := State × State

def values (vs : List Value) : List Op := vs.map .value

/-- The arithmetic-free local rules. The context rule threads the result locals. -/
inductive RuleInstance : Rule Judgment → Prop where
  | get (ls : List Value) (i : LocalIdx) (v : Value) (found : ls[i.toNat]? = some v) :
      RuleInstance ⟨[], (⟨ls, [.get i]⟩, ⟨ls, [.value v]⟩)⟩
  | set (ls : List Value) (i : LocalIdx) (v : Value) (bound : i.toNat < ls.length) :
      RuleInstance ⟨[], (⟨ls, [.value v, .set i]⟩, ⟨ls.set i.toNat v, []⟩)⟩
  | tee (ls : List Value) (i : LocalIdx) (v : Value) :
      RuleInstance ⟨[], (⟨ls, [.value v, .tee i]⟩, ⟨ls, [.value v, .value v, .set i]⟩)⟩
  | context (a b : State) (saved : List Value) (tail : List Op) :
      RuleInstance ⟨[(a, b)], (⟨a.locals, values saved ++ a.code ++ tail⟩,
        ⟨b.locals, values saved ++ b.code ++ tail⟩)⟩

def shape : SOS.Shape.{0} := ⟨⟨State, Unit⟩, Judgment, fun (s, _, t) => (s, t)⟩

def presentation : SOS.Presentation := ⟨shape, {r | RuleInstance r}⟩

abbrev Edge (a b : State) := presentation.Derives (a, b)
abbrev Runs := Relation.ReflTransGen Edge

/-- A top-first operand stack. The checker threads types only. -/
def check (types : List NumType) (stack : List NumType) : List Op → Option (List NumType)
  | [] => some stack
  | .value v :: tail => check types (v.type :: stack) tail
  | .get i :: tail => do
      let t ← types[i.toNat]?
      check types (t :: stack) tail
  | .set i :: tail =>
      match stack with
      | [] => none
      | t :: above =>
          if types[i.toNat]? = some t then check types above tail else none
  | .tee i :: tail =>
      match stack with
      | [] => none
      | t :: _ =>
          if types[i.toNat]? = some t then check types stack tail else none

def Admitted (types result : List NumType) (a : State) : Prop :=
  a.locals.map Value.type = types ∧ check types [] a.code = some result

/-- Flat code lowers constructor by constructor to each native administrative
syntax. Readback is partial on native instructions outside this slice. -/
structure Codec (A : Type) where
  emit : Op → A
  read : A → Option Op
  read_emit : ∀ op, read (emit op) = some op
  emit_read : ∀ {a op}, read a = some op → emit op = a

namespace Codec

variable {A : Type} (C : Codec A)

def encode (code : List Op) : List A := code.map C.emit

def decode (code : List A) : List Op := code.filterMap C.read

def Supported (code : List A) : Prop := ∀ a ∈ code, (C.read a).isSome

end Codec
end Silmaril.Wasm.Institution.Operational.Locals

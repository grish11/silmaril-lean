module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Defs

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape

open Functions
open Lists (State Outcome)

local notation "Expr" => Lowering.Resolve.SourceExpr
local notation "Value" => Lists.Value

/-- Defaults in the bounded wrapper can read its parameter, index that
value once, or use a literal. A singleton list exercises allocation. -/
inductive Operand where
  | parameter
  | index (offset : Int)
  | integer (value : Int)
  | list (value : Int)

@[expose] def Operand.source (operand : Operand) (parameter : String) : Expr :=
  match operand with
  | .parameter => .scalar (.read parameter)
  | .index offset => .index (.scalar (.read parameter)) (.scalar (.int offset))
  | .integer value => .scalar (.int value)
  | .list value => .list [.scalar (.int value)]

@[expose] def Operand.code (operand : Operand) (parameter : String) : Lowering.Expr :=
  match operand with
  | .parameter => Leaf.readOperand (fileSlot parameter)
  | .index offset => .index (Leaf.readOperand (fileSlot parameter)) (.atom (.scalar (.int offset)))
  | .integer value => .atom (.scalar (.int value))
  | .list value => .list [.atom (.scalar (.int value))]

@[expose] def Operand.reads (operand : Operand) (parameter : String) : List Binding :=
  match operand with
  | .parameter | .index _ => [fileSlot parameter]
  | .integer _ | .list _ => []

/-- A wrapper with one required parameter defines the child, rebinds the
parameter to a scalar, and returns the child. -/
structure Spec where
  name : String
  parameter : String
  childName : String
  required : List String
  defaults : List (String × Operand)
  returned : String
  rebound : Int

@[expose] def Spec.child (wrapper : Spec) : Defaults.Definition :=
  ⟨wrapper.childName,
    ⟨wrapper.required, wrapper.defaults.map fun (name, operand) => (name, operand.source wrapper.parameter)⟩,
    wrapper.returned⟩

@[expose] def Spec.codes (wrapper : Spec) : List Lowering.Expr :=
  wrapper.defaults.map fun (_, operand) => operand.code wrapper.parameter

@[expose] def Spec.childBody (wrapper : Spec) : Statement :=
  .ret (some (.scalar (.read wrapper.returned)))

@[expose] def Spec.bodyWith (wrapper : Spec) (childBody : Statement) : Statement :=
  .seq (.define wrapper.childName wrapper.child.parameters.source childBody)
    (.seq (.assign wrapper.parameter (.scalar (.int wrapper.rebound)))
      (.ret (some (.scalar (.read wrapper.childName)))))

@[expose] def Spec.body (wrapper : Spec) : Statement := wrapper.bodyWith wrapper.childBody

@[expose] def Spec.commandWith (wrapper : Spec) (childBody : Statement) : Command :=
  .define wrapper.name (.required [wrapper.parameter]) (wrapper.bodyWith childBody)

@[expose] def Spec.command (wrapper : Spec) : Command := wrapper.commandWith wrapper.childBody

@[expose] def Spec.frame (wrapper : Spec) (childId : Nat) : Forwarding.Frame :=
  ⟨[wrapper.parameter], [wrapper.childName], [],
    .seq (.define (fileSlot wrapper.childName) childId)
      (.seq (.assignExpr (fileSlot wrapper.parameter) (.atom (.scalar (.int wrapper.rebound))))
        (.returnExpr (Leaf.readOperand (fileSlot wrapper.childName))))⟩

structure WrapperNames (wrapper : Spec) : Prop where
  distinct : wrapper.parameter ≠ wrapper.childName
  parameterLegal : wrapper.parameter.toList.head? ≠ some '$'
  childLegal : wrapper.childName.toList.head? ≠ some '$'

structure Admitted (wrapper : Spec) : Prop where
  distinct : wrapper.parameter ≠ wrapper.childName
  parameterLegal : wrapper.parameter.toList.head? ≠ some '$'
  childLegal : wrapper.childName.toList.head? ≠ some '$'
  returned : Visible wrapper.child.parameters.names wrapper.returned

theorem Admitted.wrapperNames {wrapper : Spec} (admitted : Admitted wrapper) : WrapperNames wrapper :=
  ⟨admitted.distinct, admitted.parameterLegal, admitted.childLegal⟩

@[expose] def Spec.saved (wrapper : Spec) (values : List Value) : List (Binding × Value) :=
  (wrapper.child.parameters.optional.map (fileSlot ∘ Prod.fst)).zip values

/-- Definition-time operands use the wrapper's reached frame and address
space. Allocating a list in one default extends that frame's heap. -/
inductive Evaluates (parameter : String) (state : State) : Operand → Outcome Value → Prop where
  | parameter : Evaluates parameter state .parameter (state.read (.bound (fileSlot parameter)))
  | index (offset : Int) : Evaluates parameter state (.index offset)
      ((state.read (.bound (fileSlot parameter))).resume fun receiver =>
        Lists.readIndex receiver (.scalar (.int offset)))
  | integer (value : Int) : Evaluates parameter state (.integer value) (.ok (.scalar (.int value)) state)
  | list (value : Int) : Evaluates parameter state (.list value) (Lists.allocate [.scalar (.int value)] state)

/-- The ordered source spine stops at the first error. -/
inductive DefaultsIn (parameter : String) : State → List Operand → Outcome (List Value) → Prop where
  | nil {state : State} : DefaultsIn parameter state [] (.ok [] state)
  | next {state middle : State} {first : Operand} {tail : List Operand} {value : Value} {out : Outcome (List Value)} :
      Evaluates parameter state first (.ok value middle) → DefaultsIn parameter middle tail out →
      DefaultsIn parameter state (first :: tail) (out.resume fun values final => .ok (value :: values) final)
  | failed {state final : State} {first : Operand} {tail : List Operand} {error : Lists.Error} :
      Evaluates parameter state first (.error error final) →
      DefaultsIn parameter state (first :: tail) (.error error final)

/-- The shared wrapper rules install captures in the reached defining
frame. A failed default cannot reach installation or the rebinding. -/
inductive ReturnsWith (wrapper : Spec) (childId : Nat) (free : List FreeName)
    (caller : State) (argument : Value) : Outcome Value → Prop where
  | failed {error : Lists.Error} {final : State} :
      DefaultsIn wrapper.parameter
        (activate caller (wrapper.frame childId).declaration [] [(fileSlot wrapper.parameter, argument)])
        (wrapper.defaults.map Prod.snd) (.error error final) →
      ReturnsWith wrapper childId free caller argument (.error error (restoreCaller caller final))
  | child {values : List Value} {final : State} {captures : List Lists.Capture} :
      DefaultsIn wrapper.parameter
        (activate caller (wrapper.frame childId).declaration [] [(fileSlot wrapper.parameter, argument)])
        (wrapper.defaults.map Prod.snd) (.ok values final) →
      Installs final free captures →
      ReturnsWith wrapper childId free caller argument (.ok (.function final.heap.size)
        (restoreCaller caller ((Defaults.install (fileSlot wrapper.childName) childId captures (wrapper.saved values) final).write
          (fileSlot wrapper.parameter) (.scalar (.int wrapper.rebound)))))

/-- Success installs the saved values before rebinding the wrapper's
parameter. Failure restores the caller immediately with the heap from
the last reached default. -/
inductive Returns (wrapper : Spec) (childId : Nat) (caller : State) (argument : Value) :
    Outcome Value → Prop where
  | failed {error : Lists.Error} {final : State} :
      DefaultsIn wrapper.parameter
        (activate caller (wrapper.frame childId).declaration [] [(fileSlot wrapper.parameter, argument)])
        (wrapper.defaults.map Prod.snd) (.error error final) →
      Returns wrapper childId caller argument (.error error (restoreCaller caller final))
  | child {values : List Value} {final : State} :
      DefaultsIn wrapper.parameter
        (activate caller (wrapper.frame childId).declaration [] [(fileSlot wrapper.parameter, argument)])
        (wrapper.defaults.map Prod.snd) (.ok values final) →
      Returns wrapper childId caller argument (.ok (.function final.heap.size)
        (restoreCaller caller ((Defaults.install (fileSlot wrapper.childName) childId [] (wrapper.saved values) final).write
          (fileSlot wrapper.parameter) (.scalar (.int wrapper.rebound)))))

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape

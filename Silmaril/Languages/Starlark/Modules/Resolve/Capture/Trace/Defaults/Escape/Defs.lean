module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Defs

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape

open Functions
open Lists (State Outcome)

local notation "Expr" => Lowering.Resolve.SourceExpr
local notation "Value" => Lists.Value

/-- Defaults in the bounded wrapper can read an enclosing binding,
index the first parameter once, or use a literal. -/
inductive Operand where
  | parameter
  | read (name : String)
  | index (offset : Int)
  | integer (value : Int)
  | list (value : Int)

@[expose] def Operand.source (operand : Operand) (parameter : String) : Expr :=
  match operand with
  | .parameter => .scalar (.read parameter)
  | .read name => .scalar (.read name)
  | .index offset => .index (.scalar (.read parameter)) (.scalar (.int offset))
  | .integer value => .scalar (.int value)
  | .list value => .list [.scalar (.int value)]

@[expose] def Operand.code (operand : Operand) (parameter : String) : Lowering.Expr :=
  match operand with
  | .parameter => Leaf.readOperand (fileSlot parameter)
  | .read name => Leaf.readOperand (fileSlot name)
  | .index offset => .index (Leaf.readOperand (fileSlot parameter)) (.atom (.scalar (.int offset)))
  | .integer value => .atom (.scalar (.int value))
  | .list value => .list [.atom (.scalar (.int value))]

@[expose] def Operand.reads (operand : Operand) (parameter : String) : List Binding :=
  match operand with
  | .parameter | .index _ => [fileSlot parameter]
  | .read name => [fileSlot name]
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

@[expose] def Spec.occurrences (wrapper : Spec) (updates : List (String × Int))
    (leading : List String) : List String :=
  leading ++ wrapper.childName :: wrapper.parameter :: updates.map Prod.fst

/-- The entire wrapper block determines allocation order, including the
trailing binders that are still unbound when defaults run. -/
@[expose] def Spec.locals (wrapper : Spec) (updates : List (String × Int))
    (additional : List String := []) (leading : List String := []) : List String :=
  (wrapper.occurrences updates leading).eraseDups.filter (!(wrapper.parameter :: additional).contains ·)

theorem Spec.local_member (wrapper : Spec) (updates : List (String × Int)) (additional leading : List String)
    (name : String) (occurs : name ∈ wrapper.occurrences updates leading)
    (outside : name ∉ wrapper.parameter :: additional) : name ∈ wrapper.locals updates additional leading :=
  List.mem_filter.mpr ⟨List.mem_eraseDups.mpr occurs, by simpa using outside⟩

@[expose] def Spec.updateSuite (wrapper : Spec) (updates : List (String × Int)) : Defaults.Body.Suite :=
  updates.foldr (fun (name, value) tail => .assign name (.scalar (.int value)) tail)
    (.ret (.scalar (.read wrapper.childName)))

@[expose] def Spec.updateCode (wrapper : Spec) (updates : List (String × Int)) : Functions.Body :=
  updates.foldr (fun (name, value) tail => .seq (.assignExpr (fileSlot name) (.atom (.scalar (.int value)))) tail)
    (.returnExpr (Leaf.readOperand (fileSlot wrapper.childName)))

@[expose] def applyUpdates (updates : List (String × Int)) (state : State) : State :=
  updates.foldl (fun next (name, value) => next.write (fileSlot name) (.scalar (.int value))) state

@[expose] def Spec.bodyWith (wrapper : Spec) (childBody : Statement)
    (updates : List (String × Int) := []) : Statement :=
  .seq (.define wrapper.childName wrapper.child.parameters.source childBody)
    (.seq (.assign wrapper.parameter (.scalar (.int wrapper.rebound))) (wrapper.updateSuite updates).source)

@[expose] def Spec.body (wrapper : Spec) : Statement := wrapper.bodyWith wrapper.childBody

@[expose] def Spec.commandWith (wrapper : Spec) (childBody : Statement)
    (additional : List String := []) (updates : List (String × Int) := [])
    (leading : List (String × Expr) := []) : Command :=
  .define wrapper.name (.required (wrapper.parameter :: additional))
    (Defaults.Body.prependSource leading (wrapper.bodyWith childBody updates))

@[expose] def Spec.command (wrapper : Spec) : Command := wrapper.commandWith wrapper.childBody

@[expose] def Spec.frame (wrapper : Spec) (childId : Nat) (additional : List String := [])
    (updates : List (String × Int) := []) (leading : List String := []) : Forwarding.Frame :=
  ⟨wrapper.parameter :: additional, wrapper.locals updates additional leading, [],
    .seq (.define (fileSlot wrapper.childName) childId)
      (.seq (.assignExpr (fileSlot wrapper.parameter) (.atom (.scalar (.int wrapper.rebound))))
        (wrapper.updateCode updates))⟩

/-- An explicitly named default read must refer to the wrapper's own
lexical block. The usual parameter operands use the first parameter. -/
@[expose] def Spec.DefaultReads (wrapper : Spec) (owned : List String) : Prop :=
  ∀ name, (∃ target, (target, .read name) ∈ wrapper.defaults) →
    name ∈ owned ∧ name.toList.head? ≠ some '$'

structure WrapperNames (wrapper : Spec) : Prop where
  distinct : wrapper.parameter ≠ wrapper.childName
  parameterLegal : wrapper.parameter.toList.head? ≠ some '$'
  childLegal : wrapper.childName.toList.head? ≠ some '$'

structure Admitted (wrapper : Spec) : Prop where
  distinct : wrapper.parameter ≠ wrapper.childName
  parameterLegal : wrapper.parameter.toList.head? ≠ some '$'
  childLegal : wrapper.childName.toList.head? ≠ some '$'
  returned : Visible wrapper.child.parameters.names wrapper.returned
  defaultReads : wrapper.DefaultReads [wrapper.parameter]

theorem Admitted.wrapperNames {wrapper : Spec} (admitted : Admitted wrapper) : WrapperNames wrapper :=
  ⟨admitted.distinct, admitted.parameterLegal, admitted.childLegal⟩

@[expose] def Spec.saved (wrapper : Spec) (values : List Value) : List (Binding × Value) :=
  (wrapper.child.parameters.optional.map (fileSlot ∘ Prod.fst)).zip values

/-- Definition-time operands use the wrapper's reached frame and address
space. Allocating a list in one default extends that frame's heap. -/
inductive Evaluates (parameter : String) (state : State) : Operand → Outcome Value → Prop where
  | parameter : Evaluates parameter state .parameter (state.read (.bound (fileSlot parameter)))
  | read (name : String) : Evaluates parameter state (.read name) (state.read (.bound (fileSlot name)))
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
    (updates : List (String × Int)) (caller active : State) : Outcome Value → Prop where
  | failed {error : Lists.Error} {final : State} :
      DefaultsIn wrapper.parameter active
        (wrapper.defaults.map Prod.snd) (.error error final) →
      ReturnsWith wrapper childId free updates caller active (.error error (restoreCaller caller final))
  | child {values : List Value} {final : State} {captures : List Lists.Capture} :
      DefaultsIn wrapper.parameter active
        (wrapper.defaults.map Prod.snd) (.ok values final) →
      Installs final free captures →
      ReturnsWith wrapper childId free updates caller active (.ok (.function final.heap.size)
        (restoreCaller caller (applyUpdates updates
          ((Defaults.install (fileSlot wrapper.childName) childId captures (wrapper.saved values) final).write
            (fileSlot wrapper.parameter) (.scalar (.int wrapper.rebound))))))

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

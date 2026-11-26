module

public import Silmaril.Languages.Starlark.Lists.Defs
public import Silmaril.Languages.Starlark.Lists.Comparison.Operational.Defs

public section

namespace Silmaril.Languages.Starlark.Lists

/-- Big-step rules for resolved list operations. Each operand premise starts in
the state left by the preceding premise. A failed premise retains its state. -/
inductive Eval : {α : Type} → State → Code α → Outcome α → Prop where
  | scalar {s : State} {value : Starlark.Value} :
      Eval s (.scalar value) (.ok (.scalar value) s)
  | builtin {s : State} {id : Builtin} : Eval s (.builtin id) (.ok (.builtin id) s)
  | string {s : State} {text : String} : Eval s (.string text) (.ok (.string text) s)
  | read {s : State} {ref : Ref} : Eval s (.read ref) (s.read ref)
  | list {s : State} {elements : Code (List Value)} {out : Outcome (List Value)} :
      Eval s elements out → Eval s (.list elements) (Outcome.resume out allocate)
  | tuple {s : State} {elements : Code (List Value)} {out : Outcome (List Value)} :
      Eval s elements out → Eval s (.tuple elements) (Outcome.resume out allocateTuple)
  | dict {s : State} {entries : Code (List Entry)} {out : Outcome (List Entry)} :
      Eval s entries out → Eval s (.dict entries) (Outcome.resume out allocateDict)
  | noEntries {s : State} : Eval s .noEntries (.ok [] s)
  | entry {s t u : State} {earlier : Code (List Entry)} {key value : Expr}
      {entries : List Entry} {k : Value} {out : Outcome Value} :
      Eval s earlier (.ok entries t) → Eval t key (.ok k u) → Eval u value out →
      Eval s (.entry earlier key value) (Outcome.resume out (addDisplayEntry entries k))
  | entryPrefixError {s t : State} {earlier : Code (List Entry)} {key value : Expr} {error : Error} :
      Eval s earlier (.error error t) → Eval s (.entry earlier key value) (.error error t)
  | entryKeyError {s t u : State} {earlier : Code (List Entry)} {key value : Expr}
      {entries : List Entry} {error : Error} :
      Eval s earlier (.ok entries t) → Eval t key (.error error u) →
      Eval s (.entry earlier key value) (.error error u)
  | empty {s : State} : Eval s .empty (.ok [] s)
  | cons {s t : State} {head : Expr} {tail : Code (List Value)} {value : Value}
      {out : Outcome (List Value)} :
      Eval s head (.ok value t) → Eval t tail out →
      Eval s (.cons head tail) (Outcome.resume out fun rest => pure (value :: rest))
  | consError {s t : State} {head : Expr} {tail : Code (List Value)} {error : Error} :
      Eval s head (.error error t) → Eval s (.cons head tail) (.error error t)
  | index {s t : State} {receiver index : Expr} {value : Value} {out : Outcome Value} :
      Eval s receiver (.ok value t) → Eval t index out →
      Eval s (.index receiver index) (Outcome.resume out (readIndex value))
  | indexReceiverError {s t : State} {receiver index : Expr} {error : Error} :
      Eval s receiver (.error error t) → Eval s (.index receiver index) (.error error t)
  | slice {s : State} {operands : Code (List Value)} {out : Outcome (List Value)} :
      Eval s operands out → Eval s (.slice operands) (Outcome.resume out readSliceOperands)
  | compare {s t u : State} {op : ComparisonOp} {left right : Expr} {a b : Value}
      {out : Except Error Bool} :
      Eval s left (.ok a t) → Eval t right (.ok b u) → Comparison.Tests u.heap a b op out →
      Eval s (.compare op left right) (Comparison.finish out u)
  | compareLeftError {s t : State} {op : ComparisonOp} {left right : Expr} {error : Error} :
      Eval s left (.error error t) → Eval s (.compare op left right) (.error error t)
  | compareRightError {s t u : State} {op : ComparisonOp} {left right : Expr} {a : Value} {error : Error} :
      Eval s left (.ok a t) → Eval t right (.error error u) → Eval s (.compare op left right) (.error error u)
  | append {s t : State} {receiver argument : Expr} {address : Address} {out : Outcome Value} :
      Eval s receiver (.ok (.list address) t) → Eval t argument out →
      Eval s (.append receiver argument) (Outcome.resume out (appendAt address))
  | appendTargetError {s t : State} {receiver argument : Expr} {value : Value} :
      Eval s receiver (.ok value t) → (∀ address : Address, value ≠ .list address) →
      Eval s (.append receiver argument) (.error .appendTarget t)
  | appendReceiverError {s t : State} {receiver argument : Expr} {error : Error} :
      Eval s receiver (.error error t) → Eval s (.append receiver argument) (.error error t)
  | pass {s : State} : Eval s .pass (.ok () s)
  | eval {s : State} {expr : Expr} {out : Outcome Value} :
      Eval s expr out → Eval s (.eval expr) (Outcome.resume out fun _ => pure ())
  | assign {s : State} {binding : Binding} {rhs : Expr} {out : Outcome Value} :
      Eval s rhs out → Eval s (.assign binding rhs) (Outcome.resume out (bindValue binding))
  | setIndex {s t u : State} {receiver index rhs : Expr} {value target : Value} {out : Outcome Value} :
      Eval s rhs (.ok value t) → Eval t receiver (.ok target u) → Eval u index out →
      Eval s (.setIndex receiver index rhs) (Outcome.resume out fun i => writeIndex target i value)
  | setIndexReceiverError {s t u : State} {receiver index rhs : Expr} {value : Value}
      {error : Error} :
      Eval s rhs (.ok value t) → Eval t receiver (.error error u) →
      Eval s (.setIndex receiver index rhs) (.error error u)
  | setIndexRhsError {s t : State} {receiver index rhs : Expr} {error : Error} :
      Eval s rhs (.error error t) → Eval s (.setIndex receiver index rhs) (.error error t)
  | seq {s t : State} {first rest : Stmt} {out : Outcome Unit} :
      Eval s first (.ok () t) → Eval t rest out → Eval s (.seq first rest) out
  | seqError {s t : State} {first rest : Stmt} {error : Error} :
      Eval s first (.error error t) → Eval s (.seq first rest) (.error error t)

end Silmaril.Languages.Starlark.Lists

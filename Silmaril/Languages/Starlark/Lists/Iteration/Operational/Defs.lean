module

public import Silmaril.Languages.Starlark.Lists.Iteration.Defs
public import Silmaril.Languages.Starlark.Lists.Operational.Defs

public section

namespace Silmaril.Languages.Starlark.Lists.Iteration

/-- The two mutually recursive big-step judgments have a common index so they
can be used with one induction principle. -/
inductive Work where
  | suite {depth : Nat} (code : Suite depth)
  | items {depth : Nat} (target : Binding) (body : Suite depth) (remaining : List Value)

/-- A loop owns one iterator entry from acquisition through every body exit.
The enclosing loop, if any, receives the same iterator stack it had before. -/
inductive Runs : State → Work → Outcome Flow → Prop where
  | atomic {depth : Nat} {s : State} {stmt : Stmt} {out : Outcome Unit} :
      Eval s stmt out → Runs s (.suite (.atomic (depth := depth) stmt))
        (Outcome.resume out fun () => pure .next)
  | seq {depth : Nat} {s t : State} {first rest : Suite depth} {out : Outcome Flow} :
      Runs s (.suite first) (.ok .next t) → Runs t (.suite rest) out →
      Runs s (.suite (.seq first rest)) out
  | seqStop {depth : Nat} {s t : State} {first rest : Suite depth} {signal : Flow} :
      Runs s (.suite first) (.ok signal t) → signal ≠ .next →
      Runs s (.suite (.seq first rest)) (.ok signal t)
  | seqError {depth : Nat} {s t : State} {first rest : Suite depth} {error : Error} :
      Runs s (.suite first) (.error error t) →
      Runs s (.suite (.seq first rest)) (.error error t)
  | branch {depth : Nat} {s t : State} {test : Expr} {yes no : Suite depth}
      {value : Outcome Value} {flag : Bool} {out : Outcome Flow} :
      Eval s test value → Outcome.resume value truth = .ok flag t →
      Runs t (.suite (if flag then yes else no)) out →
      Runs s (.suite (.branch test yes no)) out
  | branchError {depth : Nat} {s t : State} {test : Expr} {yes no : Suite depth}
      {value : Outcome Value} {error : Error} :
      Eval s test value → Outcome.resume value truth = .error error t →
      Runs s (.suite (.branch test yes no)) (.error error t)
  | forIn {depth : Nat} {s t : State} {target : Binding} {iterable : Expr}
      {body : Suite (depth + 1)} {value : Outcome Value} {address : Address}
      {elements : List Value} {out : Outcome Flow} :
      Eval s iterable value → Outcome.resume value iterationSource = .ok (address, elements) t →
      Runs (pushIterator t address) (.items target body elements) out →
      Runs s (.suite (.forIn target iterable body)) (restoreIterators t.iterators out)
  | forError {depth : Nat} {s t : State} {target : Binding} {iterable : Expr}
      {body : Suite (depth + 1)} {value : Outcome Value} {error : Error} :
      Eval s iterable value → Outcome.resume value iterationSource = .error error t →
      Runs s (.suite (.forIn target iterable body)) (.error error t)
  | breakLoop {depth : Nat} {s : State} :
      Runs s (.suite (.breakLoop (depth := depth))) (.ok .breakLoop s)
  | continueLoop {depth : Nat} {s : State} :
      Runs s (.suite (.continueLoop (depth := depth))) (.ok .continueLoop s)
  | ret {depth : Nat} {s : State} {value : Expr} {out : Outcome Value} :
      Eval s value out → Runs s (.suite (.ret (depth := depth) value))
        (Outcome.resume out fun result => pure (.returned result))
  | itemsDone {depth : Nat} {s : State} {target : Binding} {body : Suite depth} :
      Runs s (.items target body []) (.ok .next s)
  | itemsAdvance {depth : Nat} {s t : State} {target : Binding} {body : Suite depth}
      {value : Value} {rest : List Value} {signal : Flow} {out : Outcome Flow} :
      Runs (s.write target value) (.suite body) (.ok signal t) →
      (signal = .next ∨ signal = .continueLoop) → Runs t (.items target body rest) out →
      Runs s (.items target body (value :: rest)) out
  | itemsBreak {depth : Nat} {s t : State} {target : Binding} {body : Suite depth}
      {value : Value} {rest : List Value} :
      Runs (s.write target value) (.suite body) (.ok .breakLoop t) →
      Runs s (.items target body (value :: rest)) (.ok .next t)
  | itemsReturn {depth : Nat} {s t : State} {target : Binding} {body : Suite depth}
      {value result : Value} {rest : List Value} :
      Runs (s.write target value) (.suite body) (.ok (.returned result) t) →
      Runs s (.items target body (value :: rest)) (.ok (.returned result) t)
  | itemsError {depth : Nat} {s t : State} {target : Binding} {body : Suite depth}
      {value : Value} {rest : List Value} {error : Error} :
      Runs (s.write target value) (.suite body) (.error error t) →
      Runs s (.items target body (value :: rest)) (.error error t)

end Silmaril.Languages.Starlark.Lists.Iteration

module

public import Silmaril.Languages.Starlark.Lists.Denotation.Defs

@[expose] public section

namespace Silmaril.Languages.Starlark.Lists.Iteration

/-- Resolved function suites. The index counts lexically enclosing loops. -/
inductive Suite : Nat → Type where
  | atomic {depth : Nat} (stmt : Stmt) : Suite depth
  | seq {depth : Nat} (first rest : Suite depth) : Suite depth
  | branch {depth : Nat} (test : Expr) (yes no : Suite depth) : Suite depth
  | forIn {depth : Nat} (target : Binding) (iterable : Expr)
      (body : Suite (depth + 1)) : Suite depth
  | breakLoop {depth : Nat} : Suite (depth + 1)
  | continueLoop {depth : Nat} : Suite (depth + 1)
  | ret {depth : Nat} (value : Expr) : Suite depth

/-- The original list-only constructor spelling remains available to clients. -/
abbrev Suite.forList {depth : Nat} (target : Binding) (iterable : Expr)
    (body : Suite (depth + 1)) : Suite depth :=
  .forIn target iterable body

inductive Flow where
  | next | breakLoop | continueLoop | returned (value : Value)
  deriving DecidableEq, Repr

def finishState {α : Type} : Outcome α → State
  | .ok _ state | .error _ state => state

def restoreIterators {α : Type} (stack : List Address) : Outcome α → Outcome α
  | .ok value state => .ok value { state with iterators := stack }
  | .error error state => .error error { state with iterators := stack }

def pushIterator (state : State) (address : Address) : State :=
  { state with iterators := address :: state.iterators }

def truth : Value → Meaning Bool
  | .scalar value => pure value.truth
  | .function _ | .builtin _ => pure true
  | .string text => pure (!text.isEmpty)
  | .list address => (fun elements => !elements.isEmpty) <$> listElements address
  | .tuple address => (fun elements => !elements.isEmpty) <$> tupleElements address
  | .dict address => (fun entries => !entries.isEmpty) <$> dictEntries address

def iterationSource : Value → Meaning (Address × List Value)
  | .scalar _ | .function _ | .builtin _ | .string _ => throw .notIterable
  | .list address => (fun elements => (address, elements)) <$> listElements address
  | .tuple address => (fun elements => (address, elements)) <$> tupleElements address
  | .dict address => (fun entries => (address, entries.map Entry.key)) <$> dictEntries address

/-- Interpret the finite sequence captured on iterator acquisition.
The body's meaning is available before the recursion over elements begins. -/
def denoteItems (target : Binding) (body : Meaning Flow) : List Value → Meaning Flow
  | [], state => .ok .next state
  | value :: rest, state =>
    match body (state.write target value) with
    | .ok .next next | .ok .continueLoop next => denoteItems target body rest next
    | .ok .breakLoop next => .ok .next next
    | .ok (.returned result) next => .ok (.returned result) next
    | .error error next => .error error next

def denoteSuite {depth : Nat} : Suite depth → Meaning Flow
  | .atomic stmt, state => Outcome.resume (denote stmt state) fun () => pure .next
  | .seq first rest, state =>
    Outcome.resume (denoteSuite first state) fun
      | .next => denoteSuite rest
      | signal => pure signal
  | .branch test yes no, state =>
    Outcome.resume (Outcome.resume (denote test state) truth) fun test =>
      if test then denoteSuite yes else denoteSuite no
  | .forIn target iterable body, state =>
    Outcome.resume (Outcome.resume (denote iterable state) iterationSource) fun (address, elements) next =>
      restoreIterators next.iterators
        (denoteItems target (denoteSuite body) elements (pushIterator next address))
  | .breakLoop, state => .ok .breakLoop state
  | .continueLoop, state => .ok .continueLoop state
  | .ret value, state => Outcome.resume (denote value state) fun result => pure (.returned result)

end Silmaril.Languages.Starlark.Lists.Iteration

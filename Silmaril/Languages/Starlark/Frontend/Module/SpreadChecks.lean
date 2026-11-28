module

public import Silmaril.Languages.Starlark.Frontend.Module.Checks
import all Silmaril.Languages.Starlark.Frontend.Module.Checks

namespace Silmaril.Languages.Starlark.Frontend.Module

private def header := "# 雪\ndef f(a,b):\n  return b\n"
private def fromList := header ++ "xs=[1]\nkw={'b':7}\nout=f(*xs, **kw)"
private def fromTuple := header ++ "xs=(1,)\nkw={'b':8}\nout=f(*xs, **kw)"
private def grouped :=
  "def f(a,b,c,d):\n  return d\nxs=[2]\nkw={'d':9}\nout=f(1, c=3, *xs, **kw)"
private def wrongIterable := header ++ "xs=1\nkw={'b':7}\nout=f(*xs, **kw)"
private def wrongMapping := header ++ "xs=1\nkw=2\nout=f(*xs, **kw)"
private def conflicting := header ++ "xs=[1]\nkw={'b':2}\nout=f(b=3, *xs, **kw)"
private def readBeforeExpansion := header ++ "xs=1\nout=f(*xs, **kw)\nkw={}"

private def nestedPrefix :=
  header ++ "def give(x):\n  return x\ndef missing(y):\n  return y\nxs=[1]\nkw={'b':7}\n"
private def nested := nestedPrefix ++ "out=f(*give(give(xs)), **give(x=kw))"
private def allocated := nestedPrefix ++ "out=f(*list(xs), **kw)"

/-- The same call and spread module texts are checked by Lean and pinned Go. -/
public def spreadControls : List Control := [
  ⟨"named-list-and-dict-spread", fromList, .exportedInt 7⟩,
  ⟨"named-tuple-and-dict-spread", fromTuple, .exportedInt 8⟩,
  ⟨"all-operand-groups", grouped, .exportedInt 9⟩,
  ⟨"named-spread-invalid-iterable", wrongIterable, .invalidStar⟩,
  ⟨"mapping-expansion-before-iterable-expansion", wrongMapping, .invalidStarStar⟩,
  ⟨"named-spread-binding-collision", conflicting, .multipleValues "b"⟩,
  ⟨"spread-read-before-expansion", readBeforeExpansion, .uninitializedGlobal "kw"⟩,
  ⟨"nested-positional-and-mapping-spreads", nested, .exportedInt 7⟩,
  ⟨"nested-builtin-spread", allocated, .exportedInt 7⟩,
  ⟨"conditional-and-logical-spreads",
    nestedPrefix ++ "out=f(*(xs if True else missing), **(False or kw))", .exportedInt 7⟩,
  ⟨"read-callee-before-nested-spread", nestedPrefix ++ "out=later(*give())\nlater=f",
    .uninitializedGlobal "later"⟩,
  ⟨"nested-named-before-spread", nestedPrefix ++ "out=f(b=missing(), *give())", .missingArgument "y"⟩,
  ⟨"nested-star-before-mapping", nestedPrefix ++ "out=f(*give(), **missing())", .missingArgument "x"⟩,
  ⟨"mapping-operand-before-star-expansion", nestedPrefix ++ "out=f(*1, **missing())", .missingArgument "y"⟩,
  ⟨"nested-spread-binding-collision", nestedPrefix ++ "out=f(b=3, *give(xs), **give(kw))", .multipleValues "b"⟩]

#guard spreadControls.all fun control => decide (observe control.source = some control.expected)

-- Inspect the normalized collection assignments and variable reads from the same
-- UTF-8 module that the executable publication control uses.
private def lowersNameSpreads : Bool := Id.run do
  let .ok parsed := parseUtf8 fromList.toUTF8 | return false
  match parsed.commands.map LocatedCommand.command with
  | [_, .assign "xs" (.list [.scalar (.int 1)]),
      .assign "kw" (.dict [(.string "b", .scalar (.int 7))]),
      .assign "out" (.call (.scalar (.read "f")) [] []
        (some (.scalar (.read "xs"))) (some (.scalar (.read "kw"))))] => return true
  | _ => return false

example : lowersNameSpreads = true := by decide +kernel

private def operandSpans : Option (List Span) := do
  let parsed ← (parseUtf8 "# 雪\nout=f(1, c=3, *xs, **kw)".toUTF8).toOption
  let [command] := parsed.commands | none
  return (← command.callSpans).ordered

example : operandSpans = some [⟨⟨12, 2, 7⟩, ⟨13, 2, 8⟩⟩, ⟨⟨15, 2, 10⟩, ⟨18, 2, 13⟩⟩,
    ⟨⟨20, 2, 15⟩, ⟨23, 2, 18⟩⟩, ⟨⟨25, 2, 20⟩, ⟨29, 2, 24⟩⟩] := by decide +kernel

-- The only lists in the final state are the source display and the copy
-- produced by the single evaluation of the inner list(xs) operand.
private def listCount : Option Nat :=
  match runUtf8 allocated.toUTF8 with
  | .ok (.ok _ state) => some (state.heap.toList.countP fun cell =>
    match cell.contents with | .list _ => true | _ => false)
  | _ => none

#guard decide (listCount = some 2)

private def nestedLowering : Option (List (Span × Span × List Span)) := do
  let parsed ← (parseUtf8 "# 雪\nout=f(*give(xs), **provide(kw))".toUTF8).toOption
  let [command] := parsed.commands | none
  match command.command with
  | .assign "out" (.call (.scalar (.read "f")) [] []
      (some (.call (.scalar (.read "give")) [.scalar (.read "xs")] [] none none))
      (some (.call (.scalar (.read "provide")) [.scalar (.read "kw")] [] none none))) =>
    return command.nestedCalls.map fun entry => (entry.span, entry.callee, entry.operands.ordered)
  | _ => none

example : nestedLowering = some [
    (⟨⟨13, 2, 8⟩, ⟨21, 2, 16⟩⟩, ⟨⟨13, 2, 8⟩, ⟨17, 2, 12⟩⟩, [⟨⟨18, 2, 13⟩, ⟨20, 2, 15⟩⟩]),
    (⟨⟨25, 2, 20⟩, ⟨36, 2, 31⟩⟩, ⟨⟨25, 2, 20⟩, ⟨32, 2, 27⟩⟩, [⟨⟨33, 2, 28⟩, ⟨35, 2, 30⟩⟩])] :=
  by decide +kernel

example : frontendDiagnostic "out = f(*xs(,))" =
    some ⟨.expected "an expression", ⟨⟨12, 1, 13⟩, ⟨13, 1, 14⟩⟩⟩ := by decide +kernel

end Silmaril.Languages.Starlark.Frontend.Module

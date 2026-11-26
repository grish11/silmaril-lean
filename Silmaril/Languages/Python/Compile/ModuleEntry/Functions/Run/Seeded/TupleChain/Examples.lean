module

import Batteries.Data.Except
import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Thms
import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.TupleChain.Eval.Thms
meta import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Defs
meta import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Defs
meta import Silmaril.Languages.Python.Core.Module.TupleDispatch.Defs
meta import Silmaril.Languages.Python.Core.Closure.Defs
meta import Silmaril.Languages.Python.Source.Scope.Defs

namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded

open Core.Module.TupleDispatch in
private def dispatchEvidence : Bool := Id.run do
  let (left, first) := Heap.empty.materialize [.bool true]
  let (right, second) := first.materialize [.int 2]
  let (empty, _) := second.materialize []
  let (joined, third) := concat second left right
  return joined == ⟨some 2, [.bool true, .int 2]⟩ &&
    third.objects == #[[.bool true], [.int 2], [.bool true, .int 2]] &&
    concat second empty left == (left, second) &&
    concat second left empty == (left, second) &&
    concat second empty empty == (empty, second) &&
    (BoundMethod.mk .eq left).invoke second (.list [.int 1]) == (.ok .notImplemented, second) &&
    (UnboundMethod.mk .eq).invoke second (.tuple left) (.list [.int 1]) == (.ok .notImplemented, second) &&
    (BoundMethod.mk .add left).invoke second (.list [.int 1]) == (.error .wrongArgument, second) &&
    !(equal left (.list [.int 1])) &&
    callUnbound second (some .stockTuple) .add (.list []) (.tuple [.int 3]) ==
      (.error (.wrongReceiver .add), ⟨#[[.bool true], [.int 2], [.int 3]]⟩) &&
    callUnbound second (some .noneValue) .add (.tuple [.int 3]) (.tuple [.int 4]) ==
      (.error (.missingAttribute .add), second)

#guard dispatchEvidence

private def intTuple (value : Int) : Source.Expr := .tuple [.integer value]

private def chain (middle : Int) : Source.Stmt :=
  let bound := Source.Expr.callWith (.attribute (intTuple 5) "__add__") [(.positional, .tuple [])]
  let unbound := Source.Expr.callWith (.attribute (.name "tuple") "__add__")
    [(.positional, intTuple middle), (.positional, .tuple [])]
  .assert_ (.comparison bound [(.eq, intTuple middle), (.eq, unbound)]) none

private def chainEvidence (space : Core.Module.SeededCall.Namespace) (middle : Int)
    (completion : Except ModuleFailure Unit) (reached : Nat) : Bool := Id.run do
  let source : Source.Module := ⟨[.assign "keep" (.integer 7), chain middle, .assign "tail" (.integer 9)]⟩
  let .ok compiled := Run.compile source | return false
  let [_, .assertTupleChain test, _] := compiled.instructions | return false
  let actual := TupleChain.evaluate (tupleLookup space) test
  let heap : Core.Closure.Heap := ⟨1, fun address => if address = 0 then some (.int 23) else none⟩
  let lists : Core.Module.ListHeap := ⟨#[[.int 31]]⟩
  let outcome := run space compiled heap (lists := lists)
  let preserved := space.bindGlobal "keep" (.int 7)
  let expected := if completion.isOk then preserved.bindGlobal "tail" (.int 9) else preserved
  return actual.reached.length == reached && outcome.completion == completion &&
    outcome.residual.moduleGlobals == expected.moduleGlobals && outcome.residual.builtins == expected.builtins &&
    outcome.lists == lists && outcome.heap.next == 1 && (outcome.heap.contents 0).map seededValue == some (.int 23) &&
    outcome.calls.isEmpty

#guard chainEvidence (legacyTupleSeed .builtin) 5 (.ok ()) 3
#guard chainEvidence .empty 5 (.error (.raised (.runtime (.nameError "tuple")))) 3
#guard chainEvidence .empty 6 (.error (.raised (.assertionError .empty))) 2
#guard chainEvidence ((legacyTupleSeed .builtin).bindGlobal "tuple" .none) 5 (.error .unsupported) 3

private def constructorIdentityEvidence (placement : SeedPlacement) : Bool := Id.run do
  let call name argument := Source.Expr.call (.name name) [argument]
  let test left op right := Source.Expr.comparison (.name left) [(op, .name right)]
  let assertion operand := Source.Stmt.expression (call "___assertTrue" operand)
  let source : Source.Module := ⟨[
    .assign "n" (.integer 7),
    .assign "first" (.tuple [.name "n"]),
    .assign "alias" (call "tuple" (.name "first")),
    .assign "second" (.tuple [.name "n"]),
    assertion (test "first" .is_ "alias"),
    assertion (test "first" .isNot "second")]⟩
  let .ok compiled := Run.compile source | return false
  let space := legacyTupleIdentitySeed placement
  let observed := run space compiled
  let first : Core.Module.SeededCall.Value := .tupleObject ⟨some 0, [.int 7]⟩
  let second : Core.Module.SeededCall.Value := .tupleObject ⟨some 1, [.int 7]⟩
  return observed.completion == .ok () && observed.heap.next == 2 &&
    observed.residual.builtins == space.builtins &&
    observed.residual.lookupGlobal "first" == some first &&
    observed.residual.lookupGlobal "alias" == some first &&
    observed.residual.lookupGlobal "second" == some second &&
    observed.calls.map (fun event => (event.callee, event.observation.result, event.observation.caught)) ==
      [("tuple", .ok first, none), ("___assertTrue", .ok .none, none), ("___assertTrue", .ok .none, none)]

#guard constructorIdentityEvidence .builtin
#guard constructorIdentityEvidence .preamble

private def closedOriginEvidence (placement : SeedPlacement) : Bool := Id.run do
  let call name arguments := Source.Expr.call (.name name) arguments
  let test := Source.Expr.comparison (.name "original") [(.is_, .name "alias")]
  let source : Source.Module := ⟨[
    .expression (call "___assertEqual" [call "tuple" [], .tuple []]),
    .assign "original" (.tuple [.integer 7]),
    .assign "alias" (call "tuple" [.name "original"]),
    .expression (call "___assertTrue" [test])]⟩
  let .ok compiled := Run.compile source | return false
  let space := legacyTupleIdentitySeed placement
  let observed := run space compiled
  let original : Core.Module.SeededCall.Value := .tupleObject ⟨some 0, [.int 7]⟩
  return observed.completion == .ok () && observed.heap.next == 1 &&
    (observed.heap.contents 0).map seededValue == some original &&
    observed.residual.lookupGlobal "original" == some original &&
    observed.residual.lookupGlobal "alias" == some original &&
    observed.calls.map (fun event => (event.callee, event.observation.result, event.observation.caught)) ==
      [("tuple", .ok (.returnedTuple []), none), ("___assertEqual", .ok .none, none),
        ("tuple", .ok original, none), ("___assertTrue", .ok .none, none)]

#guard closedOriginEvidence .builtin
#guard closedOriginEvidence .preamble

private def emptyListTupleEvidence (placement : SeedPlacement) : Bool := Id.run do
  let tupleCall := Source.Expr.call (.name "tuple") [.list_ []]
  let equalCall := Source.Expr.call (.name "___assertEqual") [tupleCall, .tuple []]
  let source : Source.Module := ⟨[.expression equalCall]⟩
  let .ok compiled := Run.compile source | return false
  let stock := legacyTupleSeed placement
  let before : Core.Module.ListHeap := ⟨#[[.int 31]]⟩
  let returned := run stock compiled (lists := before)
  let masked := run (stock.bindGlobal "tuple" .none) compiled (lists := before)
  return returned.completion == .ok () &&
    returned.lists.objects == #[[.int 31], []] && returned.heap.next == 0 &&
    returned.calls.map (fun event => (event.callee, event.observation.result, event.observation.caught)) ==
      [("tuple", .ok (.returnedTuple []), none), ("___assertEqual", .ok .none, none)] &&
    masked.completion == .error (.raised (.runtime .notCallable)) &&
    masked.lists == returned.lists && masked.heap.next == 0 &&
    masked.calls.map (fun event => (event.callee, event.observation.result, event.observation.caught)) ==
      [("tuple", .error (.raised (.runtime .notCallable)), none)]

#guard emptyListTupleEvidence .builtin
#guard emptyListTupleEvidence .preamble

private def freshListTupleEvidence (placement : SeedPlacement) : Bool := Id.run do
  let display : Source.Expr := .list_ [.boolean false, .none_, .integer 7]
  let convert := Source.Expr.call (.name "tuple") [display]
  let distinct := Source.Expr.comparison (.name "first") [(.isNot, .name "second")]
  let source : Source.Module := ⟨[
    .assign "first" convert, .assign "second" convert,
    .expression (.call (.name "___assertTrue") [distinct])]⟩
  let .ok compiled := Run.compile source | return false
  let observed := run (legacyTupleIdentitySeed placement) compiled
  let contents : List Core.Module.Value := [.bool false, .none, .int 7]
  let first : Core.Module.SeededCall.Value := .tupleObject ⟨some 0, contents⟩
  let second : Core.Module.SeededCall.Value := .tupleObject ⟨some 1, contents⟩
  return observed.completion == .ok () && observed.lists.objects == #[contents, contents] &&
    observed.heap.next == 2 && (observed.heap.contents 1).map seededValue == some (.returnedTuple contents) &&
    observed.residual.lookupGlobal "first" == some first &&
    observed.residual.lookupGlobal "second" == some second &&
    observed.calls.map (fun event => (event.callee, event.observation.result, event.observation.caught)) ==
      [("tuple", .ok first, none), ("tuple", .ok second, none), ("___assertTrue", .ok .none, none)]

#guard freshListTupleEvidence .builtin
#guard freshListTupleEvidence .preamble

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded

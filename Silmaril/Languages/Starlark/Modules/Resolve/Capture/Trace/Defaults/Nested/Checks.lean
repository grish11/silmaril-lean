module

import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Thms
import Silmaril.Languages.Starlark.Functions.Lowering.Quote.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Defs

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested

open scoped Functions.Lowering.Quote
open Assignment (LexicalBlock)
open Functions (FreeName)
open Lists (State)

private def child : Body.Definition :=
  ⟨"inner", ⟨[], [("early", starlark%[[73]]), ("saved", starlark%[x]), ("late", starlark%[[99]])]⟩,
    .assign "alias" starlark%[saved] (.ret starlark%[alias[x]])⟩

private def parent : LexicalBlock := ⟨["marker", "before", "inner", "after", "copy"], ["x"], []⟩

private theorem childBody :
    Body.Elaborates ⟨["early", "saved", "late", "alias"], parent.owned ++ parent.enclosing, []⟩ child.body
      (.seq (.assignExpr (fileSlot "alias") (Leaf.readOperand (fileSlot "saved")))
        (.returnExpr (.index (Leaf.readOperand (fileSlot "alias")) (Leaf.readOperand (fileSlot "x")))))
      [fileSlot "saved", fileSlot "alias", fileSlot "x"] :=
  .assign (by decide) (.read (by decide) (.owned (by decide)) (.owned (by decide)))
    (.ret (.index (.read (by decide) (.owned (by decide)) (.owned (by decide)))
      (.read (by decide) (.enclosing (by decide) (by decide)) (.enclosing (by decide) (by decide)))))

private theorem childDefaults :
    Lexical.Elaborates parent child.parameters.optional
      [⟨"early", starlark%[[73]], .list [.atom (.scalar (.int 73))], []⟩,
       ⟨"saved", starlark%[x], Leaf.readOperand (fileSlot "x"), [fileSlot "x"]⟩,
       ⟨"late", starlark%[[99]], .list [.atom (.scalar (.int 99))], []⟩] :=
  .cons (.list (.int 73))
    (.cons (.read (by decide) (.enclosing (by decide) (by decide)) (.enclosing (by decide) (by decide)))
      (.cons (.list (.int 99)) .nil))

-- The proof builds its plan from independent binder and read judgments.
example : Nonempty (Plan parent child) :=
  plan_of_body (by decide) (.keep (by decide) .nil) childBody childDefaults

-- A parent with no surrounding reads still propagates the nested
-- definition's requests into its own ordered capture list.
example (plan : Plan parent child) : ∃ free, Selects parent plan.reads free := by
  simpa using selects_parent plan (before := []) (after := []) (by simp)

private def firstChild : Body.Definition :=
  ⟨"before", ⟨[], []⟩, .ret starlark%[marker]⟩

private def lastChild : Body.Definition :=
  ⟨"after", ⟨[], []⟩, .ret starlark%[41]⟩

private def relayBody (shadowed : Bool) : Statement :=
  let relayTail := .ret (some starlark%[copy])
  let relayTail := if shadowed then .seq (.assign "x" starlark%[0]) relayTail else relayTail
  .seq (.assign "marker" starlark%[[17]])
    (.seq (statement firstChild)
      (.seq (statement child)
        (.seq (statement lastChild)
          (.seq (.assign "copy" starlark%[inner]) relayTail))))

private theorem sequenceProfile :
    ∃ resolved program, Sequence.Elaborates parent (relayBody false) #[] resolved program := by
  obtain ⟨first⟩ : Nonempty (Plan parent firstChild) :=
    plan_of_body (by decide) .nil
      (.ret (.read (by decide) (.enclosing (by decide) (by decide)) (.enclosing (by decide) (by decide)))) .nil
  obtain ⟨middle⟩ : Nonempty (Plan parent child) :=
    plan_of_body (by decide) (.keep (by decide) .nil) childBody childDefaults
  obtain ⟨last⟩ : Nonempty (Plan parent lastChild) :=
    plan_of_body (by decide) .nil (.ret (.int 41)) .nil
  have leading : Body.ElaboratesPrefix parent [("marker", starlark%[[17]])]
      [("marker", .list [.atom (.scalar (.int 17))])] [] :=
    .cons (by decide) (.list (.int 17)) .nil
  have ending : Body.Elaborates parent (.assign "copy" starlark%[inner] (.ret starlark%[copy]))
      (.seq (.assignExpr (fileSlot "copy") (Leaf.readOperand (fileSlot "inner")))
        (.returnExpr (Leaf.readOperand (fileSlot "copy")))) [fileSlot "inner", fileSlot "copy"] :=
    .assign (by decide) (.read (by decide) (.owned (by decide)) (.owned (by decide)))
      (.ret (.read (by decide) (.owned (by decide)) (.owned (by decide))))
  have profile := Sequence.Elaborates.define (seed := #[]) leading first
    (.define .nil middle (.define .nil last (.straight ending)))
  exact ⟨_, _, profile⟩

-- The normalized relay uses the general sequence theorem with its
-- independently elaborated body, including all three definitions.
example :
    ∃ resolved program, compileBody ⟨parent.context, .local⟩ (relayBody false) #[] = .ok (resolved, program) ∧
      ∃ free, Selects parent resolved.reads free ∧
        ∀ (active : State) (floor : Nat), Body.Frame parent free floor active →
          ∃ out, Sequence.Runs parent active (relayBody false) resolved.code out ∧
            Functions.denoteBody program (List.range program.size) resolved.code active = out := by
  obtain ⟨resolved, program, profile⟩ := sequenceProfile
  obtain ⟨free, selected⟩ := Sequence.selects profile
  refine ⟨resolved, program, Sequence.compiles profile, free, selected, ?_⟩
  intro active floor frame
  have selection : Selects parent ([] ++ resolved.reads ++ []) free := by simpa using selected
  obtain ⟨out, trace, _, _, _, exactResult⟩ :=
    Sequence.runs profile program (fun _ _ same => same) (List.range program.size) selection active frame
  exact ⟨out, trace, exactResult⟩

private def maker (shadowed failed : Bool) : Command :=
  let call := if shadowed then starlark%[relay(other)] else starlark%[relay()]
  let body := Statement.seq
    (.define "relay" (.required (if shadowed then ["x"] else [])) (relayBody shadowed))
    (.seq (.setIndex starlark%[notice] starlark%[0] starlark%[1])
      (.seq (.assign "escaped" call) (.seq (.assign "x" starlark%[1]) (.ret (some starlark%[escaped])))))
  .define "make" (.required ["seed"])
    (if failed then body else .seq (.assign "x" starlark%[seed]) body)

private def commands (shadowed failed : Bool) : List Command :=
  [.assign "original" starlark%[[11,22]], .assign "other" starlark%[[33,44]],
   .assign "notice" starlark%[[0]], maker shadowed failed, .assign "escaped" starlark%[make(original)],
   .assign "alias" starlark%[escaped], .assign "result" starlark%[alias()],
   .assign "override" starlark%[escaped(0,[91,92])]]

private def caller : State := { iterators := [123] }

private def checks (shadowed : Bool) : Bool :=
  match resolve (commands shadowed false), runModule (commands shadowed false) (fun _ => none) caller with
  | .ok resolved, .ok (.ok published final) =>
    let get name := published.exports.lookup name
    let seed := get (if shadowed then "other" else "original")
    let expectedIndex := if shadowed then 0 else 1
    (resolved.program[1]?.map (fun declaration => declaration.locals) == some [fileSlot "alias"]) &&
    (resolved.program[3]?.map (fun declaration => declaration.free.map FreeName.source) ==
      some (if shadowed then [] else [fileSlot "x"])) &&
    get "result" == some (.scalar (.int (if shadowed then 33 else 22))) &&
    get "override" == some (.scalar (.int (if shadowed then 91 else 92))) &&
    get "alias" == get "escaped" &&
    (match get "escaped" with
    | some (.function address) =>
      match final.heap[address]? with
      | some ⟨.function closure, true⟩ =>
        match closure.captures, closure.defaults with
        | [capture], [(_, .list early), (saved, snapshot), (_, .list late)] =>
          let relayCapture := final.heap.toList.findSome? fun cell =>
            match cell.contents with
            | .function relay => if relay.declaration == 3 then some relay.captures else none
            | _ => none
          closure.declaration == 1 && capture.binding == fileSlot "x" && capture.localCell &&
          relayCapture == some (if shadowed then [] else [capture]) &&
          saved == fileSlot "saved" && some snapshot == seed &&
          final.heap[capture.address]? == some ⟨.binding (some (.scalar (.int expectedIndex))), true⟩ &&
          final.heap[early]? == some ⟨.list [.scalar (.int 73)], true⟩ &&
          final.heap[late]? == some ⟨.list [.scalar (.int 99)], true⟩
        | _, _ => false
      | _ => false
    | _ => false)
  | _, _ => false

#guard checks false
#guard checks true

-- The first allocating default is retained. The later default, new
-- closure, module result and publication are all unreached.
#guard
  match resolve (commands false true), runModule (commands false true) (fun _ => none) caller with
  | .ok resolved, .ok (.error (.runtime (.uninitialized binding)) final) =>
    let initial := enter resolved.source caller
    let get name := (initial.slots (globalSlot name)).bind (fun slot => final.heap[slot.address]?)
    binding == fileSlot "x" &&
    get "escaped" == some ⟨.binding none, false⟩ &&
    get "alias" == some ⟨.binding none, false⟩ &&
    get "result" == some ⟨.binding none, false⟩ &&
    (match get "notice" with
    | some ⟨.binding (some (.list address)), false⟩ =>
      final.heap[address]? == some ⟨.list [.scalar (.int 1)], false⟩
    | _ => false) &&
    final.heap.back? == some ⟨.list [.scalar (.int 73)], false⟩ &&
    final.heap.any (fun cell => cell == ⟨.list [.scalar (.int 17)], false⟩) &&
    final.heap.any (fun cell => match cell.contents with
      | .function closure => closure.declaration == 0
      | _ => false) &&
    !(final.heap.any fun cell => match cell.contents with
      | .function closure => closure.declaration == 1 || closure.declaration == 2
      | _ => false) &&
    (final.slots (globalSlot "notice")).isNone && final.iterators == [123]
  | _, _ => false

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested

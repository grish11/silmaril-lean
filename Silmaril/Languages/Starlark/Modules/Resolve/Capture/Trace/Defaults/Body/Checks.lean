module

import Batteries.Data.Except
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Thms
import Silmaril.Languages.Starlark.Functions.Lowering.Quote.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.Defaults.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Defs

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body

open scoped Functions.Lowering.Quote
open Assignment (LexicalBlock)
open Lists (State Cell)

private def score : Definition :=
  ⟨"score", ⟨[], [("offset", starlark%[start])]⟩,
    .assign "cache" starlark%[[31]]
      (.assign "copy" starlark%[offset]
        (.assign "result" starlark%[table[copy]]
          (.assign "after" starlark%[[41]] (.ret starlark%[result]))))⟩

private def table : Command := .assign "table" starlark%[[9, 11]]
private def first : Command := invocation "saved" "first" []
private def second : Command := invocation "score" "second" [starlark%[0]]

private def commands (initialized : Bool) : List Command :=
  [.assign "start" starlark%[1], score.command, .assign "saved" starlark%[score]] ++
    if initialized then [table, first, second] else [first, table, second]

private theorem admitted (initialized : Bool) : Bindings.WithDefaults.Profile (commands initialized) := by
  let globals := names (commands initialized)
  let body := Bindings.WithDefaults.Callable.sequenced score
  have known {name : String}
      (member : name ∈ ["start", "score", "saved", "table", "first", "second"]) : Visible globals name := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
      cases initialized <;> unfold Visible <;> decide +revert
  let owned := ["offset", "cache", "copy", "result", "after"]
  let block : LexicalBlock := ⟨owned, [], globals⟩
  have localRead (name : String) (legal : name.toList.head? ≠ some '$') (member : name ∈ owned) :
      Operand block (.scalar (.read name)) (Leaf.readOperand (fileSlot name)) [fileSlot name] :=
    .read legal (.owned member) (.owned member)
  have hidden : "table" ∉ block.owned := by simp [block, owned]
  have outer : "table" ∉ block.enclosing := by simp [block]
  have captured : Operand block starlark%[table] (Leaf.readOperand (globalSlot "table")) [globalSlot "table"] :=
    .read (by decide) (.global hidden outer (known (by decide)).1)
      (.module hidden outer (known (by decide)).1)
  have profile : body.Admitted globals := by
    refine ⟨?_, ?_⟩
    · intro item h
      simp [score] at h
      subst item
      exact .operand (.read (known (by decide)))
    · have related := Elaborates.assign (block := block) (name := "cache")
        (by change "cache" ∈ owned; decide) (.list (.int 31))
        (.assign (name := "copy") (by change "copy" ∈ owned; decide) (localRead "offset" (by decide) (by decide))
          (.assign (name := "result") (by change "result" ∈ owned; decide)
            (.index captured (localRead "copy" (by decide) (by decide)))
            (.assign (name := "after") (by change "after" ∈ owned; decide) (.list (.int 41))
              (.ret (localRead "result" (by decide) (by decide))))))
      exact plan_of_suite globals score ["cache", "copy", "result", "after"]
        (.keep (by decide) (.keep (by decide) (.keep (by decide) (.keep (by decide) .nil)))) related
  have tableOk : Initializer globals starlark%[[9, 11]] := by
    apply Initializer.list
    intro item h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> exact .int _
  have oneArg : ∀ argument ∈ [starlark%[0]], Trace.Operand globals argument := by
    intro argument h
    simp at h
    subst argument
    exact .int 0
  change Bindings.WithDefaults.Schedule globals (fun _ => none) (commands initialized)
  unfold commands
  refine .setup (known (by decide)) (.operand (.int 1)) (.define (body := body) (known (name := "score") (by decide))
    profile (.copy (body := body) (known (by decide)) (known (by decide)) rfl ?_))
  cases initialized with
  | false =>
    exact .invoke (body := body) (known (by decide)) (known (by decide)) rfl (by simp)
      (.setup (known (by decide)) tableOk (.invoke (body := body) (known (by decide)) (known (by decide)) rfl oneArg (.nil _)))
  | true =>
    exact .setup (known (by decide)) tableOk
      (.invoke (body := body) (known (by decide)) (known (by decide)) rfl (by simp)
        (.invoke (body := body) (known (by decide)) (known (by decide)) rfl oneArg (.nil _)))

private def caller : State := { bindings := fun _ => some (.scalar (.int 99)), iterators := [123] }

example (initialized : Bool) {resolved : ResolvedModule} (checked : resolve (commands initialized) = .ok resolved) :
    ∃ out publication,
      Wrapper.ReachedPrefix (Bindings.WithDefaults.Step resolved (names (commands initialized))) 0
        (enter resolved.source caller) (commands initialized) out ∧
      Leaf.Finishes (names (commands initialized)) caller out publication ∧
      Initializes (commands initialized) (fun _ => none) caller #[] (.ok publication) ∧
      runModule (commands initialized) (fun _ => none) caller = .ok publication :=
  Bindings.WithDefaults.checked_module (admitted initialized) checked (fun _ => none) caller

#guard
  match resolve (commands true), runModule (commands true) (fun _ => none) caller with
  | .ok resolved, .ok (.ok published final) =>
    let initial := enter resolved.source caller
    published.exports.lookup "first" == some (.scalar (.int 11)) &&
    published.exports.lookup "second" == some (.scalar (.int 9)) &&
    published.exports.lookup "score" == published.exports.lookup "saved" &&
    (match published.exports.lookup "table", published.exports.lookup "score" with
      | some (.list table), some (.function function) =>
        final.heap[table]? == some ⟨.list [.scalar (.int 9), .scalar (.int 11)], true⟩ &&
        (match final.heap[function]? with
          | some ⟨.function closure, true⟩ =>
            closure.defaults == [(fileSlot "offset", .scalar (.int 1))] &&
            (match closure.captures with
              | [capture] => capture.binding == globalSlot "table" && !capture.localCell &&
                (match initial.slots (globalSlot "table") with
                  | some (.owned address) => capture.address == address
                  | _ => false)
              | _ => false)
          | _ => false)
      | _, _ => false) &&
    final.iterators == [123]
  | _, _ => false

#guard
  match resolve (commands false), runModule (commands false) (fun _ => none) caller with
  | .ok resolved, .ok (.error (.runtime (.uninitialized binding)) final) =>
    let initial := enter resolved.source caller
    let get (name : String) : Option Lists.Contents :=
      match initial.slots (globalSlot name) with
      | some (.owned address) => final.heap[address]?.map Cell.contents
      | _ => none
    let active := initial.heap.size + 1
    binding == globalSlot "table" && get "first" == some (.binding none) &&
    get "second" == some (.binding none) && get "table" == some (.binding none) &&
    final.heap[active + 1]?.map Cell.contents == some (.binding (some (.list (active + 5)))) &&
    final.heap[active + 2]? == some ⟨.binding (some (.scalar (.int 1))), false⟩ &&
    final.heap[active + 3]? == some ⟨.binding none, false⟩ &&
    final.heap[active + 4]? == some ⟨.binding none, false⟩ &&
    final.heap[active + 5]? == some ⟨.list [.scalar (.int 31)], false⟩ &&
    final.heap.size == active + 6 &&
    final.bindingValue (globalSlot "first") == .ok (.scalar (.int 99)) && final.iterators == [123]
  | _, _ => false

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body

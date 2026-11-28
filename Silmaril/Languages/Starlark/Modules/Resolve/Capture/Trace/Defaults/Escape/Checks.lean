module

import Batteries.Data.Except
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.Defaults.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Thms
import Silmaril.Languages.Starlark.Functions.Lowering.Quote.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.Defaults.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Defs

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape

open scoped Functions.Lowering.Quote
open Lists (State Cell)
open Bindings.WithDefaults (Callable)

private def maker (fails : Bool) : Spec :=
  ⟨"maker", "seed", "inner", ["seed"],
    if fails then [("kept", .list 1), ("value", .index 1), ("skipped", .list 3)]
    else [("value", .parameter), ("buffer", .list 1)], "value", 91⟩

private def commands (fails : Bool) : List Command :=
  [(maker fails).command, .assign "saved_seed" starlark%[[3]],
    invocation "maker" "escaped" [starlark%[saved_seed]], .assign "saved" starlark%[escaped],
    invocation "saved" "first" [starlark%[0]], .assign "replacement" starlark%[[4]],
    invocation "saved" "override" [starlark%[0], starlark%[replacement]],
    invocation "escaped" "again" [starlark%[0]]]

private theorem admitted (fails : Bool) : Bindings.WithDefaults.Profile (commands fails) := by
  let globals := names (commands fails)
  let body := Callable.escaping (maker fails)
  let child := Callable.defaulted (maker fails).child
  have known {name : String} (member : name ∈
      ["maker", "saved_seed", "escaped", "saved", "first", "replacement", "override", "again"]) :
      Visible globals name := by
    change name ∈ names (commands fails) ∧ _
    constructor
    · exact member
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have wrapperOK : body.Admitted globals := by
    change Admitted (maker fails)
    cases fails <;> refine ⟨by decide, by decide, by decide, by unfold Visible; decide, ?_⟩
    all_goals intro name present; obtain ⟨target, present⟩ := present; simp [maker] at present
  have single (value : Int) : Initializer globals (.list [.scalar (.int value)]) :=
    .list (by intro _ h; simp at h; subst_vars; exact .int _)
  have readArg : ∀ argument ∈ [starlark%[saved_seed]], Trace.Operand globals argument := by
    intro argument present
    simp at present
    subst argument
    exact .read (known (by decide))
  have oneArg : ∀ argument ∈ [starlark%[0]], Trace.Operand globals argument := by
    intro argument present
    simp at present
    subst argument
    exact .int _
  have overrideArg : ∀ argument ∈ [starlark%[0], starlark%[replacement]], Trace.Operand globals argument := by
    intro argument present
    simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl
    · exact .int _
    · exact .read (known (by decide))
  unfold Bindings.WithDefaults.Profile
  change Bindings.WithDefaults.Schedule globals (fun _ => none) (commands fails)
  unfold commands
  exact .define (body := body) (known (name := "maker") (by decide)) wrapperOK
    (.setup (known (by decide)) (single 3)
    (.invoke (body := body) (known (by decide)) (known (by decide)) rfl readArg
    (.copy (body := child) (known (by decide)) (known (by decide)) rfl
    (.invoke (body := child) (known (by decide)) (known (by decide)) rfl oneArg
    (.setup (known (by decide)) (single 4)
    (.invoke (body := child) (known (by decide)) (known (by decide)) rfl overrideArg
    (.invoke (body := child) (known (by decide)) (known (by decide)) rfl oneArg (.nil _))))))))

private def caller : State := { bindings := fun _ => some (.scalar (.int 99)), iterators := [123] }

example (fails : Bool) {resolved : ResolvedModule} (checked : resolve (commands fails) = .ok resolved) :
    ∃ out publication,
      Wrapper.ReachedPrefix (Bindings.WithDefaults.Step resolved (names (commands fails))) 0 (enter resolved.source caller) (commands fails) out ∧
      Leaf.Finishes (names (commands fails)) caller out publication ∧
      Initializes (commands fails) (fun _ => none) caller #[] (.ok publication) ∧
      runModule (commands fails) (fun _ => none) caller = .ok publication :=
  Bindings.WithDefaults.checked_module (admitted fails) checked (fun _ => none) caller

#guard
  match runModule (commands false) (fun _ => none) caller with
  | .ok (.ok published final) =>
    let get := fun name => published.exports.lookup name
    match get "saved_seed", get "escaped", get "maker" with
    | some (.list seed), some (.function address), some (.function root) =>
      get "saved" == get "escaped" && get "first" == get "saved_seed" && get "again" == get "saved_seed" &&
      get "override" == get "replacement" &&
      final.heap[seed]? == some ⟨.list [.scalar (.int 3)], true⟩ &&
      final.heap.any (fun cell => cell.contents == .binding (some (.scalar (.int 91)))) &&
      (match final.heap[address]?, final.heap[root]? with
       | some ⟨.function child, true⟩, some ⟨.function parent, true⟩ =>
         child.declaration == 0 && parent.declaration == 1 && child.captures.isEmpty &&
         (match child.defaults with
          | [(_, .list saved), (_, .list buffer)] =>
            saved == seed && final.heap[buffer]? == some ⟨.list [.scalar (.int 1)], true⟩ &&
            (final.heap.filter (fun cell => cell.contents == .list [.scalar (.int 1)])).size == 1
          | _ => false)
       | _, _ => false) && final.iterators == [123]
    | _, _, _ => false
  | _ => false

#guard
  match resolve (commands true), runModule (commands true) (fun _ => none) caller with
  | .ok resolved, .ok (.error (.runtime (.indexRange 1 1)) final) =>
    let initial := enter resolved.source caller
    let get (name : String) : Option Lists.Contents := match initial.slots (globalSlot name) with
      | some (.owned address) => final.heap[address]?.map Cell.contents
      | _ => none
    -- Module slots, wrapper closure, seed list, two activation slots, and
    -- the first default's list are all the reached allocations.
    let args := initial.heap.size + 2
    final.heap.size == args + 3 &&
    final.heap[args + 1]? == some ⟨.binding none, false⟩ &&
    final.heap[args + 2]? == some ⟨.list [.scalar (.int 1)], false⟩ &&
    (match get "saved_seed" with
    | some (.binding (some (.list seed))) => final.heap[args]? == some ⟨.binding (some (.list seed)), false⟩
    | _ => false) &&
    get "escaped" == some (.binding none) && get "saved" == some (.binding none) && get "first" == some (.binding none) &&
    final.bindingValue (globalSlot "escaped") == .ok (.scalar (.int 99)) && final.iterators == [123]
  | _, _ => false

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape

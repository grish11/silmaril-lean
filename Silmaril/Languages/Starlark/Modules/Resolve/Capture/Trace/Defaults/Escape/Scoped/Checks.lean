module

import Batteries.Data.Except
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped.Thms
import Silmaril.Languages.Starlark.Functions.Lowering.Quote.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.Defaults.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Defs

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped

open scoped Functions.Lowering.Quote
open Assignment (LexicalBlock)
open Bindings.WithDefaults (Callable)
open Lists (State Cell)

private def maker : Spec :=
  ⟨⟨"make", "seed", "inner", [], [("saved", .parameter)], "answer", 0⟩,
    [("cache", starlark%[[31]]), ("picked", starlark%[saved[offset]]),
      ("buffer", starlark%[[picked]]), ("answer", starlark%[buffer[seed]]),
      ("repeat_read", starlark%[saved[offset]]), ("after", starlark%[[41]])], ["offset"]⟩

private def replacement (fails : Bool) : Functions.Lowering.Resolve.SourceExpr :=
  if fails then starlark%[[7]] else starlark%[[7, 9]]

private def commands (fails : Bool) : List Command :=
  [maker.command, .assign "seed_a" starlark%[[3, 5]], .assign "seed_b" starlark%[[6, 8]],
    invocation "make" "a" [starlark%[seed_a], starlark%[1]], invocation "make" "b" [starlark%[seed_b], starlark%[0]],
    .assign "alias" starlark%[a], invocation "alias" "first" [], invocation "b" "second" [],
    .assign "replacement" (replacement fails), invocation "a" "override" [starlark%[replacement]],
    invocation "alias" "again" []]

private theorem admitted (fails : Bool) : Bindings.WithDefaults.Profile (commands fails) := by
  let globals := names (commands fails)
  have known {name : String}
      (member : name ∈ ["make", "seed_a", "seed_b", "a", "b", "alias",
        "first", "second", "replacement", "override", "again"]) : Visible globals name := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      cases fails <;> unfold Visible <;> decide +revert
  let child := maker.child
  let locals := ["cache", "picked", "buffer", "answer", "repeat_read", "after"]
  let owned := ["saved", "cache", "picked", "buffer", "answer", "repeat_read", "after"]
  let block : LexicalBlock := ⟨child.parameters.names ++ locals, maker.enclosing, globals⟩
  have inBlock {name : String} (member : name ∈ owned) : name ∈ block.owned := member
  have localOrigin {name : String} (member : name ∈ owned) : ReadOrigin block (fileSlot name) .owned :=
    .owned (inBlock member)
  have localRead (name : String) (member : name ∈ owned) (legal : name.toList.head? ≠ some '$') :
      Defaults.Body.Operand block (.scalar (.read name)) (Leaf.readOperand (fileSlot name)) [fileSlot name] :=
    .read legal (.owned (inBlock member)) (localOrigin member)
  have outerOrigin {name : String} (outside : name ∉ owned) (member : name ∈ ["seed", "offset", "inner"]) :
      ReadOrigin block (fileSlot name) .enclosing :=
    .enclosing outside member
  have outerRead (name : String) (outside : name ∉ owned) (member : name ∈ ["seed", "offset", "inner"])
      (legal : name.toList.head? ≠ some '$') :
      Defaults.Body.Operand block (.scalar (.read name)) (Leaf.readOperand (fileSlot name)) [fileSlot name] :=
    .read legal (.enclosing outside member) (outerOrigin outside member)
  have wrapper : Admitted globals maker := by
    refine ⟨⟨⟨by decide, by decide, by decide⟩, by decide⟩, ?_⟩
    have pick := Defaults.Body.Operand.index (localRead "saved" (by decide) (by decide))
      (outerRead "offset" (by decide) (by decide) (by decide))
    have code := Defaults.Body.Elaborates.assign (block := block) (name := "cache") (inBlock (by decide)) (.list (.int 31))
      (.assign (name := "picked") (inBlock (by decide)) pick
        (.assign (name := "buffer") (inBlock (by decide)) (.list (localRead "picked" (by decide) (by decide)))
          (.assign (name := "answer") (inBlock (by decide))
            (.index (localRead "buffer" (by decide) (by decide)) (outerRead "seed" (by decide) (by decide) (by decide)))
            (.assign (name := "repeat_read") (inBlock (by decide)) pick
              (.assign (name := "after") (inBlock (by decide)) (.list (.int 41))
                (.ret (localRead "answer" (by decide) (by decide))))))))
    let entries : List Functions.FreeName :=
      [⟨fileSlot "offset", fileSlot "offset"⟩, ⟨fileSlot "seed", fileSlot "seed"⟩]
    have selects : Selects block
        [fileSlot "saved", fileSlot "offset", fileSlot "picked", fileSlot "buffer", fileSlot "seed",
          fileSlot "saved", fileSlot "offset", fileSlot "answer"] entries := by
      apply Selects.owned (localOrigin (name := "saved") (by decide))
      apply Selects.enclosing (outerOrigin (name := "offset") (by decide) (by decide))
      apply Selects.owned (localOrigin (name := "picked") (by decide))
      apply Selects.owned (localOrigin (name := "buffer") (by decide))
      apply Selects.enclosing (outerOrigin (name := "seed") (by decide) (by decide))
      exact .owned (localOrigin (name := "answer") (by decide)) .nil
    refine ⟨⟨⟨locals, _, _, entries, .keep (by decide) (.keep (by decide) (.keep (by decide)
      (.keep (by decide) (.keep (by decide) (.keep (by decide) .nil))))), code, selects⟩, ?_⟩⟩
    intro entry member
    change entry ∈ entries at member
    simp [entries] at member
    rcases member with rfl | rfl
    · exact ⟨"offset", by decide, rfl⟩
    · exact ⟨"seed", by decide, rfl⟩
  have pair (first second : Int) : Initializer globals (.list [.scalar (.int first), .scalar (.int second)]) :=
    .list (by intro item member; simp at member; rcases member with rfl | rfl <;> exact .int _)
  have replace : Initializer globals (replacement fails) := by
    cases fails
    · exact pair 7 9
    · exact .list (by intro item member; simp at member; subst item; exact .int _)
  have read {name : String} (visible : Visible globals name) :
      ∀ argument ∈ [(.scalar (.read name) : Functions.Lowering.Resolve.SourceExpr)], Trace.Operand globals argument := by
    intro argument present
    simp at present
    subst argument
    exact .read visible
  have wrapperArgs {name : String} (visible : Visible globals name) (index : Int) :
      ∀ argument ∈ [(.scalar (.read name) : Functions.Lowering.Resolve.SourceExpr), .scalar (.int index)],
        Trace.Operand globals argument := by
    intro argument present
    simp at present
    rcases present with rfl | rfl
    · exact .read visible
    · exact .int index
  let parent := Callable.nestedBody maker
  let escaped := Callable.sequenced maker.child
  change Bindings.WithDefaults.Schedule globals (fun _ => none) (commands fails)
  unfold commands
  exact .define (body := parent) (known (name := "make") (by decide)) wrapper
    (.setup (known (by decide)) (pair 3 5) (.setup (known (by decide)) (pair 6 8)
      (.invoke (body := parent) (known (by decide)) (known (by decide)) rfl (wrapperArgs (known (by decide)) 1)
        (.invoke (body := parent) (known (by decide)) (known (by decide)) rfl (wrapperArgs (known (by decide)) 0)
          (.copy (body := escaped) (known (by decide)) (known (by decide)) rfl
            (.invoke (body := escaped) (known (by decide)) (known (by decide)) rfl (by simp)
              (.invoke (body := escaped) (known (by decide)) (known (by decide)) rfl (by simp)
                (.setup (known (by decide)) replace
                  (.invoke (body := escaped) (known (by decide)) (known (by decide)) rfl (read (known (by decide)))
                    (.invoke (body := escaped) (known (by decide)) (known (by decide)) rfl (by simp) (.nil _)))))))))))

private def caller : State := { bindings := fun _ => some (.scalar (.int 99)), iterators := [123] }

example (fails : Bool) {resolved : ResolvedModule} (checked : resolve (commands fails) = .ok resolved) :
    ∃ out publication,
      Wrapper.ReachedPrefix (Bindings.WithDefaults.Step resolved (names (commands fails))) 0
        (enter resolved.source caller) (commands fails) out ∧
      Leaf.Finishes (names (commands fails)) caller out publication ∧
      Initializes (commands fails) (fun _ => none) caller #[] (.ok publication) ∧
      runModule (commands fails) (fun _ => none) caller = .ok publication :=
  Bindings.WithDefaults.checked_module (admitted fails) checked (fun _ => none) caller

private def captureAddresses (heap : Array Cell) (closure seed : Lists.Value)
    (offset : Int) : Option (List Nat) := do
  let .function address := closure | none
  let ⟨.function child, true⟩ ← heap[address]? | none
  let [first, second] := child.captures | none
  if child.declaration == 0 && child.defaults == [(fileSlot "saved", seed)] &&
      first.binding == fileSlot "offset" && first.localCell &&
      second.binding == fileSlot "seed" && second.localCell &&
      heap[first.address]? == some ⟨.binding (some (.scalar (.int offset))), true⟩ &&
      heap[second.address]? == some ⟨.binding (some (.scalar (.int 0))), true⟩ then
    some [first.address, second.address]
  else none

#guard
  match resolve (commands false), runModule (commands false) (fun _ => none) caller with
  | .ok resolved, .ok (.ok published final) =>
    let entered := (enter resolved.source caller).heap.size
    let get name := published.exports.lookup name
    match get "a", get "b", get "seed_a", get "seed_b" with
    | some a, some b, some (.list seedA), some (.list seedB) =>
      get "alias" == some a && a != b &&
      get "first" == some (.scalar (.int 5)) && get "second" == some (.scalar (.int 6)) &&
      get "override" == some (.scalar (.int 9)) && get "again" == some (.scalar (.int 5)) &&
      final.heap[seedA]? == some ⟨.list [.scalar (.int 3), .scalar (.int 5)], true⟩ &&
      final.heap[seedB]? == some ⟨.list [.scalar (.int 6), .scalar (.int 8)], true⟩ &&
      captureAddresses final.heap a (.list seedA) 1 == some [entered + 4, entered + 3] &&
      captureAddresses final.heap b (.list seedB) 0 == some [entered + 8, entered + 7] &&
      final.bindingValue (globalSlot "first") == .ok (.scalar (.int 99)) && final.iterators == [123]
    | _, _, _, _ => false
  | _, _ => false

#guard
  match resolve (commands true), runModule (commands true) (fun _ => none) caller with
  | .ok resolved, .ok (.error (.runtime (.indexRange 1 1)) final) =>
    let initial := enter resolved.source caller
    let get (name : String) : Option Lists.Contents :=
      match initial.slots (globalSlot name) with
      | some (.owned address) => final.heap[address]?.map Cell.contents
      | _ => none
    -- One wrapper closure, two seed lists, two wrapper activations of four cells each,
    -- two child activations of ten cells each, and the explicit replacement list.
    let active := initial.heap.size + 32
    final.heap.size == active + 8 &&
    get "first" == some (.binding (some (.scalar (.int 5)))) &&
    get "second" == some (.binding (some (.scalar (.int 6)))) &&
    get "a" == get "alias" && get "override" == some (.binding none) && get "again" == some (.binding none) &&
    final.heap[active + 1]? == some ⟨.binding (some (.list (active + 7))), false⟩ &&
    ([2, 3, 4, 5, 6] : List Nat).all (fun index => final.heap[active + index]? == some ⟨.binding none, false⟩) &&
    final.heap[active + 7]? == some ⟨.list [.scalar (.int 31)], false⟩ &&
    (final.heap.filter (fun cell => cell.contents == .list [.scalar (.int 41)])).size == 2 &&
    final.bindingValue (globalSlot "override") == .ok (.scalar (.int 99)) && final.iterators == [123]
  | _, _ => false

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped

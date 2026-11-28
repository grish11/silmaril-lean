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

private inductive End where
  | success | prefixError | defaultError | moduleError | moduleDefaultError

private def firstIndex : End → Int
  | .prefixError => 1
  | _ => 0

private def defaultName : End → String
  | .defaultError => "unused"
  | _ => "offset"

private def maker (ending : End) : Spec :=
  ⟨⟨"make", "seed", "inner", [], [("early", .list 14),
      ("saved", .read (defaultName ending)), ("setting_at_def", .read "setting"), ("shadow_at_def", .read "shadow"),
      ("last", .list 73)], "answer", 0⟩,
    [("picked", starlark%[saved[offset]]), ("buffer", starlark%[[[saved[setting_at_def]]]]),
      ("answer", starlark%[buffer[shadow_at_def][seed]]), ("repeat_read", starlark%[saved[offset]])],
    [], [("offset", 0), ("unused", 42), ("offset", 1)],
    [("earlier", starlark%[[13]]), ("shadow", starlark%[seed]), ("offset", starlark%[table[shadow]])]⟩

private def edit : Callable := .required
  (.mixed "edit" ["index"] ⟨"index", starlark%[table], starlark%[index], .plain starlark%[patch], starlark%[index]⟩)

private def initialTable : Command := .assign "table" starlark%[outer_a]

private def initialSetting : Command := .assign "setting" starlark%[1]

private def firstCall (ending : End) : Command :=
  invocation "make" "a" [.scalar (.int (firstIndex ending))]

private def firstCommands (ending : End) : List Command :=
  match ending with
  | .moduleError => [initialSetting, firstCall ending, initialTable]
  | .moduleDefaultError => [initialTable, firstCall ending, initialSetting]
  | _ => [initialTable, initialSetting, firstCall ending]

private def commands (ending : End) : List Command :=
  [(maker ending).command, .assign "shadow" starlark%[99],
    .assign "seed_a" starlark%[[3, 5]], .assign "seed_b" starlark%[[6, 8]],
    .assign "outer_a" starlark%[[seed_a]]] ++
  firstCommands ending ++
  [.assign "make_alias" starlark%[make], edit.command, .assign "patch" starlark%[(0, seed_b)],
    invocation "edit" "touched" [starlark%[0]], invocation "make_alias" "b" [starlark%[0]],
    .assign "alias" starlark%[a], invocation "alias" "first" [], invocation "b" "second" [],
    .assign "replacement" starlark%[[7, 9]], invocation "a" "override" [starlark%[0], starlark%[replacement]],
    invocation "alias" "again" []]

private theorem admitted (ending : End) : Bindings.WithDefaults.Profile (commands ending) := by
  let globals := names (commands ending)
  have known {name : String}
      (member : name ∈ ["make", "shadow", "seed_a", "seed_b", "outer_a", "table", "setting", "a", "make_alias", "edit", "patch", "touched", "b", "alias",
        "first", "second", "replacement", "override", "again"]) : Visible globals name := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      cases ending <;> unfold Visible <;> decide +revert
  let spec := maker ending
  let locals := ["picked", "buffer", "answer", "repeat_read"]
  let owned := ["early", "saved", "setting_at_def", "shadow_at_def", "last", "picked", "buffer", "answer", "repeat_read"]
  let block : LexicalBlock := ⟨spec.child.parameters.names ++ locals, spec.enclosing, globals⟩
  have inBlock {name : String} (member : name ∈ owned) : name ∈ block.owned := by
    cases ending <;> exact member
  have localOrigin {name : String} (member : name ∈ owned) : ReadOrigin block (fileSlot name) .owned :=
    .owned (inBlock member)
  have localRead (name : String) (member : name ∈ owned) (legal : name.toList.head? ≠ some '$') :
      Defaults.Body.Operand block (.scalar (.read name)) (Leaf.readOperand (fileSlot name)) [fileSlot name] :=
    .read legal (.owned (inBlock member)) (localOrigin member)
  have outsideBlock {name : String} (outside : name ∉ owned) : name ∉ block.owned := by
    cases ending <;> exact outside
  have outerOrigin {name : String} (outside : name ∉ owned) (member : name ∈ ["seed", "earlier", "shadow", "offset", "inner", "unused"]) :
      ReadOrigin block (fileSlot name) .enclosing :=
    .enclosing (outsideBlock outside) member
  have outerRead (name : String) (outside : name ∉ owned) (member : name ∈ ["seed", "earlier", "shadow", "offset", "inner", "unused"])
      (legal : name.toList.head? ≠ some '$') :
      Defaults.Body.Operand block (.scalar (.read name)) (Leaf.readOperand (fileSlot name)) [fileSlot name] :=
    .read legal (.enclosing (outsideBlock outside) member) (outerOrigin outside member)
  have wrapper : Admitted globals spec := by
    have wrapperNames : Escape.WrapperNames spec.wrapper := by
      cases ending <;> exact ⟨by decide, by decide, by decide⟩
    have childFresh : spec.wrapper.childName ∉ spec.additional := by change "inner" ∉ ([] : List String); decide
    refine ⟨⟨wrapperNames, childFresh, ?_⟩, ?_⟩
    · intro name member
      change name ∈ ["offset", "unused", "offset"] at member
      simp at member
      rcases member with rfl | rfl | rfl <;> cases ending <;> decide
    · have pick := Defaults.Body.Operand.index (localRead "saved" (by decide) (by decide))
        (outerRead "offset" (by decide) (by decide) (by decide))
      have code := Defaults.Body.Elaborates.assign (block := block) (name := "picked") (inBlock (by decide)) pick
        (.assign (name := "buffer") (inBlock (by decide))
          (.list (.list (.index (localRead "saved" (by decide) (by decide)) (localRead "setting_at_def" (by decide) (by decide)))))
          (.assign (name := "answer") (inBlock (by decide))
            (.index (.index (localRead "buffer" (by decide) (by decide)) (localRead "shadow_at_def" (by decide) (by decide)))
              (outerRead "seed" (by decide) (by decide) (by decide)))
            (.assign (name := "repeat_read") (inBlock (by decide)) pick
              (.ret (localRead "answer" (by decide) (by decide))))))
      let entries : List Functions.FreeName :=
        [⟨fileSlot "offset", fileSlot "offset"⟩, ⟨fileSlot "seed", fileSlot "seed"⟩]
      have selects : Selects block
          [fileSlot "saved", fileSlot "offset", fileSlot "saved", fileSlot "setting_at_def",
            fileSlot "buffer", fileSlot "shadow_at_def", fileSlot "seed", fileSlot "saved", fileSlot "offset", fileSlot "answer"]
          entries := by
        apply Selects.owned (localOrigin (name := "saved") (by decide))
        apply Selects.enclosing (outerOrigin (name := "offset") (by decide) (by decide))
        apply Selects.owned (localOrigin (name := "setting_at_def") (by decide))
        apply Selects.owned (localOrigin (name := "buffer") (by decide))
        apply Selects.owned (localOrigin (name := "shadow_at_def") (by decide))
        apply Selects.enclosing (outerOrigin (name := "seed") (by decide) (by decide))
        exact .owned (localOrigin (name := "answer") (by decide)) .nil
      have binders : Block.LocalBinders spec.child.parameters.names spec.child.body.binders locals := by
        cases ending <;> exact .keep (by decide) (.keep (by decide) (.keep (by decide) (.keep (by decide) .nil)))
      have member {name : String} (known : name ∈ ["seed", "earlier", "shadow", "offset", "inner", "unused"]) :
          name ∈ (spec.block globals).owned := known
      let outerBlock := spec.block globals
      have ownedRead (name : String) (eligible : name ∈ ["seed", "earlier", "shadow", "offset", "inner", "unused"])
          (legal : name.toList.head? ≠ some '$') :
          Defaults.Body.Operand outerBlock (.scalar (.read name)) (Leaf.readOperand (fileSlot name)) [fileSlot name] :=
        .read legal (.owned (member eligible)) (.owned (member eligible))
      have hidden : "table" ∉ outerBlock.owned := show "table" ∉ ["seed", "earlier", "shadow", "offset", "inner", "unused"] by decide
      have table : Defaults.Body.Operand outerBlock starlark%[table]
          (Leaf.readOperand (globalSlot "table")) [globalSlot "table"] :=
        .read (by decide) (.global hidden (by simp [outerBlock, Spec.block]) (known (by decide)).1)
          (.module hidden (by simp [outerBlock, Spec.block]) (known (by decide)).1)
      have settingHidden : "setting" ∉ outerBlock.owned :=
        show "setting" ∉ ["seed", "earlier", "shadow", "offset", "inner", "unused"] by decide
      have setting : Defaults.Body.Operand outerBlock starlark%[setting]
          (Leaf.readOperand (globalSlot "setting")) [globalSlot "setting"] :=
        .read (by decide) (.global settingHidden (by simp [outerBlock, Spec.block]) (known (by decide)).1)
          (.module settingHidden (by simp [outerBlock, Spec.block]) (known (by decide)).1)
      have leading := Defaults.Body.ElaboratesPrefix.cons (name := "earlier") (member (by decide)) (.list (.int 13))
        (.cons (name := "shadow") (member (by decide)) (ownedRead "seed" (by decide) (by decide))
          (.cons (name := "offset") (member (by decide)) (.index table (ownedRead "shadow" (by decide) (by decide))) .nil))
      have chosen : defaultName ending ∈ ["seed", "earlier", "shadow", "offset", "inner", "unused"] := by
        cases ending <;> decide
      have legal : (defaultName ending).toList.head? ≠ some '$' := by cases ending <;> decide
      have defaults := Lexical.Elaborates.cons (name := "early") (.list (.int 14))
        (.cons (name := "saved") (ownedRead (defaultName ending) chosen legal)
          (.cons (name := "setting_at_def") setting
            (.cons (name := "shadow_at_def") (ownedRead "shadow" (by decide) (by decide))
              (.cons (name := "last") (.list (.int 73)) .nil))))
      refine ⟨⟨⟨locals, _, _, entries, binders, code, selects⟩, ?_, _,
        [fileSlot "seed", globalSlot "table", fileSlot "shadow"], leading, _, defaults,
        [⟨globalSlot "table", globalSlot "table"⟩, ⟨globalSlot "setting", globalSlot "setting"⟩], ?_⟩⟩
      · intro entry present
        change entry ∈ entries at present
        simp [entries] at present
        rcases present with rfl | rfl
        · exact ⟨"offset", member (by decide), by change "offset" ≠ "inner"; decide, rfl⟩
        · exact ⟨"seed", member (by decide), by change "seed" ≠ "inner"; decide, rfl⟩
      · have tableOrigin : ReadOrigin outerBlock (globalSlot "table") .module :=
          .module hidden (by simp [outerBlock, Spec.block]) (known (by decide)).1
        have settingOrigin : ReadOrigin outerBlock (globalSlot "setting") .module :=
          .module settingHidden (by simp [outerBlock, Spec.block]) (known (by decide)).1
        cases ending <;>
          exact .owned (.owned (name := "seed") (member (by decide)))
            (.module tableOrigin (.owned (.owned (name := "shadow") (member (by decide)))
              (.owned (.owned (member chosen)) (.module settingOrigin .nil))))
  have pair (first second : Int) : Initializer globals (.list [.scalar (.int first), .scalar (.int second)]) :=
    .list (by intro item member; simp at member; rcases member with rfl | rfl <;> exact .int _)
  have read {name : String} (visible : Visible globals name) :
      ∀ argument ∈ [(.scalar (.read name) : Functions.Lowering.Resolve.SourceExpr)], Trace.Operand globals argument := by
    intro argument present
    simp at present
    subst argument
    exact .read visible
  have singleton {name : String} (visible : Visible globals name) : Initializer globals (.list [.scalar (.read name)]) :=
    .list (read visible)
  have overrideArgs : ∀ argument ∈ [starlark%[0], starlark%[replacement]], Trace.Operand globals argument := by
    intro argument present
    simp at present
    rcases present with rfl | rfl
    · exact .int 0
    · exact .read (known (by decide))
  have editOk : edit.Admitted globals := by
    change Definitions globals [] _
    refine .mixed (by intro name h; simp at h; subst name; decide) (by decide) ?_ ?_ ?_ ?_
    · exact ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (known (by decide)).1), by decide⟩
    · exact ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (known (by decide)).1), by decide⟩
    · exact ⟨List.mem_cons_self, by decide⟩
    · exact ⟨List.mem_cons_self, by decide⟩
  have patchOk : Initializer globals starlark%[(0, seed_b)] := by
    apply Initializer.tuple
    intro item present
    simp at present
    rcases present with rfl | rfl
    · exact .int 0
    · exact .read (known (by decide))
  let parent := Callable.nestedBody spec
  let escaped := Callable.sequenced spec.child
  have initial : Initializer globals starlark%[outer_a] := .operand (.read (known (by decide)))
  have indexArg (index : Int) : ∀ argument ∈ [(.scalar (.int index) : Functions.Lowering.Resolve.SourceExpr)],
      Trace.Operand globals argument := by
    intro argument present
    have same := List.mem_singleton.mp present
    subst argument
    exact .int index
  change Bindings.WithDefaults.Schedule globals (fun _ => none) (commands ending)
  unfold commands
  refine .define (body := parent) (known (name := "make") (by decide)) wrapper
    (.setup (known (by decide)) (.operand (.int 99))
      (.setup (known (by decide)) (pair 3 5) (.setup (known (by decide)) (pair 6 8)
        (.setup (known (by decide)) (singleton (known (by decide))) ?_))))
  have rest : ∀ entries, entries "make" = some parent → entries "a" = some escaped →
      Bindings.WithDefaults.Schedule globals entries
        [.assign "make_alias" starlark%[make], edit.command, .assign "patch" starlark%[(0, seed_b)],
          invocation "edit" "touched" [starlark%[0]], invocation "make_alias" "b" [starlark%[0]],
          .assign "alias" starlark%[a], invocation "alias" "first" [], invocation "b" "second" [],
          .assign "replacement" starlark%[[7, 9]], invocation "a" "override" [starlark%[0], starlark%[replacement]],
          invocation "alias" "again" []] := by
    intro entries root childAt
    refine .copy (body := parent) (known (by decide)) (known (by decide)) root
      (.define (body := edit) (known (by decide)) editOk
        (.setup (known (by decide)) patchOk
          (.invoke (body := edit) (known (by decide)) (known (by decide)) rfl (indexArg 0)
            (.invoke (body := parent) (known (by decide)) (known (by decide)) rfl (indexArg 0)
              (.copy (body := escaped) (known (by decide)) (known (by decide)) ?_
                (.invoke (body := escaped) (known (by decide)) (known (by decide)) rfl (by simp)
                  (.invoke (body := escaped) (known (by decide)) (known (by decide)) rfl (by simp)
                    (.setup (known (by decide)) (pair 7 9)
                      (.invoke (body := escaped) (known (by decide)) (known (by decide)) ?_ overrideArgs
                        (.invoke (body := escaped) (known (by decide)) (known (by decide)) rfl (by simp) (.nil _)))))))))))
    all_goals simpa [Bindings.WithDefaults.Entries.write, edit, Callable.name, Forwarding.Chain.name] using childAt
  cases ending
  case moduleError =>
    exact .setup (name := "setting") (known (by decide)) (.operand (.int 1))
      (.invoke (body := parent) (known (by decide)) (known (by decide)) rfl (indexArg 0)
        (.setup (known (by decide)) initial (rest _ rfl rfl)))
  case moduleDefaultError =>
    exact .setup (name := "table") (known (by decide)) initial
      (.invoke (body := parent) (known (by decide)) (known (by decide)) rfl (indexArg 0)
        (.setup (name := "setting") (known (by decide)) (.operand (.int 1)) (rest _ rfl rfl)))
  all_goals
    exact .setup (name := "table") (known (by decide)) initial
      (.setup (name := "setting") (known (by decide)) (.operand (.int 1))
        (.invoke (body := parent) (known (by decide)) (known (by decide)) rfl (indexArg _) (rest _ rfl rfl)))

private def caller : State := { bindings := fun _ => some (.scalar (.int 99)), iterators := [123] }

example (ending : End) {resolved : ResolvedModule} (checked : resolve (commands ending) = .ok resolved) :
    ∃ out publication,
      Wrapper.ReachedPrefix (Bindings.WithDefaults.Step resolved (names (commands ending))) 0
        (enter resolved.source caller) (commands ending) out ∧
      Leaf.Finishes (names (commands ending)) caller out publication ∧
      Initializes (commands ending) (fun _ => none) caller #[] (.ok publication) ∧
      runModule (commands ending) (fun _ => none) caller = .ok publication :=
  Bindings.WithDefaults.checked_module (admitted ending) checked (fun _ => none) caller

private def captureAddresses (heap : Array Cell) (closure seed : Lists.Value) : Option (List Nat) := do
  let .function address := closure | none
  let ⟨.function child, true⟩ ← heap[address]? | none
  let [first, second] := child.captures | none
  let [(early, .list allocated), (saved, savedValue), (setting, .scalar (.int 1)),
    (shadow, .scalar (.int 0)), (last, .list later)] := child.defaults | none
  if child.declaration == 0 && early == fileSlot "early" && saved == fileSlot "saved" && savedValue == seed &&
      setting == fileSlot "setting_at_def" && shadow == fileSlot "shadow_at_def" && last == fileSlot "last" && heap[allocated]? == some ⟨.list [.scalar (.int 14)], true⟩ &&
      heap[later]? == some ⟨.list [.scalar (.int 73)], true⟩ &&
      first.binding == fileSlot "offset" && first.localCell &&
      second.binding == fileSlot "seed" && second.localCell &&
      heap[first.address]? == some ⟨.binding (some (.scalar (.int 1))), true⟩ &&
      heap[second.address]? == some ⟨.binding (some (.scalar (.int 0))), true⟩ then
    some [first.address, second.address]
  else none

#guard
  match resolve (commands .success), runModule (commands .success) (fun _ => none) caller with
  | .ok resolved, .ok (.ok published final) =>
    let initial := enter resolved.source caller
    let entered := initial.heap.size
    let get name := published.exports.lookup name
    match get "a", get "b", get "seed_a", get "seed_b", get "make", initial.slots (globalSlot "table"),
        initial.slots (globalSlot "setting") with
    | some a, some b, some (.list seedA), some (.list seedB), some (.function make), some (.owned table), some (.owned setting) =>
      (resolved.program[1]?.map Functions.Declaration.locals) ==
        some [fileSlot "earlier", fileSlot "shadow", fileSlot "offset", fileSlot "inner", fileSlot "unused"] &&
      get "shadow" == some (.scalar (.int 99)) && get "table" == get "outer_a" && get "make_alias" == get "make" &&
      (match final.heap[make]? with
        | some ⟨.function wrapper, true⟩ => wrapper.captures == [⟨globalSlot "table", table, false⟩, ⟨globalSlot "setting", setting, false⟩]
        | _ => false) &&
      get "alias" == some a && a != b &&
      get "first" == some (.scalar (.int 5)) && get "second" == some (.scalar (.int 8)) &&
      get "override" == some (.scalar (.int 9)) && get "again" == some (.scalar (.int 5)) &&
      final.heap[seedA]? == some ⟨.list [.scalar (.int 3), .scalar (.int 5)], true⟩ &&
      final.heap[seedB]? == some ⟨.list [.scalar (.int 6), .scalar (.int 8)], true⟩ &&
      final.heap[entered + 3]? == some ⟨.list [.list seedB], true⟩ &&
      get "touched" == some (.scalar (.int 0)) &&
      captureAddresses final.heap a (.list seedA) == some [entered + 7, entered + 4] &&
      captureAddresses final.heap b (.list seedB) == some [entered + 20, entered + 17] &&
      final.bindingValue (globalSlot "first") == .ok (.scalar (.int 99)) && final.iterators == [123]
    | _, _, _, _, _, _, _ => false
  | _, _ => false

private def errorControl (ending : End) (expected : Lists.Error) (reachedDefault : Bool) : Bool :=
  match resolve (commands ending), runModule (commands ending) (fun _ => none) caller with
  | .ok resolved, .ok (.error (.runtime error) final) =>
    let initial := enter resolved.source caller
    let get (name : String) : Option Lists.Contents :=
      match initial.slots (globalSlot name) with
      | some (.owned address) => final.heap[address]?.map Cell.contents
      | _ => none
    let active := initial.heap.size + 4
    error == expected && final.heap.size == active + (if reachedDefault then 8 else 7) &&
    (["a", "b", "make_alias", "edit", "patch", "touched", "alias", "first", "second", "replacement", "override", "again"] : List String).all
      (fun name => get name == some (.binding none)) &&
    get "table" == some (.binding (if expected == .uninitialized (globalSlot "table") then none else some (.list (active - 1)))) &&
    get "setting" == some (.binding
      (if expected == .uninitialized (globalSlot "setting") then none else some (.scalar (.int 1)))) &&
    final.heap[active]? == some ⟨.binding (some (.scalar (.int (firstIndex ending)))), false⟩ &&
    final.heap[active - 3]? == some ⟨.list [.scalar (.int 3), .scalar (.int 5)], false⟩ &&
    final.heap[active + 1]? == some ⟨.binding (some (.list (active + 6))), false⟩ &&
    final.heap[active + 2]? == some ⟨.binding (some (.scalar (.int (firstIndex ending)))), false⟩ &&
    final.heap[active + 3]? == some ⟨.binding (if reachedDefault then some (.list (active - 3)) else none), false⟩ &&
    final.heap[active + 4]? == some ⟨.binding none, false⟩ &&
    final.heap[active + 5]? == some ⟨.binding none, false⟩ &&
    final.heap[active + 6]? == some ⟨.list [.scalar (.int 13)], false⟩ &&
    final.heap[active + 7]? == (if reachedDefault then some ⟨.list [.scalar (.int 14)], false⟩ else none) &&
    final.bindingValue (globalSlot "table") == .ok (.scalar (.int 99)) && final.iterators == [123]
  | _, _ => false

#guard errorControl .moduleError (.uninitialized (globalSlot "table")) false
#guard errorControl .prefixError (.indexRange 1 1) false
#guard errorControl .defaultError (.uninitialized (fileSlot "unused")) true
#guard errorControl .moduleDefaultError (.uninitialized (globalSlot "setting")) true

#guard
  match resolve (commands .success ++ [.assign "table" starlark%[0]]) with
  | .error (.validation (.bindingCollision "table")) => true
  | _ => false

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped

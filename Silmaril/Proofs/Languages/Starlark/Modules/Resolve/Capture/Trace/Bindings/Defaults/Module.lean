module

public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.Defaults.Escape
public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.Defaults.Body
public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.Defaults.Scoped
public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Leaf.Publication

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.WithDefaults

open Silmaril.Languages.Starlark.Modules (enter Catalog)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Block (ModuleBinders)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.WithDefaults
open Silmaril.Languages.Starlark.Functions (Program)
open Silmaril.Languages.Starlark.Lists (State)

private theorem cons_legal {name : String} {names : List String} (head : name.toList.head? ≠ some '$')
    (tail : ∀ item ∈ names, item.toList.head? ≠ some '$') :
    ∀ item ∈ name :: names, item.toList.head? ≠ some '$' := by
  intro item present
  rcases List.mem_cons.mp present with rfl | later
  · exact head
  · exact tail _ later

private theorem static {globals : List String} {entries : Entries} {commands : List Command}
    (profile : Schedule globals entries commands) :
    ModuleBinders commands (names commands) ∧ RootCall.Segment globals commands ∧
      (∀ name ∈ names commands, name.toList.head? ≠ some '$') := by
  induction profile with
  | nil => exact ⟨.nil, .nil, by simp [names]⟩
  | @define _ body _ visible admitted _ ih =>
    cases body with
    | required chain =>
      exact ⟨.cons (.define _ _ _) ih.1, .define _ (fun program =>
        definitions_accept admitted program [] (fun _ => Iff.rfl)) ih.2.1, cons_legal visible.2 ih.2.2⟩
    | defaulted definition =>
      obtain ⟨codes, emission, _, _⟩ := Defaults.definition_emission admitted
      exact ⟨.cons (.define _ _ _) ih.1, .emit ⟨definition.emitted codes, emission⟩ ih.2.1,
        cons_legal visible.2 ih.2.2⟩
    | escaping wrapper =>
      exact ⟨.cons (.define _ _ _) ih.1, .emitPair ⟨wrapper.child.emitted wrapper.codes,
        (fun id => (wrapper.frame id).declaration), Defaults.Escape.emission wrapper admitted globals⟩ ih.2.1,
        cons_legal visible.2 ih.2.2⟩
    | sequenced definition =>
      obtain ⟨plan, codes, emitted, _, _⟩ := Defaults.Body.emission admitted
      exact ⟨.cons (.define _ _ _) ih.1, .emit ⟨plan.declaration codes, emitted⟩ ih.2.1,
        cons_legal visible.2 ih.2.2⟩
    | nestedBody spec =>
      obtain ⟨plan⟩ := admitted.plan
      exact ⟨.cons (.define _ _ _) ih.1,
        .emitPair ⟨plan.childDeclaration, (fun id => (plan.frame id).declaration),
          Defaults.Escape.Scoped.emission spec globals admitted.names plan⟩ ih.2.1,
        cons_legal visible.2 ih.2.2⟩
  | setup visible _ _ ih | copy _ visible _ _ ih | invoke _ visible _ _ _ ih =>
    exact ⟨.cons (.assign _ _) ih.1, .assign _ _ ih.2.1, cons_legal visible.2 ih.2.2⟩

private theorem schedule_trace {globals : List String} {entries : Entries} {commands : List Command}
    (profile : Schedule globals entries commands)
    (globalsLegal : ∀ name ∈ globals, name.toList.head? ≠ some '$')
    (before : List Command) {linked : Program} {resolved : ResolvedModule}
    (declared : ModuleBinders (before ++ commands) globals)
    (checked : resolve (before ++ commands) linked = .ok resolved)
    (state : State) (layout : ModuleSlots globals state)
    (pool : LiveBindings globals resolved.program entries state) :
    ∃ out, Wrapper.ReachedPrefix (Step resolved globals) before.length state commands out := by
  induction profile generalizing before state with
  | nil => exact ⟨_, .nil⟩
  | @define entries body rest visible admitted tail ih =>
    apply Bindings.advanceWith (steps := Step resolved globals)
      (invariant := fun next => ModuleSlots globals next ∧ LiveBindings globals resolved.program (entries.write body.name (some body)) next)
      declared checked ?_ (fun earlier d c next pair => ih earlier d c next pair.1 pair.2)
    have suffix := (static tail).2.1
    cases body with
    | required chain =>
      obtain ⟨next, step, ⟨_, live⟩, written⟩ :=
        Bindings.define_step declared checked admitted suffix globalsLegal visible layout (required_pool pool)
      refine ⟨_, .ordinary step, ?_⟩
      intro final success
      cases success
      apply update layout pool written
      intro code same
      cases same
      exact live chain.name chain (by simp [Trace.Bindings.Environment.write])
    | defaulted definition =>
      obtain ⟨out, step, progress⟩ := define_saved declared checked admitted suffix visible layout
      refine ⟨out, step, ?_⟩
      intro next success
      obtain ⟨written, live⟩ := progress next success
      exact update layout pool written (fun code same => by cases same; exact live)
    | escaping wrapper =>
      obtain ⟨next, step, written, live⟩ := define_wrapper declared checked admitted suffix visible layout
      exact ⟨_, step, fun _ success => by
        cases success
        exact update layout pool written (fun _ same => by cases same; exact live)⟩
    | sequenced definition =>
      obtain ⟨out, step, progress⟩ := define_body declared checked admitted suffix visible layout
      exact ⟨out, step, fun next success => by
        obtain ⟨written, live⟩ := progress next success
        exact update layout pool written (fun _ same => by cases same; exact live)⟩
    | nestedBody spec =>
      obtain ⟨next, step, written, live⟩ := define_scoped declared checked admitted suffix visible layout
      exact ⟨_, step, fun _ success => by
        cases success
        exact update layout pool written (fun _ same => by cases same; exact live)⟩
  | @setup entries name source rest visible allowed tail ih =>
    obtain ⟨out, step, progress⟩ := setup_step declared checked allowed state
    apply Bindings.advanceWith (steps := Step resolved globals)
      (invariant := fun next => ModuleSlots globals next ∧ LiveBindings globals resolved.program (entries.write name none) next)
      declared checked ⟨out, .ordinary step, ?_⟩
      (fun earlier d c next pair => ih earlier d c next pair.1 pair.2)
    intro next success
    obtain ⟨value, middle, rfl, added⟩ := progress next success
    have kept : Bindings.Preserves state middle := by
      rcases added with rfl | ⟨cell, rfl⟩
      · exact Bindings.Preserves.refl _
      · exact Bindings.Preserves.push _ cell
    exact update layout pool (.commit _ _ kept) (fun _ impossible => nomatch impossible)
  | @copy entries source destination body rest src dst selected tail ih =>
    apply Bindings.advanceWith (steps := Step resolved globals)
      (invariant := fun next => ModuleSlots globals next ∧ LiveBindings globals resolved.program (entries.write destination (some body)) next)
      declared checked ?_ (fun earlier d c next pair => ih earlier d c next pair.1 pair.2)
    cases body with
    | required chain =>
      obtain ⟨next, step, ⟨_, live⟩, written⟩ :=
        Bindings.alias_step declared checked src dst (required_at selected) layout (required_pool pool)
      refine ⟨_, .ordinary step, ?_⟩
      intro final success
      cases success
      apply update layout pool written
      intro code same
      cases same
      exact live destination chain (by simp [Trace.Bindings.Environment.write])
    | defaulted definition =>
      obtain ⟨_, ⟨saved⟩⟩ := pool source (.defaulted definition) selected
      obtain ⟨next, step, written, live⟩ := alias_saved declared checked src dst saved layout
      exact ⟨_, step, fun final success => by
        cases success
        exact update layout pool written (fun _ same => by cases same; exact live)⟩
    | escaping wrapper =>
      obtain ⟨_, ⟨root⟩⟩ := pool source (.escaping wrapper) selected
      obtain ⟨next, step, written, live⟩ := alias_wrapper declared checked src dst root layout
      exact ⟨_, step, fun _ success => by
        cases success
        exact update layout pool written (fun _ same => by cases same; exact live)⟩
    | sequenced definition =>
      obtain ⟨_, ⟨saved⟩⟩ := pool source (.sequenced definition) selected
      obtain ⟨next, step, written, live⟩ := alias_body declared checked src dst saved layout
      exact ⟨_, step, fun _ success => by
        cases success
        exact update layout pool written (fun _ same => by cases same; exact live)⟩
    | nestedBody spec =>
      obtain ⟨_, ⟨root⟩⟩ := pool source (.nestedBody spec) selected
      obtain ⟨next, step, written, live⟩ := alias_scoped declared checked src dst root layout
      exact ⟨_, step, fun _ success => by
        cases success
        exact update layout pool written (fun _ same => by cases same; exact live)⟩
  | @invoke entries callee destination body arguments rest src dst selected args tail ih =>
    apply Bindings.advanceWith (steps := Step resolved globals)
      (invariant := fun next => ModuleSlots globals next ∧ LiveBindings globals resolved.program (entries.write destination body.returned) next)
      declared checked ?_ (fun earlier d c next pair => ih earlier d c next pair.1 pair.2)
    cases body with
    | required chain =>
      obtain ⟨out, step, progress⟩ :=
        Bindings.invoke_step declared checked src dst args (required_at selected) layout (required_pool pool)
      refine ⟨out, .ordinary step, ?_⟩
      intro next success
      obtain ⟨_, live, written⟩ := progress next success
      apply update layout pool written
      intro code same
      cases chain with
      | mixed => cases same
      | wrapper name parameters child =>
        cases same
        exact live destination child (by simp [Bindings.callResult, Trace.Bindings.Environment.write])
    | defaulted definition =>
      obtain ⟨_, ⟨saved⟩⟩ := pool callee (.defaulted definition) selected
      obtain ⟨out, step, progress⟩ := call_step declared checked src args saved
      exact ⟨out, step, fun next success =>
        update layout pool (progress next success) (fun _ impossible => nomatch impossible)⟩
    | escaping wrapper =>
      obtain ⟨_, ⟨root⟩⟩ := pool callee (.escaping wrapper) selected
      obtain ⟨out, step, progress⟩ := call_wrapper declared checked src dst args root layout
      exact ⟨out, step, fun next success => by
        obtain ⟨written, live⟩ := progress next success
        exact update layout pool written (fun _ same => by cases same; exact live)⟩
    | sequenced definition =>
      obtain ⟨_, ⟨saved⟩⟩ := pool callee (.sequenced definition) selected
      obtain ⟨out, step, progress⟩ := call_body declared checked src args saved
      exact ⟨out, step, fun next success =>
        update layout pool (progress next success) (fun _ impossible => nomatch impossible)⟩
    | nestedBody spec =>
      obtain ⟨_, ⟨root⟩⟩ := pool callee (.nestedBody spec) selected
      obtain ⟨out, step, progress⟩ := call_scoped declared checked src dst args root layout
      exact ⟨out, step, fun next success => by
        obtain ⟨written, live⟩ := progress next success
        exact update layout pool written (fun _ same => by cases same; exact live)⟩

theorem checked_trace {commands : List Command} (profile : Profile commands)
    {linked : Program} {resolved : ResolvedModule} (checked : resolve commands linked = .ok resolved)
    (caller : State) :
    ModuleBinders commands (names commands) ∧
      ∃ out, Wrapper.ReachedPrefix (Step resolved (names commands)) 0 (enter resolved.source caller) commands out := by
  obtain ⟨declared, _, legal⟩ := static profile
  exact ⟨declared, schedule_trace profile legal [] declared checked (enter resolved.source caller)
    (entered_slots declared checked caller) (fun _ _ impossible => nomatch impossible)⟩

theorem checked_module {commands : List Command} (profile : Profile commands)
    {linked : Program} {resolved : ResolvedModule} (checked : resolve commands linked = .ok resolved)
    (host : Catalog) (caller : State) :
    ∃ out publication,
      Wrapper.ReachedPrefix (Step resolved (names commands)) 0 (enter resolved.source caller) commands out ∧
      Leaf.Finishes (names commands) caller out publication ∧
      Initializes commands host caller linked (.ok publication) ∧ runModule commands host caller linked = .ok publication := by
  obtain ⟨declared, out, reached⟩ := checked_trace profile checked caller
  obtain ⟨observed, finishes⟩ := publication_total _ caller out
  exact ⟨out, observed, reached, finishes,
    Leaf.module_observes declared checked host caller (fun _ _ _ _ => step_sound checked host) reached finishes⟩

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.WithDefaults

module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.Defs
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named

open Silmaril.Languages.Starlark (Binding)
open Silmaril.Languages.Starlark.Modules.Resolve.Assignment (LexicalBlock)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Lists (State Outcome Value Error Entry Cell Contents dictEntries projectCell getCell
  allocateDict insertDisplayEntry addDisplayEntry editCell fromExcept)
open Silmaril.Languages.Starlark.Lists.Iteration (finishState)

theorem keeps_push (state : State) (cell : Cell) :
    Body.Keeps state.heap.size state {state with heap := state.heap.push cell} := by
  refine ⟨by simp, fun address _ below stored => ?_⟩
  simp [Array.getElem?_push, Nat.ne_of_lt below, stored]

private theorem trim_kept {floor : Nat} {first last : State}
    (kept : Body.Keeps first.heap.size first last) : Body.Keeps floor first last :=
  ⟨kept.1, fun address cell _ stored => kept.2 address cell (Array.getElem?_eq_some_iff.mp stored).choose stored⟩

theorem keeps_after {first middle final : State}
    (earlier : Body.Keeps first.heap.size first middle) (later : Body.Keeps middle.heap.size middle final) :
    Body.Keeps first.heap.size first final :=
  Body.keeps_trans earlier (trim_kept later)

private theorem insertion_keeps (state : State) (address : Nat) (key value : Value) :
    Body.Keeps address state (finishState (insertDisplayEntry (.dict address) key value state)) := by
  have same : Body.Keeps address state state := ⟨rfl, fun _ _ _ h => h⟩
  have mutation (cell : Cell) :
      Body.Keeps address state {state with heap := state.heap.setIfInBounds address cell} := by
    refine ⟨rfl, fun other _ below found => ?_⟩
    simpa only [Array.getElem?_setIfInBounds_ne (Nat.ne_of_gt below)] using found
  cases read : state.heap[address]? with
  | none =>
    simpa [insertDisplayEntry, dictEntries, projectCell, getCell, bind, EStateM.bind, read, finishState] using same
  | some cell =>
    cases kind : cell.contents with
    | dict entries =>
      simp only [insertDisplayEntry, dictEntries, projectCell, getCell, bind, EStateM.bind, read, kind, pure, EStateM.pure]
      have stable : finishState (addDisplayEntry entries key value state) = state := by
        simp only [addDisplayEntry]
        split
        · rfl
        · split <;> rfl
      cases inserted : addDisplayEntry entries key value state with
      | error error failed =>
        have unchanged : failed = state := by simpa only [inserted, finishState] using stable
        simpa only [unchanged, finishState] using same
      | ok updated reached =>
        have unchanged : reached = state := by simpa only [inserted, finishState] using stable
        subst reached
        simp only [editCell, getCell, bind, EStateM.bind, read, kind]
        split
        · exact same
        · split
          · exact same
          · exact mutation _
    | _ =>
      simp only [insertDisplayEntry, dictEntries, projectCell, getCell, bind, EStateM.bind, read, kind]
      exact same

private abbrev Evaluates (program : Program) (available : List DeclarationId) :=
  Lowering.EvaluatesWith program available (Lowering.coreClosureRuns program available) (fun _ => True)

private theorem display_operand_total (program : Program) (available : List DeclarationId)
    {block : LexicalBlock} {source : Lowering.Resolve.SourceExpr} {code : Lowering.Expr} {reads : List Binding}
    (related : DisplayOperand block source code reads) (state : State) :
    ∃ out, EvaluatesDisplayOperand block state source code out ∧ Evaluates program available state code out ∧
      Body.Keeps state.heap.size state (finishState out) := by
  cases related with
  | plain operand =>
    obtain ⟨out, ran, kept⟩ := Body.operand_total operand state
    exact ⟨out, .plain ran, Body.evaluates_with _ _ _ ran, kept⟩
  | string text => exact ⟨_, .string state text, .atom trivial .string, ⟨rfl, fun _ _ _ h => h⟩⟩

private theorem entries_total (program : Program) (available : List DeclarationId)
    {block : LexicalBlock} {source codes reads}
    (related : DisplayEntries block source codes reads) (address : Nat) (state : State) :
    ∃ out, EvaluatesEntries block address state source codes out ∧
      Lowering.EvaluatesEntriesWith program available (Lowering.coreClosureRuns program available)
        (fun _ => True) (.dict address) state codes out ∧
      Body.Keeps address state (finishState out) := by
  induction related generalizing state with
  | empty => exact ⟨_, .empty _, .noEntries, ⟨rfl, fun _ _ _ h => h⟩⟩
  | entry key value _ ih =>
    obtain ⟨keyOut, readKey, keyExec, keptKey⟩ := display_operand_total program available key state
    cases keyOut with
    | error error reached => exact ⟨_, .keyError readKey, .keyError keyExec, trim_kept keptKey⟩
    | ok k keyed =>
      obtain ⟨valueOut, readValue, valueExec, keptValue⟩ := display_operand_total program available value keyed
      have kept := trim_kept (floor := address) (keeps_after keptKey keptValue)
      cases valueOut with
      | error error reached => exact ⟨_, .valueError readKey readValue, .valueError keyExec valueExec, kept⟩
      | ok v valued =>
        have retained := insertion_keeps valued address k v
        cases inserted : insertDisplayEntry (.dict address) k v valued with
        | error error reached =>
          have stable : Body.Keeps address valued reached := by simpa only [inserted, finishState] using retained
          exact ⟨_, .insertionError readKey readValue inserted, .insertionError keyExec valueExec inserted,
            Body.keeps_trans kept stable⟩
        | ok marker reached =>
          cases marker
          have stable : Body.Keeps address valued reached := by simpa only [inserted, finishState] using retained
          obtain ⟨out, rest, native, last⟩ := ih reached
          exact ⟨out, .entry readKey readValue inserted rest, .entry keyExec valueExec inserted native,
            Body.keeps_trans kept (Body.keeps_trans stable last)⟩

theorem mapping_total (program : Program) (available : List DeclarationId)
    {block : LexicalBlock} (mapping : Option (Mapping block)) (state : State) :
    ∃ out, EvaluatesMapping block mapping state out ∧
      Lowering.EvaluatesManyWith program available (Lowering.coreClosureRuns program available) (fun _ => True)
        state (mapping.map Mapping.code).toList
        (out.resume fun address reached => .ok (address.map Value.dict).toList reached) ∧
      Body.Keeps state.heap.size state (finishState out) ∧
      (∀ address reached, out = .ok address reached → address.isSome = mapping.isSome) := by
  cases mapping with
  | none => exact ⟨_, .absent _, .empty, ⟨rfl, fun _ _ _ h => h⟩, fun _ _ h => by cases h; rfl⟩
  | some mapping =>
    let allocated := {state with heap := state.heap.push ⟨.dict [], false⟩}
    have allocation : allocateDict [] state = .ok (.dict state.heap.size) allocated := rfl
    obtain ⟨out, source, native, kept⟩ := entries_total program available mapping.related state.heap.size allocated
    have keptAll := Body.keeps_trans (keeps_push state ⟨.dict [], false⟩) kept
    cases out with
    | error error reached =>
      exact ⟨_, .dict allocation source, .headError (.dict allocation native), keptAll, fun _ _ h => nomatch h⟩
    | ok marker reached =>
      cases marker
      exact ⟨_, .dict allocation source, .cons (.dict allocation native) .empty, keptAll,
        fun _ _ h => by cases h; rfl⟩

private theorem keyword_entries_total (entries : List Entry) : ∃ result, KeywordEntries entries result := by
  induction entries with
  | nil => exact ⟨_, .empty⟩
  | cons entry rest ih =>
    obtain ⟨key, keyCode, value⟩ := entry
    cases key with
    | string text => obtain ⟨_, ran⟩ := ih; exact ⟨_, .string ran⟩
    | _ => exact ⟨_, .nonString (by intro _ h; cases h)⟩

theorem keyword_entries_exact {entries : List Entry} {result : Except Error Keywords}
    (source : KeywordEntries entries result) :
    (entries.mapM fun entry => match entry.key with
      | .string name => .ok (name, entry.value)
      | key => .error (.keywordMustBeString key)) = result := by
  induction source with
  | empty => rfl
  | @string _ _ _ _ result _ ih =>
    simp only [List.mapM_cons, bind, Except.bind, ih]
    cases result <;> rfl
  | @nonString key _ _ _ unsupported =>
    cases key <;> solve | exact (unsupported _ rfl).elim | rfl

theorem project_state {α : Type} (state : State) (address : Nat) (project : Contents → Option α) :
    finishState (projectCell address project state) = state := by
  cases stored : state.heap[address]? with
  | none => simp [projectCell, getCell, bind, EStateM.bind, stored, finishState]
  | some cell =>
    cases kind : project cell.contents <;>
      simp only [projectCell, getCell, bind, EStateM.bind, stored, kind] <;> rfl

theorem expand_mapping_total (state : State) (address : Option Nat) :
    ∃ out, ExpandsMapping state address out ∧ expandStarStar (address.map Value.dict) state = out ∧
      finishState out = state := by
  cases address with
  | none => exact ⟨_, .absent, rfl, rfl⟩
  | some address =>
    cases read : dictEntries address state with
    | error error reached =>
      have same : reached = state := by
        have unchanged : finishState (dictEntries address state) = state := project_state state address _
        simpa only [read, finishState] using unchanged
      subst reached
      exact ⟨_, .readError read, by simp [expandStarStar, bind, EStateM.bind, read], rfl⟩
    | ok entries reached =>
      have same : reached = state := by
        have unchanged : finishState (dictEntries address state) = state := project_state state address _
        simpa only [read, finishState] using unchanged
      subst reached
      obtain ⟨result, ran⟩ := keyword_entries_total entries
      refine ⟨fromExcept result state, .dict read ran, ?_, ?_⟩
      · simp only [expandStarStar, Option.map_some, bind, EStateM.bind, read]
        exact congrArg (fun values : Except Error Keywords => fromExcept values state) (keyword_entries_exact ran)
      · cases result <;> rfl

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named

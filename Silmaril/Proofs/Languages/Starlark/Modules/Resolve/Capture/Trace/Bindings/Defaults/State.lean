module

public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.Defaults.Call
public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.Module

import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.WithDefaults

open Silmaril.Languages.Starlark.Modules (globalSlot)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Block (ModuleBinders)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.WithDefaults
open Silmaril.Languages.Starlark.Functions (Program FreeName)
open Silmaril.Languages.Starlark.Lists (Cell State)

@[expose] def requiredEntries (entries : Entries) : Trace.Bindings.Environment := fun name =>
  match entries name with
  | some (.required chain) => some chain
  | _ => none

theorem required_pool {globals : List String} {program : Program} {entries : Entries} {state : State}
    (pool : LiveBindings globals program entries state) :
    Trace.Bindings.LiveBindings globals program (requiredEntries entries) state := by
  intro name chain tracked
  unfold requiredEntries at tracked
  cases slot : entries name with
  | none => simp [slot] at tracked
  | some code =>
    cases code with
    | defaulted | escaping | sequenced | nestedBody => simp [slot] at tracked
    | required actual =>
      simp [slot] at tracked
      subst chain
      exact pool name _ slot

theorem required_write (entries : Entries) (name : String) (value : Option Callable) :
    requiredEntries (entries.write name value) = (requiredEntries entries).write name
      (match value with | some (.required chain) => some chain | _ => none) := by
  funext other
  by_cases same : other = name <;> simp [requiredEntries, Entries.write, Trace.Bindings.Environment.write, same]

theorem required_at {entries : Entries} {name : String} {chain : Forwarding.Chain}
    (atName : entries name = some (.required chain)) : requiredEntries entries name = some chain := by
  simp [requiredEntries, atName]

theorem commit_captures {state middle : State} {free : List FreeName}
    {captures : List Silmaril.Languages.Starlark.Lists.Capture}
    (kept : Bindings.Preserves state middle) (destination : String) (value : Silmaril.Languages.Starlark.Lists.Value)
    (installed : Installs state free captures) (cells : Defaults.Body.CaptureCells state captures) :
    Installs (middle.write (globalSlot destination) value) free captures ∧
      Defaults.Body.CaptureCells (middle.write (globalSlot destination) value) captures :=
  ⟨Silmaril.Languages.Starlark.Modules.Resolve.Capture.installs_in_same_slots ((slots_write _ _ _).trans kept.slots) installed,
    Defaults.Body.capture_cells_written _ _ _ (Defaults.Body.capture_cells_preserved kept cells)⟩

theorem keep_live {globals : List String} {program : Program} {state middle : State}
    {name destination : String} {code : Callable} (value : Silmaril.Languages.Starlark.Lists.Value)
    (layout : ModuleSlots globals state) (unchanged : Bindings.Preserves state middle)
    (live : LiveBinding globals program state name code) (other : destination ≠ name) :
    LiveBinding globals program (middle.write (globalSlot destination) value) name code := by
  have distinct := (unchanged.layout layout).distinct
  cases code with
  | required chain =>
    obtain ⟨member, seed, frame, rest, address, captures, linked, selected, installed, legal⟩ := live
    have retained := unchanged.live layout member selected
    exact ⟨member, seed, frame, rest, address, captures, linked,
      (RootCall.write_keeps_live _ _ _ _ distinct retained other).2, installed, legal⟩
  | defaulted definition =>
    obtain ⟨member, ⟨saved⟩⟩ := live
    have retained := unchanged.live layout member saved.live
    exact ⟨member, ⟨{ saved with live := (RootCall.write_keeps_live _ _ _ _ distinct retained other).2 }⟩⟩
  | escaping wrapper =>
    obtain ⟨member, ⟨root⟩⟩ := live
    have retained := unchanged.live layout member root.live
    exact ⟨member, ⟨{ root with live := (RootCall.write_keeps_live _ _ _ _ distinct retained other).2 }⟩⟩
  | sequenced definition =>
    obtain ⟨member, ⟨saved⟩⟩ := live
    have retained := unchanged.live layout member saved.live
    exact ⟨member, ⟨{ saved with
      cells := Defaults.Body.capture_cells_written _ _ _ (Defaults.Body.capture_cells_preserved unchanged saved.cells)
      live := (RootCall.write_keeps_live _ _ _ _ distinct retained other).2 }⟩⟩
  | nestedBody spec =>
    obtain ⟨member, ⟨root⟩⟩ := live
    have retained := unchanged.live layout member root.live
    obtain ⟨installed, cells⟩ := commit_captures unchanged destination value root.installed root.cells
    exact ⟨member, ⟨{ root with
      installed := installed
      cells := cells
      live := (RootCall.write_keeps_live _ _ _ _ distinct retained other).2 }⟩⟩

theorem update {globals : List String} {program : Program} {entries : Entries} {state next : State}
    {destination : String} {shape : Option Callable}
    (layout : ModuleSlots globals state) (pool : LiveBindings globals program entries state)
    (writes : Bindings.Writes state destination next)
    (new : ∀ code, shape = some code → LiveBinding globals program next destination code) :
    ModuleSlots globals next ∧ LiveBindings globals program (entries.write destination shape) next := by
  cases writes with
  | commit middle value kept =>
    refine ⟨written_slots (kept.layout layout) _ _, ?_⟩
    intro name code tracked
    by_cases same : name = destination
    · subst name
      exact new code (by simpa [Entries.write] using tracked)
    · have before : entries name = some code := by simpa [Entries.write, same] using tracked
      exact keep_live value layout kept (pool name code before) (Ne.symm same)

theorem commit_cell {globals : List String} {state : State} {destination : String}
    (member : destination ∈ globals) (layout : ModuleSlots globals state)
    (address id : Nat) (captures : List Silmaril.Languages.Starlark.Lists.Capture)
    (defaults : List (Silmaril.Languages.Starlark.Binding × Silmaril.Languages.Starlark.Lists.Value))
    (cell : state.heap[address]? = some ⟨.function ⟨id, captures, defaults⟩, false⟩) :
    RootCall.Live (state.write (globalSlot destination) (.function address)) destination address id captures false defaults := by
  obtain ⟨slot, _, _, owned, stored⟩ := layout.usable destination member
  exact ⟨⟨slot, by rw [slots_write]; exact owned⟩, writes_binding _ _ _ _ owned stored,
    write_keeps_function _ _ _ _ _ _ cell⟩

theorem retarget {globals : List String} {program : Program} {state : State} {destination : String}
    {definition : Defaults.Definition} (member : destination ∈ globals) (layout : ModuleSlots globals state)
    (id : Nat) (codes : List Silmaril.Languages.Starlark.Functions.Lowering.Expr)
    (address : Nat) (values : List Silmaril.Languages.Starlark.Lists.Value)
    (codeLength : codes.length = definition.parameters.optional.length)
    (valueLength : values.length = definition.parameters.optional.length)
    (found : program[id]? = some (definition.emitted codes))
    (cell : state.heap[address]? = some ⟨.function ⟨id, [],
      (definition.parameters.optional.map (Silmaril.Languages.Starlark.Modules.fileSlot ∘ Prod.fst)).zip values⟩, false⟩) :
    LiveBinding globals program (state.write (globalSlot destination) (.function address)) destination (.defaulted definition) := by
  exact ⟨member, ⟨⟨id, codes, address, values, codeLength, valueLength, found,
    commit_cell member layout address id [] _ cell⟩⟩⟩

theorem alias_saved {before rest : List Command} {globals : List String} {source destination : String}
    {linked : Program} {resolved : ResolvedModule}
    (declared : ModuleBinders (before ++ .assign destination (.scalar (.read source)) :: rest) globals)
    (checked : resolve (before ++ .assign destination (.scalar (.read source)) :: rest) linked = .ok resolved)
    (sourceKnown : Visible globals source) (destinationKnown : Visible globals destination)
    {state : State} {definition : Defaults.Definition} (saved : Saved resolved.program state source definition)
    (layout : ModuleSlots globals state) :
    ∃ next, Step resolved globals before.length state (.assign destination (.scalar (.read source))) (.ok () next) ∧
      Bindings.Writes state destination next ∧ LiveBinding globals resolved.program next destination (.defaulted definition) := by
  have related := global_operand sourceKnown
  obtain ⟨reads, tracked⟩ := RootCall.resolves_operand related
  have site := RootCall.checked_assign_site before rest destination _ _ reads globals linked resolved declared checked tracked
  have evaluated : RootCall.Evaluates state (.scalar (.read source)) (.ok (.function saved.address) state) := by
    simpa [State.read, saved.live.binding] using RootCall.Evaluates.name (state := state) source
  exact ⟨_, .ordinary (.setup site (.atom related evaluated)), .commit state _ (Bindings.Preserves.refl _),
    retarget destinationKnown.1 layout saved.id saved.codes saved.address saved.values saved.codeLength
      saved.valueLength saved.found saved.live.cell⟩

theorem define_saved {before after : List Command} {definition : Defaults.Definition} {globals : List String}
    {linked : Program} {resolved : ResolvedModule}
    (declared : ModuleBinders (before ++ definition.command :: after) globals)
    (checked : resolve (before ++ definition.command :: after) linked = .ok resolved)
    (admitted : Defaults.Admitted globals definition) (suffix : RootCall.Segment globals after)
    (known : Visible globals definition.name) {state : State} (layout : ModuleSlots globals state) :
    ∃ out, Step resolved globals before.length state definition.command out ∧
      (∀ next, out = .ok () next →
        Bindings.Writes state definition.name next ∧ LiveBinding globals resolved.program next definition.name (.defaulted definition)) := by
  obtain ⟨codes, emits, length, evaluates⟩ := Defaults.definition_emission admitted
  obtain ⟨id, site, found⟩ := RootCall.checked_single_emission before after _ definition.name globals linked resolved
    (definition.emitted codes) declared checked suffix emits
  obtain ⟨out, ran, kept⟩ := evaluates state
  cases out with
  | error error final =>
    exact ⟨.error (.runtime error) final, .definition (.define site found length (.failed ran)),
      fun _ impossible => nomatch impossible⟩
  | ok values final =>
    let stored := (definition.parameters.optional.map (Silmaril.Languages.Starlark.Modules.fileSlot ∘ Prod.fst)).zip values
    let cell : Cell := ⟨.function ⟨id, [], stored⟩, false⟩
    let middle : State := { final with heap := final.heap.push cell }
    have preserved : Bindings.Preserves state middle := (kept _ _ rfl).trans (Bindings.Preserves.push final cell)
    have lengthValues : values.length = definition.parameters.optional.length := by
      simpa only [List.length_map] using Defaults.evaluated_length ran
    refine ⟨.ok () (middle.write (globalSlot definition.name) (.function final.heap.size)),
      .definition (.define site found length (.installed ran .nil)), ?_⟩
    intro next same
    cases same
    exact ⟨.commit middle _ preserved, retarget known.1 (preserved.layout layout) id codes final.heap.size
      values length lengthValues found Array.getElem?_push_size⟩

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.WithDefaults

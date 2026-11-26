module

public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped.Site
public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Run
public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Frame
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped

open Silmaril.Languages.Starlark (Binding)
open Silmaril.Languages.Starlark.Modules (fileSlot globalSlot)
open Silmaril.Languages.Starlark.Modules.Resolve (requiredSignature)
open Silmaril.Languages.Starlark.Modules.Resolve.Assignment (LexicalBlock)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Lists.Iteration (Flow)
open Silmaril.Languages.Starlark.Lists (State Cell Slot Value Capture Outcome)

private theorem install_owned (active : State) (free : List FreeName)
    (slots : ∀ entry ∈ free, ∃ name address value frozen,
      entry = ⟨fileSlot name, fileSlot name⟩ ∧ active.slots (fileSlot name) = some (.owned address) ∧
      active.heap[address]? = some ⟨.binding value, frozen⟩) :
    ∃ captures, Installs active free captures ∧ Defaults.Body.CaptureCells active captures := by
  induction free with
  | nil => exact ⟨[], .nil, by simp [Defaults.Body.CaptureCells]⟩
  | cons entry tail ih =>
    obtain ⟨name, address, value, frozen, rfl, owned, stored⟩ := slots entry List.mem_cons_self
    obtain ⟨captures, installed, live⟩ := ih (fun entry member => slots entry (List.mem_cons_of_mem _ member))
    refine ⟨_, .cons (.enclosing owned) installed, ?_⟩
    intro capture member
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨value, frozen, stored⟩
    · exact live capture later

private theorem reached_installs {globals : List String} {spec : Spec} (plan : Plan globals spec)
    {state : State} {floor : Nat} {free : List FreeName} (frame : Defaults.Body.Frame (spec.block globals) free floor state) :
    ∃ captures, Installs state plan.body.free captures ∧ Defaults.Body.CaptureCells state captures := by
  apply install_owned
  intro entry member
  obtain ⟨name, owned, _, rfl⟩ := plan.captured entry member
  obtain ⟨address, value, frozen, _, slot, stored⟩ := frame.owned name owned
  exact ⟨name, address, value, frozen, rfl, slot, stored⟩

private theorem prefix_slots {globals : List String} {spec : Spec} (plan : Plan globals spec) (childId : Nat) :
    (plan.frame childId).declaration.signature.slots ++ (plan.frame childId).declaration.locals =
      (spec.block globals).owned.map fileSlot := by
  simp [Plan.frame, Spec.frame, Spec.block, Spec.enclosing, Spec.parameters, Defaults.Escape.Spec.frame,
    Forwarding.Frame.declaration, requiredSignature, Signature.slots, Signature.named, List.map_map, Function.comp_def]

theorem prefix_frame {globals : List String} {spec : Spec} (plan : Plan globals spec)
    (childId : Nat) (caller : State) (moduleCaptures : List Capture)
    (installed : Installs caller plan.moduleFree moduleCaptures)
    (cells : Defaults.Body.CaptureCells caller moduleCaptures) (assigned : List (Binding × Value)) :
    Defaults.Body.Frame (spec.block globals) plan.moduleFree caller.heap.size
      (activate caller (plan.frame childId).declaration moduleCaptures assigned) := by
  exact Defaults.Body.selected_frame (spec.block globals) (plan.frame childId).declaration (prefix_slots plan childId)
    plan.leadingSelects caller caller moduleCaptures installed cells assigned

theorem prefix_module_read {globals : List String} {spec : Spec} (plan : Plan globals spec)
    (childId : Nat) (caller : State) (moduleCaptures : List Capture)
    (installed : Installs caller plan.moduleFree moduleCaptures) (assigned : List (Binding × Value))
    (name : String) (selected : (⟨globalSlot name, globalSlot name⟩ : FreeName) ∈ plan.moduleFree)
    (address : Nat) (value : Option Value) (frozen : Bool)
    (owned : caller.slots (globalSlot name) = some (.owned address))
    (cell : caller.heap[address]? = some ⟨.binding value, frozen⟩) :
    let active := activate caller (plan.frame childId).declaration moduleCaptures assigned
    active.slots (globalSlot name) = some (.captured address false) ∧
      active.bindingValue (globalSlot name) = caller.bindingValue (globalSlot name) := by
  obtain ⟨capture, found, same, receipt⟩ := Forwarding.find_receipt installed (globalSlot name) selected
  have unowned : globalSlot name ∉ (plan.frame childId).declaration.signature.slots ++ (plan.frame childId).declaration.locals := by
    rw [prefix_slots plan childId]
    simp [globalSlot, fileSlot]
  have slot := Silmaril.Languages.Starlark.Modules.Resolve.Capture.activate_capture caller (plan.frame childId).declaration moduleCaptures capture assigned
    (by simpa only [same] using found) (by simpa only [same] using unowned)
  cases receipt with
  | capturedGlobal forwarded =>
    rw [owned] at forwarded
    cases forwarded
  | ownedGlobal origin =>
    cases Option.some.inj (owned.symm.trans origin)
    have kept := Wrapper.activation_preserves caller (plan.frame childId).declaration moduleCaptures assigned address
      (Array.getElem?_eq_some_iff.mp cell).choose
    exact ⟨slot, by simp only [State.bindingValue, slot, owned, Slot.address, kept]⟩

theorem activate_installs {globals : List String} {spec : Spec} (plan : Plan globals spec)
    (childId : Nat) (caller : State) (moduleCaptures : List Capture) (assigned : List (Binding × Value)) :
    let active := activate caller (plan.frame childId).declaration moduleCaptures assigned
    ∃ captures, Installs active plan.body.free captures ∧ Defaults.Body.CaptureCells active captures :=
  reached_installs plan (Defaults.Escape.wrapper_activation (plan.frame childId) globals caller moduleCaptures assigned)

private theorem assigned_slots {names : List String} {values : List Value} {assigned : List (Binding × Value)}
    (bound : Entry.Binds names values (.ok assigned)) : assigned.map Prod.fst = names.map fileSlot := by
  cases bound with
  | success filled =>
    induction filled with
    | nil => rfl
    | cons _ ih => simp [ih]

theorem local_unbound {spec : Spec} (names : Names spec) (childId : Nat) (caller : State) (moduleCaptures : List Capture)
    {values : List Value} {assigned : List (Binding × Value)} (bound : Entry.Binds spec.parameters values (.ok assigned))
    (name : String) (localName : name ∈ spec.updates.map Prod.fst) :
    let active := activate caller (spec.frame childId).declaration moduleCaptures assigned
    ∃ address, active.slots (fileSlot name) = some (.owned address) ∧
      active.heap[address]? = some ⟨.binding none, false⟩ := by
  apply RootCall.activate_unassigned
  · have localSlot : name ∈ spec.wrapper.locals spec.updates spec.additional (spec.leading.map Prod.fst) :=
      spec.wrapper.local_member spec.updates spec.additional _ name
        (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ localName)))
        (names.localUpdates name localName).1
    exact List.mem_append_right _ (List.mem_map.mpr ⟨name, localSlot, rfl⟩)
  · intro argument member same
    have present := List.mem_map_of_mem (f := Prod.fst) member
    rw [assigned_slots bound, same] at present
    obtain ⟨other, member, equal⟩ := List.mem_map.mp present
    have sameName : other = name := congrArg Binding.name equal
    rw [sameName] at member
    exact (names.localUpdates name localName).1 member

theorem failed_local_unbound {globals : List String} {spec : Spec} (names : Names spec) (plan : Plan globals spec)
    (childId : Nat) (caller : State) (moduleCaptures : List Capture) {values : List Value} {assigned : List (Binding × Value)}
    (bound : Entry.Binds spec.parameters values (.ok assigned)) (name : String) (localName : name ∈ spec.updates.map Prod.fst)
    {error : Silmaril.Languages.Starlark.Lists.Error} {next : State}
    (failed : Defaults.Escape.ReturnsWith spec.wrapper childId plan.body.free spec.updates caller
      (activate caller (spec.frame childId).declaration moduleCaptures assigned) (.error error next)) :
    let active := activate caller (spec.frame childId).declaration moduleCaptures assigned
    ∃ address, active.slots (fileSlot name) = some (.owned address) ∧
      next.heap[address]? = some ⟨.binding none, false⟩ ∧ next.slots = caller.slots ∧ next.bindings = caller.bindings := by
  obtain ⟨address, owned, stored⟩ := local_unbound names childId caller moduleCaptures bound name localName
  obtain ⟨slots, bindings, kept⟩ := Defaults.Escape.failed_keeps failed
  exact ⟨address, owned, kept _ _ _ stored, slots, bindings⟩

private theorem installs_order {active : State} {free : List FreeName} {captures : List Capture}
    (installed : Installs active free captures) :
    captures.map Capture.binding = free.map FreeName.target := by
  induction installed with
  | nil => rfl
  | cons receipt _ ih => cases receipt <;> simp [ih]

private theorem selected_unique {block : LexicalBlock} {reads : List Binding} {free : List FreeName}
    (selected : Selects block reads free) : (free.map FreeName.target).Nodup := by
  have targets {reads : List Binding} {free : List FreeName} (tail : Selects block reads free) :
      free.map FreeName.target =
        reads.eraseDups.filter (fun binding => binding.scope == .global || !block.owned.contains binding.name) := by
    simp [← Silmaril.Languages.Starlark.Modules.Resolve.Capture.captureNames_eq tail, Silmaril.Languages.Starlark.Modules.Resolve.captureNames,
      List.map_map, Function.comp_def]
  induction selected with
  | nil => simp
  | owned _ _ ih => exact ih
  | enclosing _ tail ih | module _ tail ih =>
    rw [List.map_cons, List.nodup_cons]
    exact ⟨by rw [targets tail]; simp, ih⟩

theorem capture_order {globals : List String} {spec : Spec} (plan : Plan globals spec)
    {active : State} {captures : List Capture} (installed : Installs active plan.body.free captures) :
    captures.map Capture.binding = (plan.body.declaration spec.wrapper.codes).free.map FreeName.target ∧
      (captures.map Capture.binding).Nodup := by
  have ordered := installs_order installed
  exact ⟨ordered, by rw [ordered]; exact selected_unique plan.body.selects⟩

theorem returns_total {globals : List String} {spec : Spec} (names : Names spec)
    (plan : Plan globals spec) (program : Program) (available : List DeclarationId) (childId : Nat)
    (found : program[childId]? = some (plan.body.declaration spec.wrapper.codes))
    (caller : State) (moduleCaptures : List Capture) (moduleInstalled : Installs caller plan.moduleFree moduleCaptures)
    (moduleCells : Defaults.Body.CaptureCells caller moduleCaptures) (assigned : List (Binding × Value)) :
    let active := activate caller (plan.frame childId).declaration moduleCaptures assigned
    ∃ out bodyOut, Returns plan childId caller moduleCaptures assigned out ∧
      Exec program available active (plan.frame childId).code bodyOut ∧ Leaf.returnTo caller bodyOut = out ∧
      (∀ value next, out = .ok value next → ∃ address values reached captures,
        value = .function address ∧ values.length = spec.child.parameters.optional.length ∧
        Defaults.Body.RunsPrefix (spec.block globals) active spec.leading plan.leadingCode (.ok () reached) ∧
        (∃ defaultsState, Defaults.Escape.DefaultsIn spec.wrapper.parameter reached
          (spec.wrapper.defaults.map Prod.snd) (.ok values defaultsState)) ∧
        Installs reached plan.body.free captures ∧
        next.heap[address]? = some ⟨.function ⟨childId, captures, spec.wrapper.saved values⟩, false⟩ ∧
        Bindings.Preserves caller next ∧ Defaults.Body.CaptureCells next captures ∧
        (∀ parameter before frozen,
          reached.slots (fileSlot spec.wrapper.parameter) = some (.owned parameter) →
          reached.heap[parameter]? = some ⟨.binding before, frozen⟩ →
          next.heap[parameter]? = some ⟨.binding (some (.scalar (.int spec.wrapper.rebound))), frozen⟩)) := by
  let frame := plan.frame childId
  let active := activate caller frame.declaration moduleCaptures assigned
  have layout : Defaults.Body.Frame (spec.block globals) plan.moduleFree caller.heap.size active :=
    prefix_frame plan childId caller moduleCaptures moduleInstalled moduleCells assigned
  obtain ⟨result, leadingRun, live, stable⟩ := Defaults.Body.prefix_total plan.leading active layout
  let tail := (spec.frame childId).code
  cases result with
  | error error after =>
    have ran := Defaults.Body.prefix_sound program available leadingRun tail (.error error after) (by
      intro _ impossible; cases impossible)
    exact ⟨_, _, .failed leadingRun, ran, rfl, fun _ _ impossible => nomatch impossible⟩
  | ok value reached =>
    cases value
    have separate : RootCall.DistinctOwned reached := by
      have sameSlots : reached.slots = active.slots := stable.1
      have distinct : RootCall.DistinctOwned active := RootCall.activation_distinct caller frame.declaration moduleCaptures assigned
      simpa only [RootCall.DistinctOwned, sameSlots] using distinct
    have earlier (address : Nat) (stored : Cell) (found : caller.heap[address]? = some stored) :
        reached.heap[address]? = some stored := by
      have low := (Array.getElem?_eq_some_iff.mp found).choose
      exact stable.2 address stored low ((Wrapper.activation_preserves caller frame.declaration moduleCaptures assigned address low).trans found)
    obtain ⟨captures, installed, cells⟩ := reached_installs plan live
    obtain ⟨out, bodyOut, returned, ranTail, restored, progress⟩ := Defaults.Escape.returns_from_total
      program available spec.wrapper names.wrapper childId (plan.body.declaration spec.wrapper.codes) found rfl
      spec.additional (spec.leading.map Prod.fst) names.childFresh spec.updates names.localUpdates globals
      caller reached ⟨live.owned, by simp⟩ separate earlier captures installed cells
    have ran := Defaults.Body.prefix_sound program available leadingRun tail bodyOut (by
      intro state same
      cases same
      exact ranTail)
    refine ⟨out, bodyOut, .entered leadingRun returned, ran, restored, ?_⟩
    intro value next same
    obtain ⟨address, values, equality, length, record, kept, savedCells, defaults, rebound⟩ := progress value next same
    exact ⟨address, values, reached, captures, equality, length, leadingRun, defaults, installed, record, kept, savedCells, rebound⟩

private theorem returns_unique {globals : List String} {spec : Spec} {plan : Plan globals spec} {childId : Nat}
    {caller : State} {moduleCaptures : List Capture} {assigned : List (Binding × Value)} {first second : Outcome Value}
    (left : Returns plan childId caller moduleCaptures assigned first) (right : Returns plan childId caller moduleCaptures assigned second) :
    first = second := by
  cases left with
  | failed leading =>
    cases right with
    | failed other => cases Defaults.Body.prefix_unique leading other; rfl
    | entered other _ => cases Defaults.Body.prefix_unique leading other
  | entered leading rest =>
    cases right with
    | failed other => cases Defaults.Body.prefix_unique leading other
    | entered other later =>
      cases Defaults.Body.prefix_unique leading other
      exact Defaults.Escape.returns_with_unique rest later

theorem returns_sound {globals : List String} {spec : Spec} (names : Names spec)
    (plan : Plan globals spec) (program : Program) (available : List DeclarationId) (childId : Nat)
    (found : program[childId]? = some (plan.body.declaration spec.wrapper.codes))
    (caller : State) (moduleCaptures : List Capture) (moduleInstalled : Installs caller plan.moduleFree moduleCaptures)
    (moduleCells : Defaults.Body.CaptureCells caller moduleCaptures) (assigned : List (Binding × Value)) {out : Outcome Value}
    (source : Returns plan childId caller moduleCaptures assigned out) :
    ∃ bodyOut, Exec program available (activate caller (plan.frame childId).declaration moduleCaptures assigned)
      (plan.frame childId).code bodyOut ∧ Leaf.returnTo caller bodyOut = out := by
  obtain ⟨_, bodyOut, reached, ran, restored, _⟩ := returns_total names plan program available childId found caller moduleCaptures moduleInstalled moduleCells assigned
  exact ⟨bodyOut, ran, restored.trans (returns_unique reached source)⟩

theorem returned_frame {globals : List String} {spec : Spec} (names : Names spec)
    (plan : Plan globals spec) (program : Program) (available : List DeclarationId) (childId : Nat)
    (found : program[childId]? = some (plan.body.declaration spec.wrapper.codes))
    (caller : State) (moduleCaptures : List Capture) (moduleInstalled : Installs caller plan.moduleFree moduleCaptures)
    (moduleCells : Defaults.Body.CaptureCells caller moduleCaptures) (assigned : List (Binding × Value)) {address : Nat} {next : State}
    (source : Returns plan childId caller moduleCaptures assigned (.ok (.function address) next)) :
    let active := activate caller (plan.frame childId).declaration moduleCaptures assigned
    ∃ reached values captures, values.length = spec.child.parameters.optional.length ∧
      Defaults.Body.RunsPrefix (spec.block globals) active spec.leading plan.leadingCode (.ok () reached) ∧
      (∃ defaultsState, Defaults.Escape.DefaultsIn spec.wrapper.parameter reached
        (spec.wrapper.defaults.map Prod.snd) (.ok values defaultsState)) ∧
      Installs reached plan.body.free captures ∧
      next.heap[address]? = some ⟨.function ⟨childId, captures, spec.wrapper.saved values⟩, false⟩ ∧
      next.slots = caller.slots ∧ next.bindings = caller.bindings ∧
      (∀ parameter before frozen,
        reached.slots (fileSlot spec.wrapper.parameter) = some (.owned parameter) →
        reached.heap[parameter]? = some ⟨.binding before, frozen⟩ →
        next.heap[parameter]? = some ⟨.binding (some (.scalar (.int spec.wrapper.rebound))), frozen⟩) ∧
      ∀ arguments : List (Binding × Value),
        Defaults.Body.Frame plan.body.block plan.body.free next.heap.size
          (activate next (plan.body.declaration spec.wrapper.codes) captures arguments) := by
  obtain ⟨_, _, independently, _, _, progress⟩ := returns_total names plan program available childId found caller moduleCaptures moduleInstalled moduleCells assigned
  obtain ⟨actual, values, reached, captures, same, count, leading, defaults, installed, cell, kept, cells, rebound⟩ :=
    progress _ _ (returns_unique independently source)
  cases same
  refine ⟨reached, values, captures, count, leading, defaults, installed, cell, kept.slots, ?_, rebound, ?_⟩
  · cases source with
    | entered _ exit => cases exit; rfl
  · intro arguments
    exact Defaults.Body.captured_frame plan.body _ (Defaults.Escape.code_length spec.wrapper) next reached
      captures installed cells arguments

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped

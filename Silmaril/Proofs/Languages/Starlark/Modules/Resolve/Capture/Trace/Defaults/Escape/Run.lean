module

public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Site
public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall.Bindings
public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Wrapper.Heap
public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Frame

import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape

open Silmaril.Languages.Starlark (Binding)
open Silmaril.Languages.Starlark.Modules (fileSlot)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Assignment (LexicalBlock)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Lists (State Cell Outcome Value Slot)
open Silmaril.Languages.Starlark.Lists.Iteration (Flow finishState)

theorem frame_layout_with (wrapper : Spec) (admitted : WrapperNames wrapper) (childId : Nat)
    (caller : State) (argument : Value) :
    let frame := activate caller (wrapper.frame childId).declaration [] [(fileSlot wrapper.parameter, argument)]
    frame.slots (fileSlot wrapper.parameter) = some (.owned caller.heap.size) ∧
    frame.heap[caller.heap.size]? = some ⟨.binding (some argument), false⟩ ∧
    frame.slots (fileSlot wrapper.childName) = some (.owned (caller.heap.size + 1)) ∧
    frame.heap[caller.heap.size + 1]? = some ⟨.binding none, false⟩ := by
  have different : fileSlot wrapper.parameter ≠ fileSlot wrapper.childName := by
    intro same
    exact admitted.distinct (congrArg Binding.name same)
  simp [activate, Spec.frame, Spec.locals, Spec.occurrences, List.eraseDups_cons, Ne.symm admitted.distinct, admitted.distinct,
    Forwarding.Frame.declaration, requiredSignature,
    Signature.slots, Signature.named, State.allocateSlot, State.write, different,
    Array.getElem?_push, Array.getElem?_setIfInBounds, Array.size_push]
  constructor
  · omega
  · let blank : Cell := ⟨.binding none, false⟩
    simpa only [Array.size_push, blank] using Array.getElem_push_eq (xs := caller.heap.push blank) (x := blank)

theorem frame_layout (wrapper : Spec) (admitted : Admitted wrapper) (childId : Nat)
    (caller : State) (argument : Value) :
    let frame := activate caller (wrapper.frame childId).declaration [] [(fileSlot wrapper.parameter, argument)]
    frame.slots (fileSlot wrapper.parameter) = some (.owned caller.heap.size) ∧
    frame.heap[caller.heap.size]? = some ⟨.binding (some argument), false⟩ ∧
    frame.slots (fileSlot wrapper.childName) = some (.owned (caller.heap.size + 1)) ∧
    frame.heap[caller.heap.size + 1]? = some ⟨.binding none, false⟩ :=
  frame_layout_with wrapper admitted.wrapperNames childId caller argument

private theorem returns_unique {wrapper : Spec} {childId : Nat} {caller : State} {argument : Value}
    {first second : Outcome Value} (a : Returns wrapper childId caller argument first)
    (b : Returns wrapper childId caller argument second) : first = second := by
  cases a with
  | failed earlier =>
    cases b with
    | failed later => cases Defaults.Lexical.unique earlier later; rfl
    | child later => cases Defaults.Lexical.unique earlier later
  | child earlier =>
    cases b with
    | failed later => cases Defaults.Lexical.unique earlier later
    | child later => cases Defaults.Lexical.unique earlier later; rfl

theorem failed_child_unbound (wrapper : Spec) (admitted : Admitted wrapper) (childId : Nat)
    (caller : State) (argument : Value) {error : Silmaril.Languages.Starlark.Lists.Error} {next : State}
    (failed : Returns wrapper childId caller argument (.error error next)) :
    next.heap[caller.heap.size]? = some ⟨.binding (some argument), false⟩ ∧
    next.heap[caller.heap.size + 1]? = some ⟨.binding none, false⟩ ∧
    next.slots = caller.slots ∧ next.bindings = caller.bindings := by
  cases failed with
  | @failed _ final ran =>
    let active := activate caller (wrapper.frame childId).declaration [] [(fileSlot wrapper.parameter, argument)]
    obtain ⟨out, traced, kept, _⟩ := Defaults.Lexical.total (legacy_elaborates wrapper admitted) active
    have equal := Defaults.Lexical.unique traced ran
    rw [equal] at kept
    obtain ⟨_, parameter, _, child⟩ := frame_layout wrapper admitted childId caller argument
    exact ⟨kept.2 _ _ parameter, kept.2 _ _ child, rfl, rfl⟩

theorem failed_keeps {wrapper : Spec} {block : LexicalBlock} {items : List PlainPositionalDefault}
    {childId : Nat} {free : List FreeName} {updates : List (String × Int)}
    {caller active next : State} {error : Silmaril.Languages.Starlark.Lists.Error}
    (related : Defaults.Lexical.Elaborates block wrapper.child.parameters.optional items)
    (failed : ReturnsWith wrapper block items childId free updates caller active (.error error next)) :
    next.slots = caller.slots ∧ next.bindings = caller.bindings ∧
      ∀ (address : Nat) (value : Option Value) (frozen : Bool),
        active.heap[address]? = some (⟨.binding value, frozen⟩ : Cell) →
          next.heap[address]? = some (⟨.binding value, frozen⟩ : Cell) := by
  cases failed with
  | @failed _ final ran =>
    obtain ⟨out, traced, kept, _⟩ := Defaults.Lexical.total related active
    rw [Defaults.Lexical.unique traced ran] at kept
    exact ⟨rfl, rfl, fun _ _ _ cell => kept.2 _ _ cell⟩

private theorem kept_write (state : State) (target : Binding) (value : Value) (address : Nat)
    (owned : state.slots target = some (.owned address)) (key : Nat) (different : key ≠ address) :
    (state.write target value).heap[key]? = state.heap[key]? :=
  RootCall.write_other_cell _ _ _ _ (by simp [owned, Ne.symm different])

/-- Each update executes as a step of the existing straight-line body.
The child binding remains readable, and earlier caller cells are untouched. -/
private theorem updates_run (wrapper : Spec) (updates : List (String × Int)) (block : LexicalBlock)
    (known : wrapper.childName ∈ block.owned)
    (writes : ∀ name ∈ updates.map Prod.fst, name ∈ block.owned ∧ name ≠ wrapper.childName)
    (floor : Nat) (state : State) (frame : Defaults.Body.Frame block [] floor state)
    (distinct : RootCall.DistinctOwned state) (value : Value)
    (read : state.bindingValue (fileSlot wrapper.childName) = .ok value) :
    Defaults.Body.Runs block state (wrapper.updateSuite updates) (wrapper.updateCode updates)
        (.ok (.returned value) (applyUpdates updates state)) ∧
      Defaults.Body.Keeps floor state (applyUpdates updates state) := by
  induction updates generalizing state with
  | nil =>
    have observed : Defaults.Body.Evaluates block state (.scalar (.read wrapper.childName))
        (Leaf.readOperand (fileSlot wrapper.childName)) (state.read (.bound (fileSlot wrapper.childName))) :=
      .read (.owned known)
    rw [State.read, read] at observed
    exact ⟨.ret observed, rfl, fun _ _ _ cell => cell⟩
  | cons update rest ih =>
    obtain ⟨member, different⟩ := writes update.1 List.mem_cons_self
    let valueWritten : Value := .scalar (.int update.2)
    let next := state.write (fileSlot update.1) valueWritten
    have slots : next.slots = state.slots := slots_write _ _ _
    obtain ⟨childAddress, _, _, _, childAt, _⟩ := frame.owned wrapper.childName known
    have other : state.slots (fileSlot update.1) ≠ some (.owned childAddress) :=
      fun hit => different (congrArg Binding.name (distinct _ _ _ hit childAt))
    have same : next.heap[childAddress]? = state.heap[childAddress]? :=
      RootCall.write_other_cell state (fileSlot update.1) valueWritten childAddress other
    have readNext : next.bindingValue (fileSlot wrapper.childName) = .ok value := by
      simpa only [State.bindingValue, slots, childAt, Slot.address, same] using read
    obtain ⟨nextFrame, firstKeeps⟩ := Defaults.Body.written_frame member valueWritten frame
    have distinctNext : RootCall.DistinctOwned next := by simpa only [RootCall.DistinctOwned, slots] using distinct
    obtain ⟨tail, preserves⟩ := ih (fun name hit => writes name (List.mem_cons_of_mem _ hit)) next
      nextFrame distinctNext readNext
    exact ⟨.assign (.int update.2) tail, Defaults.Body.keeps_trans firstKeeps preserves⟩

private theorem updates_keep (updates : List (String × Int)) (state : State)
    (captures : List Silmaril.Languages.Starlark.Lists.Capture)
    (address : Nat) (closure : Silmaril.Languages.Starlark.Lists.Closure)
    (stored : state.heap[address]? = some ⟨.function closure, false⟩)
    (live : Defaults.Body.CaptureCells state captures) :
    (applyUpdates updates state).heap[address]? = some ⟨.function closure, false⟩ ∧
      Defaults.Body.CaptureCells (applyUpdates updates state) captures := by
  induction updates generalizing state with
  | nil => exact ⟨stored, live⟩
  | cons update rest ih =>
    exact ih _ (write_keeps_function _ _ _ _ _ _ stored) (Defaults.Body.capture_cells_written _ _ _ live)

private theorem updates_other (updates : List (String × Int)) (state : State) (name : String)
    (address : Nat) (owned : state.slots (fileSlot name) = some (.owned address))
    (distinct : RootCall.DistinctOwned state) (different : name ∉ updates.map Prod.fst) :
    (applyUpdates updates state).heap[address]? = state.heap[address]? := by
  induction updates generalizing state with
  | nil => rfl
  | cons update rest ih =>
    have other : state.slots (fileSlot update.1) ≠ some (.owned address) := by
      intro found
      exact different (List.mem_cons.mpr (.inl (congrArg Binding.name (distinct _ _ _ owned found))))
    let next := state.write (fileSlot update.1) (.scalar (.int update.2))
    have slots : next.slots = state.slots := slots_write _ _ _
    have keptDistinct : RootCall.DistinctOwned next := by simpa only [RootCall.DistinctOwned, slots] using distinct
    exact (ih next (slots ▸ owned) keptDistinct (fun hit => different (List.mem_cons_of_mem _ hit))).trans
      (RootCall.write_other_cell _ _ _ _ other)

theorem wrapper_activation (frame : Forwarding.Frame) (globals : List String)
    (caller : State) (captures : List Silmaril.Languages.Starlark.Lists.Capture) (assigned : List (Binding × Value)) :
    Defaults.Body.Frame ⟨frame.owned, [], globals⟩ [] caller.heap.size (activate caller frame.declaration captures assigned) := by
  refine ⟨?_, by simp⟩
  intro name declared
  obtain ⟨address, value, frozen, owned, stored⟩ := Entry.activated_cell caller frame captures assigned name declared
  exact ⟨address, value, frozen, Wrapper.activation_fresh caller frame.declaration captures assigned _ _ owned, owned, stored⟩

/-- Execute the wrapper with its reached positional binding and installed
capture vector. The trailing body initializes or rebinds its owned locals
through the same cells recorded during child installation. -/
theorem returns_from_total (program : Program) (available : List DeclarationId) (wrapper : Spec)
    (admitted : WrapperNames wrapper) (childId : Nat) (declaration : Declaration)
    (found : program[childId]? = some declaration)
    {defaultBlock : LexicalBlock} {items : List PlainPositionalDefault}
    (defaults : Defaults.Lexical.Elaborates defaultBlock wrapper.child.parameters.optional items)
    (signature : declaration.signature = wrapper.child.parameters.signature (items.map PlainPositionalDefault.value))
    (additional leading : List String) (childFresh : wrapper.childName ∉ additional) (updates : List (String × Int))
    (fresh : ∀ name ∈ updates.map Prod.fst, name ∉ wrapper.parameter :: additional ∧ name ≠ wrapper.childName)
    (globals : List String) (caller active : State)
    (layout : Defaults.Body.Frame ⟨(wrapper.frame childId additional updates leading).owned, [], globals⟩
      [] caller.heap.size active)
    (activeDistinct : RootCall.DistinctOwned active)
    (earlier : ∀ (address : Nat) (stored : Cell), caller.heap[address]? = some stored →
      active.heap[address]? = some stored)
    (captures : List Silmaril.Languages.Starlark.Lists.Capture)
    (selected : Installs active declaration.free captures)
    (cells : Defaults.Body.CaptureCells active captures) :
    ∃ out bodyOut, ReturnsWith wrapper defaultBlock items childId declaration.free updates caller active out ∧
      Exec program available active (wrapper.frame childId additional updates leading).code bodyOut ∧
      Leaf.returnTo caller bodyOut = out ∧
      (∀ value next, out = .ok value next → ∃ address values,
        value = .function address ∧ values.length = wrapper.child.parameters.optional.length ∧
        next.heap[address]? = some ⟨.function ⟨childId, captures, wrapper.saved values⟩, false⟩ ∧
        Bindings.Preserves caller next ∧ Defaults.Body.CaptureCells next captures ∧
        (∃ defaultsState, Defaults.Lexical.Evaluates defaultBlock active items (.ok values defaultsState)) ∧
        (∀ parameter before frozen,
          active.slots (fileSlot wrapper.parameter) = some (.owned parameter) →
          active.heap[parameter]? = some ⟨.binding before, frozen⟩ →
          next.heap[parameter]? = some ⟨.binding (some (.scalar (.int wrapper.rebound))), frozen⟩)) := by
  let frame := wrapper.frame childId additional updates leading
  let block : LexicalBlock := ⟨frame.owned, [], globals⟩
  have childKnown : wrapper.childName ∈ block.owned :=
    List.mem_append_right _ (wrapper.local_member updates additional leading _ (by simp [Spec.occurrences]) (by
      simp [Ne.symm admitted.distinct, childFresh]))
  have parameterKnown : wrapper.parameter ∈ block.owned := by simp [block, frame, Spec.frame, Forwarding.Frame.owned]
  obtain ⟨parameterAddress, parameterBefore, parameterFrozen, parameterFresh, paramOwn, paramCell⟩ :=
    layout.owned wrapper.parameter parameterKnown
  obtain ⟨childAddress, childBefore, childFrozen, childFreshAddress, childOwn, childCell⟩ :=
    layout.owned wrapper.childName childKnown
  have distinct : parameterAddress ≠ childAddress := by
    intro equal
    have owned := activeDistinct _ _ _ paramOwn (equal ▸ childOwn)
    exact admitted.distinct (congrArg Binding.name owned)
  obtain ⟨out, ran, extension, count⟩ := Defaults.Lexical.total defaults active
  have kept : Bindings.Preserves active (finishState out) := ⟨extension.1, fun address cell found _ => extension.2 address cell found⟩
  have execute {out : Outcome Flow} (step : Defaults.Lexical.Defines defaultBlock (fileSlot wrapper.childName) childId
      declaration.free wrapper.child.parameters items active out) :
      Exec program available active (.define (fileSlot wrapper.childName) childId) out :=
    (Defaults.Lexical.defines_sound program available _ childId _ declaration defaults found signature step).1
  cases out with
  | error error final =>
    exact ⟨_, _, .failed ran, .seqError (execute (.failed ran)), rfl, fun _ _ impossible => nomatch impossible⟩
  | ok values final =>
    have installs := Silmaril.Languages.Starlark.Modules.Resolve.Capture.installs_in_same_slots kept.slots selected
    let cell : Cell := ⟨.function ⟨childId, captures, wrapper.saved values⟩, false⟩
    let grown : State := { final with heap := final.heap.push cell }
    let child := fileSlot wrapper.childName
    let parameter := fileSlot wrapper.parameter
    let value : Value := .scalar (.int wrapper.rebound)
    let installed := grown.write child (.function final.heap.size)
    let rebound := installed.write parameter value
    have grownKept : Bindings.Preserves active grown := kept.trans (Bindings.Preserves.push final cell)
    have installedSlots : installed.slots = active.slots := (slots_write _ _ _).trans grownKept.slots
    have childAt : grown.slots child = some (.owned childAddress) := grownKept.slots ▸ childOwn
    have childStored := grownKept.cells _ _ childCell trivial
    have installedRead : installed.bindingValue child = .ok (.function final.heap.size) :=
      writes_binding grown child _ _ childAt childStored
    have paramAt : installed.slots parameter = some (.owned parameterAddress) := installedSlots ▸ paramOwn
    have childAfter : installed.slots child = some (.owned childAddress) := installedSlots ▸ childOwn
    have reboundRead : rebound.bindingValue child = .ok (.function final.heap.size) := by
      have saved := kept_write installed parameter value parameterAddress paramAt childAddress (Ne.symm distinct)
      simpa only [State.bindingValue, rebound, slots_write, childAfter, Slot.address, saved] using installedRead
    have childCode : Exec program available active (.define child childId) (.ok .next installed) :=
      execute (.installed ran installs)
    have assignCode : Exec program available installed (.assignExpr parameter (.atom (.scalar (.int wrapper.rebound))))
        (.ok .next rebound) :=
      .assignExpr (.evaluates (calls := fun _ _ _ => False) (fun _ _ _ h => h.elim) (.atom trivial .scalar))
    have grownFrame : Defaults.Body.Frame block [] caller.heap.size grown := by
      refine ⟨?_, by simp⟩
      intro name member
      obtain ⟨address, before, frozen, freshAddress, slot, stored⟩ := layout.owned name member
      exact ⟨address, before, frozen, freshAddress, grownKept.slots ▸ slot, grownKept.cells _ _ stored trivial⟩
    have installedFrame := (Defaults.Body.written_frame childKnown (.function final.heap.size) grownFrame).1
    have reboundFrame := (Defaults.Body.written_frame parameterKnown value installedFrame).1
    have reboundSlots : rebound.slots = active.slots := (slots_write _ _ _).trans installedSlots
    have reboundDistinct : RootCall.DistinctOwned rebound := by
      simpa only [RootCall.DistinctOwned, reboundSlots] using activeDistinct
    have localWrites (name : String) (member : name ∈ updates.map Prod.fst) :
        name ∈ block.owned ∧ name ≠ wrapper.childName :=
      ⟨List.mem_append_right _ (wrapper.local_member updates additional leading name
        (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member))) (fresh name member).1),
        (fresh name member).2⟩
    obtain ⟨tail, tailKeeps⟩ := updates_run wrapper updates block childKnown localWrites caller.heap.size
      rebound reboundFrame reboundDistinct (.function final.heap.size) reboundRead
    let done := applyUpdates updates rebound
    have body : Exec program available active frame.code (.ok (.returned (.function final.heap.size)) done) :=
      .seq childCode (.seq assignCode (Defaults.Body.runs_sound program available tail))
    refine ⟨_, _, .child ran installs, body, rfl, ?_⟩
    intro result next same
    cases same
    have length : values.length = wrapper.child.parameters.optional.length := count values final rfl
    have recordAfter : rebound.heap[final.heap.size]? = some cell :=
      write_keeps_function _ _ _ _ _ _
        (write_keeps_function _ _ _ _ _ _ Array.getElem?_push_size)
    have untilInstall := Defaults.Body.capture_cells_preserved grownKept cells
    have afterInstall := Defaults.Body.capture_cells_written grown child (.function final.heap.size) untilInstall
    have afterRebind := Defaults.Body.capture_cells_written installed parameter value afterInstall
    obtain ⟨recordDone, cellsDone⟩ := updates_keep updates rebound captures final.heap.size _ recordAfter afterRebind
    refine ⟨final.heap.size, values, rfl, length, recordDone, ⟨rfl, ?_⟩, cellsDone, ⟨final, ran⟩, ?_⟩
    · intro index stored existing kind
      have low := (Array.getElem?_eq_some_iff.mp existing).choose
      have inGrown := grownKept.cells index stored (earlier index stored existing) kind
      have afterChild := kept_write grown child (.function final.heap.size) _ childAt index (by omega)
      have afterRebound := kept_write installed parameter value _ paramAt index (by omega)
      exact tailKeeps.2 index stored low (afterRebound.trans (afterChild.trans inGrown))
    · intro index before frozen owned stored
      have same := Option.some.inj (paramOwn.symm.trans owned)
      cases same
      have retained : installed.heap[parameterAddress]? = some ⟨.binding before, frozen⟩ :=
        (kept_write grown child (.function final.heap.size) _ childAt parameterAddress distinct).trans
          (grownKept.cells _ _ stored trivial)
      have within := (Array.getElem?_eq_some_iff.mp retained).choose
      have reboundValue : rebound.heap[parameterAddress]? = some ⟨.binding (some value), frozen⟩ := by
        simp only [rebound, State.write, paramAt, retained]
        exact Array.getElem?_setIfInBounds_self_of_lt within
      have other : wrapper.parameter ∉ updates.map Prod.fst :=
        fun member => (fresh wrapper.parameter member).1 List.mem_cons_self
      exact (updates_other updates rebound wrapper.parameter parameterAddress
        (reboundSlots ▸ paramOwn) reboundDistinct other).trans reboundValue

theorem returns_total (program : Program) (available : List DeclarationId) (wrapper : Spec)
    (admitted : Admitted wrapper) (childId : Nat) (found : program[childId]? = some (wrapper.child.emitted wrapper.codes))
    (caller : State) (argument : Value) :
    ∃ out bodyOut, Returns wrapper childId caller argument out ∧
      Exec program available
        (activate caller (wrapper.frame childId).declaration [] [(fileSlot wrapper.parameter, argument)])
        (wrapper.frame childId).code bodyOut ∧ Leaf.returnTo caller bodyOut = out ∧
      (∀ value next, out = .ok value next → ∃ address values,
        value = .function address ∧ values.length = wrapper.child.parameters.optional.length ∧
        next.heap[address]? = some ⟨.function ⟨childId, [], wrapper.saved values⟩, false⟩ ∧
        next.heap[caller.heap.size]? = some ⟨.binding (some (.scalar (.int wrapper.rebound))), false⟩ ∧
        Bindings.Preserves caller next) := by
  let frame := wrapper.frame childId
  let assigned := [(fileSlot wrapper.parameter, argument)]
  let active := activate caller frame.declaration [] assigned
  have earlier (address : Nat) (stored : Cell) (found : caller.heap[address]? = some stored) :
      active.heap[address]? = some stored :=
    (Wrapper.activation_preserves caller frame.declaration [] assigned _ (Array.getElem?_eq_some_iff.mp found).choose).trans found
  obtain ⟨out, bodyOut, source, ran, restored, result⟩ := returns_from_total program available wrapper
    admitted.wrapperNames childId (wrapper.child.emitted wrapper.codes) found (legacy_elaborates wrapper admitted)
    (by rw [planned_codes]; rfl) [] [] (by simp) [] (by simp)
    [] caller active (wrapper_activation frame [] caller [] assigned)
    (RootCall.activation_distinct caller frame.declaration [] assigned) earlier [] .nil (by simp [Defaults.Body.CaptureCells])
  refine ⟨out, bodyOut, ?_, ran, restored, ?_⟩
  · cases source with
    | failed failed => exact .failed failed
    | child evaluated installed =>
      cases installed
      exact .child evaluated
  · intro value state equality
    obtain ⟨address, values, returned, length, cell, kept, _, _, rebound⟩ := result value state equality
    obtain ⟨owned, stored, _, _⟩ := frame_layout wrapper admitted childId caller argument
    exact ⟨address, values, returned, length, cell, rebound _ _ _ owned stored, kept⟩

theorem returns_with_unique {wrapper : Spec} {block : LexicalBlock} {items : List PlainPositionalDefault} {childId : Nat} {free : List FreeName}
    {updates : List (String × Int)} {caller active : State} {first second : Outcome Value}
    (a : ReturnsWith wrapper block items childId free updates caller active first)
    (b : ReturnsWith wrapper block items childId free updates caller active second) : first = second := by
  cases a with
  | failed earlier =>
    cases b with
    | failed later => cases Defaults.Lexical.unique earlier later; rfl
    | child later _ => cases Defaults.Lexical.unique earlier later
  | child earlier installed =>
    cases b with
    | failed later => cases Defaults.Lexical.unique earlier later
    | child later installed' =>
      cases Defaults.Lexical.unique earlier later
      have same := Except.ok.inj ((Capture.installs_lookup _ installed).symm.trans (Capture.installs_lookup _ installed'))
      cases same
      rfl

theorem returns_sound (program : Program) (available : List DeclarationId) (wrapper : Spec)
    (admitted : Admitted wrapper) (childId : Nat) (found : program[childId]? = some (wrapper.child.emitted wrapper.codes))
    (caller : State) (argument : Value) {out : Outcome Value} (source : Returns wrapper childId caller argument out) :
    ∃ bodyOut, Exec program available
        (activate caller (wrapper.frame childId).declaration [] [(fileSlot wrapper.parameter, argument)])
        (wrapper.frame childId).code bodyOut ∧ Leaf.returnTo caller bodyOut = out := by
  obtain ⟨_, bodyOut, result, ran, returned, _⟩ := returns_total program available wrapper admitted childId found caller argument
  exact ⟨bodyOut, ran, returned.trans (returns_unique result source)⟩

theorem returned_record (program : Program) (available : List DeclarationId) (wrapper : Spec)
    (admitted : Admitted wrapper) (childId : Nat) (found : program[childId]? = some (wrapper.child.emitted wrapper.codes))
    (caller : State) (argument : Value) {address : Nat} {next : State}
    (source : Returns wrapper childId caller argument (.ok (.function address) next)) :
    ∃ defaults, defaults.length = wrapper.child.parameters.optional.length ∧
      next.heap[address]? = some ⟨.function ⟨childId, [], wrapper.saved defaults⟩, false⟩ ∧
      next.heap[caller.heap.size]? = some ⟨.binding (some (.scalar (.int wrapper.rebound))), false⟩ ∧
      next.slots = caller.slots ∧ next.bindings = caller.bindings := by
  obtain ⟨_, _, returned, _, _, observation⟩ := returns_total program available wrapper admitted childId found caller argument
  obtain ⟨actual, defaults, equal, length, cell, rebound, kept⟩ := observation _ _ (returns_unique returned source)
  cases equal
  exact ⟨defaults, length, cell, rebound, kept.slots, by cases source; rfl⟩

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape

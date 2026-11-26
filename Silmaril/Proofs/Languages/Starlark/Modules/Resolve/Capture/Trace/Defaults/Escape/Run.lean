module

public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Site
public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall.Bindings
public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Wrapper.Heap

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape

open Silmaril.Languages.Starlark (Binding)
open Silmaril.Languages.Starlark.Modules (fileSlot)
open Silmaril.Languages.Starlark.Modules.Resolve
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
  simp [activate, Spec.frame, Forwarding.Frame.declaration, requiredSignature,
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

private abbrev EvalOperand (program : Program) (available : List DeclarationId)
    (state : State) (code : Lowering.Expr) (out : Outcome Value) :=
  Lowering.EvaluatesWith program available (fun _ _ _ => False) (fun _ => True) state code out

private theorem operand_sound (program : Program) (available : List DeclarationId)
    {parameter : String} {state : State} {operand : Operand} {out : Outcome Value}
    (source : Evaluates parameter state operand out) :
    EvalOperand program available state (operand.code parameter) out := by
  cases source with
  | parameter => exact .atom trivial .read
  | integer => exact .atom trivial .scalar
  | list =>
    exact .list (.cons (.atom trivial .scalar) .empty)
  | index offset =>
    have read : EvalOperand program available state (Leaf.readOperand (fileSlot parameter))
        (state.read (.bound (fileSlot parameter))) := .atom trivial .read
    cases same : state.read (.bound (fileSlot parameter)) with
    | error =>
      rw [same] at read
      exact .indexReceiverError read
    | ok =>
      rw [same] at read
      exact .index read (.atom trivial .scalar)

private theorem defaults_sound (program : Program) (available : List DeclarationId)
    {parameter : String} {state : State} {operands : List Operand} {out : Outcome (List Value)}
    (source : DefaultsIn parameter state operands out) :
    ExecExprs program available state (operands.map (fun operand => operand.code parameter)) out := by
  apply ExecExprs.evaluatesMany (calls := fun _ _ _ => False) (fun _ _ _ impossible => impossible.elim)
  induction source with
  | nil => exact .empty
  | failed first => exact .headError (operand_sound _ _ first)
  | @next _ _ _ _ _ out first _ ih =>
    cases out with
    | error => exact .tailError (operand_sound _ _ first) ih
    | ok => exact .cons (operand_sound _ _ first) ih

private theorem operand_total (parameter : String) (state : State) (operand : Operand) :
    ∃ out, Evaluates parameter state operand out ∧
      Bindings.Preserves state (finishState out) := by
  cases operand with
  | parameter =>
    refine ⟨_, .parameter, ?_⟩
    cases read : state.bindingValue (fileSlot parameter) <;>
      simpa [State.read, read, finishState] using Bindings.Preserves.refl state
  | integer value => exact ⟨_, .integer value, Bindings.Preserves.refl _⟩
  | list value => exact ⟨_, .list value, Bindings.Preserves.push _ _⟩
  | index offset =>
    refine ⟨_, .index offset, ?_⟩
    cases read : state.bindingValue (fileSlot parameter) with
    | error => simpa [State.read, read, Outcome.resume, finishState] using Bindings.Preserves.refl state
    | ok receiver =>
      simpa [State.read, read, Outcome.resume, RootCall.read_index_state] using Bindings.Preserves.refl state

private theorem operand_unique {parameter : String} {state : State} {operand : Operand}
    {first second : Outcome Value} (a : Evaluates parameter state operand first)
    (b : Evaluates parameter state operand second) : first = second := by
  cases a <;> cases b <;> rfl

private theorem defaults_unique {parameter : String} {state : State} {operands : List Operand}
    {first second : Outcome (List Value)} (a : DefaultsIn parameter state operands first)
    (b : DefaultsIn parameter state operands second) : first = second := by
  induction a generalizing second with
  | nil => cases b; rfl
  | next first tail ih =>
    cases b with
    | next other rest =>
      cases operand_unique first other
      rw [ih rest]
    | failed other => cases operand_unique first other
  | failed first =>
    cases b with
    | next other _ => cases operand_unique first other
    | failed other => cases operand_unique first other; rfl

private theorem returns_unique {wrapper : Spec} {childId : Nat} {caller : State} {argument : Value}
    {first second : Outcome Value} (a : Returns wrapper childId caller argument first)
    (b : Returns wrapper childId caller argument second) : first = second := by
  cases a with
  | failed earlier =>
    cases b with
    | failed later => cases defaults_unique earlier later; rfl
    | child later => cases defaults_unique earlier later
  | child earlier =>
    cases b with
    | failed later => cases defaults_unique earlier later
    | child later => cases defaults_unique earlier later; rfl

private theorem defaults_total (parameter : String) (state : State) (operands : List Operand) :
    ∃ out, DefaultsIn parameter state operands out ∧ Bindings.Preserves state (finishState out) ∧
      (∀ values final, out = .ok values final → values.length = operands.length) := by
  induction operands generalizing state with
  | nil =>
    exact ⟨_, .nil, Bindings.Preserves.refl _, fun values final equal => by cases equal; rfl⟩
  | cons first rest ih =>
    obtain ⟨out, ran, kept⟩ := operand_total parameter state first
    cases out with
    | error error final => exact ⟨_, .failed ran, kept, fun _ _ impossible => nomatch impossible⟩
    | ok value middle =>
      obtain ⟨out, tail, nextKept, size⟩ := ih middle
      cases out with
      | error error final => exact ⟨_, .next ran tail, kept.trans nextKept, fun _ _ impossible => nomatch impossible⟩
      | ok values final =>
        have count := size values final rfl
        exact ⟨_, .next ran tail, kept.trans nextKept, fun _ _ equal => by cases equal; simp [count]⟩

theorem failed_child_unbound (wrapper : Spec) (admitted : Admitted wrapper) (childId : Nat)
    (caller : State) (argument : Value) {error : Silmaril.Languages.Starlark.Lists.Error} {next : State}
    (failed : Returns wrapper childId caller argument (.error error next)) :
    next.heap[caller.heap.size]? = some ⟨.binding (some argument), false⟩ ∧
    next.heap[caller.heap.size + 1]? = some ⟨.binding none, false⟩ ∧
    next.slots = caller.slots ∧ next.bindings = caller.bindings := by
  cases failed with
  | @failed _ final ran =>
    let active := activate caller (wrapper.frame childId).declaration [] [(fileSlot wrapper.parameter, argument)]
    obtain ⟨out, traced, kept, _⟩ := defaults_total wrapper.parameter active (wrapper.defaults.map Prod.snd)
    have equal := defaults_unique traced ran
    rw [equal] at kept
    obtain ⟨_, parameter, _, child⟩ := frame_layout wrapper admitted childId caller argument
    exact ⟨kept.cells _ _ parameter trivial, kept.cells _ _ child trivial, rfl, rfl⟩

private theorem reached_defaults (program : Program) (available : List DeclarationId) (wrapper : Spec)
    (childId : Nat) (declaration : Declaration) (found : program[childId]? = some declaration)
    (signature : declaration.signature = wrapper.child.parameters.signature wrapper.codes)
    {state : State} {out : Outcome (List Value)}
    (ran : DefaultsIn wrapper.parameter state (wrapper.defaults.map Prod.snd) out) :
    ExecExprs program available state (defaultOperands program childId) out := by
  have ordered : defaultOperands program childId = wrapper.codes := by
    simp [defaultOperands, found, signature, Defaults.signature_defaults, List.map_snd_zip, code_length]
  rw [ordered]
  simpa [Spec.codes, List.map_map, Function.comp_def] using defaults_sound program available ran

private theorem kept_write (state : State) (target : Binding) (value : Value) (address : Nat)
    (owned : state.slots target = some (.owned address)) (key : Nat) (different : key ≠ address) :
    (state.write target value).heap[key]? = state.heap[key]? :=
  RootCall.write_other_cell _ _ _ _ (by simp [owned, Ne.symm different])

/-- The independent wrapper execution supplies both the operational body
and the escaped closure record after the local write and caller restore. -/
theorem returns_with_total (program : Program) (available : List DeclarationId) (wrapper : Spec)
    (admitted : WrapperNames wrapper) (childId : Nat) (declaration : Declaration)
    (found : program[childId]? = some declaration)
    (signature : declaration.signature = wrapper.child.parameters.signature wrapper.codes)
    (caller : State) (argument : Value) (captures : List Silmaril.Languages.Starlark.Lists.Capture)
    (capturesHere : ∀ state : State,
      state.slots (fileSlot wrapper.parameter) = some (.owned caller.heap.size) →
      Installs state declaration.free captures) :
    ∃ out bodyOut, ReturnsWith wrapper childId declaration.free caller argument out ∧
      Exec program available
        (activate caller (wrapper.frame childId).declaration [] [(fileSlot wrapper.parameter, argument)])
        (wrapper.frame childId).code bodyOut ∧ Leaf.returnTo caller bodyOut = out ∧
      (∀ value next, out = .ok value next → ∃ address values,
        value = .function address ∧ values.length = wrapper.child.parameters.optional.length ∧
        next.heap[address]? = some ⟨.function ⟨childId, captures, wrapper.saved values⟩, false⟩ ∧
        next.heap[caller.heap.size]? = some ⟨.binding (some (.scalar (.int wrapper.rebound))), false⟩ ∧
        Bindings.Preserves caller next ∧ (∃ owner, Installs owner declaration.free captures)) := by
  let active := activate caller (wrapper.frame childId).declaration [] [(fileSlot wrapper.parameter, argument)]
  obtain ⟨paramOwn, paramCell, childOwn, childCell⟩ := frame_layout_with wrapper admitted childId caller argument
  obtain ⟨out, ran, kept, count⟩ := defaults_total wrapper.parameter active (wrapper.defaults.map Prod.snd)
  have native := reached_defaults program available wrapper childId declaration found signature ran
  cases out with
  | error error final =>
    exact ⟨_, _, .failed ran, .seqError (.define native), rfl, fun _ _ impossible => nomatch impossible⟩
  | ok values final =>
    have installs := capturesHere final (kept.slots ▸ paramOwn)
    let cell : Cell := ⟨.function ⟨childId, captures, wrapper.saved values⟩, false⟩
    let grown : State := { final with heap := final.heap.push cell }
    let child := fileSlot wrapper.childName
    let parameter := fileSlot wrapper.parameter
    let value : Value := .scalar (.int wrapper.rebound)
    let installed := grown.write child (.function final.heap.size)
    let rebound := installed.write parameter value
    let returned := restoreCaller caller rebound
    have grownKept : Bindings.Preserves active grown := kept.trans (Bindings.Preserves.push final cell)
    have installedSlots : installed.slots = active.slots := (slots_write _ _ _).trans grownKept.slots
    have childAt : grown.slots child = some (.owned (caller.heap.size + 1)) := grownKept.slots ▸ childOwn
    have childStored := grownKept.cells _ _ childCell trivial
    have installedRead : installed.bindingValue child = .ok (.function final.heap.size) :=
      writes_binding grown child _ _ childAt childStored
    have paramAt : installed.slots parameter = some (.owned caller.heap.size) := installedSlots ▸ paramOwn
    have childAfter : installed.slots child = some (.owned (caller.heap.size + 1)) := installedSlots ▸ childOwn
    have reboundRead : rebound.bindingValue child = .ok (.function final.heap.size) := by
      have saved := kept_write installed parameter value caller.heap.size paramAt (caller.heap.size + 1) (by omega)
      simpa only [State.bindingValue, rebound, slots_write, childAfter, Slot.address, saved] using installedRead
    have childCode : Exec program available active (.define child childId) (.ok .next installed) := by
      have actual := Exec.define (target := child) native
      have loaded := Capture.installs_lookup final installs
      simpa [Outcome.resume, define, found, loaded, signature, Defaults.signature_defaults, Spec.saved,
        List.map_fst_zip, code_length, installed, grown, cell] using actual
    have assignCode : Exec program available installed (.assignExpr parameter (.atom (.scalar (.int wrapper.rebound))))
        (.ok .next rebound) :=
      .assignExpr (.evaluates (calls := fun _ _ _ => False) (fun _ _ _ h => h.elim) (.atom trivial .scalar))
    have expression : ExecExpr program available rebound (Leaf.readOperand child)
        (.ok (.function final.heap.size) rebound) := by
      have read : ExecExpr program available rebound (Leaf.readOperand child) (rebound.read (.bound child)) :=
        .evaluates (calls := fun _ _ _ => False) (fun _ _ _ h => h.elim) (.atom trivial .read)
      simpa [State.read, reboundRead] using read
    have body : Exec program available active (wrapper.frame childId).code
        (.ok (.returned (.function final.heap.size)) rebound) :=
      .seq childCode (.seq assignCode (.returnExpr expression))
    refine ⟨_, _, .child ran installs, body, rfl, ?_⟩
    intro result next same
    cases same
    have length : values.length = wrapper.child.parameters.optional.length := by
      simpa [Spec.child] using count values final rfl
    have recordAfter : rebound.heap[final.heap.size]? = some cell :=
      write_keeps_function _ _ _ _ _ _
        (write_keeps_function _ _ _ _ _ _ Array.getElem?_push_size)
    have parameterRetained : installed.heap[caller.heap.size]? = some ⟨.binding (some argument), false⟩ :=
      (kept_write grown child (.function final.heap.size) _ childAt caller.heap.size (by omega)).trans
        (grownKept.cells _ _ paramCell trivial)
    have parameterRebound : rebound.heap[caller.heap.size]? = some ⟨.binding (some value), false⟩ := by
      have within := (Array.getElem?_eq_some_iff.mp parameterRetained).choose
      simp only [rebound, State.write, paramAt, parameterRetained]
      exact Array.getElem?_setIfInBounds_self_of_lt within
    refine ⟨final.heap.size, values, rfl, length, recordAfter, parameterRebound, ⟨rfl, ?_⟩, ⟨final, installs⟩⟩
    intro index stored existing kind
    have low := (Array.getElem?_eq_some_iff.mp existing).choose
    have inFrame := Wrapper.activation_preserves caller (wrapper.frame childId).declaration []
      [(fileSlot wrapper.parameter, argument)] index low
    have inGrown := grownKept.cells index stored (inFrame.trans existing) kind
    have afterChild := kept_write grown child (.function final.heap.size) _ childAt index (by omega)
    have afterRebound := kept_write installed parameter value _ paramAt index (by omega)
    exact afterRebound.trans (afterChild.trans inGrown)

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
  obtain ⟨out, bodyOut, source, ran, restored, result⟩ := returns_with_total program available wrapper
    admitted.wrapperNames childId (wrapper.child.emitted wrapper.codes) found rfl caller argument []
    (fun _ _ => .nil)
  refine ⟨out, bodyOut, ?_, ran, restored, ?_⟩
  · cases source with
    | failed failed => exact .failed failed
    | child evaluated installed =>
      cases installed
      exact .child evaluated
  · intro value state equality
    obtain ⟨address, values, returned, length, cell, rebound, kept, _⟩ := result value state equality
    exact ⟨address, values, returned, length, cell, rebound, kept⟩

theorem returns_with_unique {wrapper : Spec} {childId : Nat} {free : List FreeName}
    {caller : State} {argument : Value} {first second : Outcome Value}
    (a : ReturnsWith wrapper childId free caller argument first)
    (b : ReturnsWith wrapper childId free caller argument second) : first = second := by
  cases a with
  | failed earlier =>
    cases b with
    | failed later => cases defaults_unique earlier later; rfl
    | child later _ => cases defaults_unique earlier later
  | child earlier installed =>
    cases b with
    | failed later => cases defaults_unique earlier later
    | child later installed' =>
      cases defaults_unique earlier later
      have same := Except.ok.inj ((Capture.installs_lookup _ installed).symm.trans (Capture.installs_lookup _ installed'))
      cases same
      rfl

theorem returns_with_sound (program : Program) (available : List DeclarationId) (wrapper : Spec)
    (admitted : WrapperNames wrapper) (childId : Nat) (declaration : Declaration)
    (found : program[childId]? = some declaration)
    (signature : declaration.signature = wrapper.child.parameters.signature wrapper.codes)
    (caller : State) (argument : Value) (captures : List Silmaril.Languages.Starlark.Lists.Capture)
    (capturesHere : ∀ state : State,
      state.slots (fileSlot wrapper.parameter) = some (.owned caller.heap.size) →
      Installs state declaration.free captures)
    {out : Outcome Value} (source : ReturnsWith wrapper childId declaration.free caller argument out) :
    ∃ bodyOut, Exec program available
        (activate caller (wrapper.frame childId).declaration [] [(fileSlot wrapper.parameter, argument)])
        (wrapper.frame childId).code bodyOut ∧ Leaf.returnTo caller bodyOut = out := by
  obtain ⟨_, bodyOut, result, ran, returned, _⟩ := returns_with_total program available wrapper admitted childId
    declaration found signature caller argument captures capturesHere
  exact ⟨bodyOut, ran, returned.trans (returns_with_unique result source)⟩

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

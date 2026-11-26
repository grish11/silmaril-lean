module

public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped.Site
public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Run
public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Frame
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped

open Silmaril.Languages.Starlark (Binding)
open Silmaril.Languages.Starlark.Modules (fileSlot)
open Silmaril.Languages.Starlark.Modules.Resolve.Assignment (LexicalBlock)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Lists (State Value Capture Outcome)

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

theorem activate_installs {globals : List String} {spec : Spec} (plan : Plan globals spec)
    (childId : Nat) (caller : State) (assigned : List (Binding × Value)) :
    let active := activate caller (spec.frame childId).declaration [] assigned
    ∃ captures, Installs active plan.body.free captures ∧ Defaults.Body.CaptureCells active captures := by
  apply install_owned
  intro entry member
  obtain ⟨name, parameter, rfl⟩ := plan.captured entry member
  have declared : name ∈ (spec.frame childId).owned := List.mem_append_left _ parameter
  obtain ⟨address, value, frozen, owned, stored⟩ := Entry.activated_cell caller (spec.frame childId) [] assigned name declared
  exact ⟨name, address, value, frozen, rfl, owned, stored⟩

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

theorem returns_sound {globals : List String} {spec : Spec} (names : Names spec)
    (plan : Plan globals spec) (program : Program) (available : List DeclarationId) (childId : Nat)
    (found : program[childId]? = some (plan.body.declaration spec.wrapper.codes))
    (caller : State) (assigned : List (Binding × Value)) {out : Outcome Value}
    (source : Defaults.Escape.ReturnsWith spec.wrapper childId plan.body.free caller
      (activate caller (spec.frame childId).declaration [] assigned) out) :
    ∃ bodyOut, Exec program available (activate caller (spec.frame childId).declaration [] assigned)
      (spec.frame childId).code bodyOut ∧ Leaf.returnTo caller bodyOut = out := by
  obtain ⟨captures, installed, cells⟩ := activate_installs plan childId caller assigned
  obtain ⟨_, bodyOut, reached, ran, restored, _⟩ := Defaults.Escape.returns_with_total program available spec.wrapper
    names.wrapper childId (plan.body.declaration spec.wrapper.codes) found rfl spec.additional caller assigned
    captures installed cells
  exact ⟨bodyOut, ran, restored.trans (Defaults.Escape.returns_with_unique reached source)⟩

theorem returned_frame {globals : List String} {spec : Spec} (names : Names spec)
    (plan : Plan globals spec) (program : Program) (available : List DeclarationId) (childId : Nat)
    (found : program[childId]? = some (plan.body.declaration spec.wrapper.codes))
    (caller : State) (assigned : List (Binding × Value)) {address : Nat} {next : State}
    (source : Defaults.Escape.ReturnsWith spec.wrapper childId plan.body.free caller
      (activate caller (spec.frame childId).declaration [] assigned) (.ok (.function address) next)) :
    let active := activate caller (spec.frame childId).declaration [] assigned
    ∃ values captures, values.length = spec.child.parameters.optional.length ∧
      Installs active plan.body.free captures ∧
      next.heap[address]? = some ⟨.function ⟨childId, captures, spec.wrapper.saved values⟩, false⟩ ∧
      next.slots = caller.slots ∧ next.bindings = caller.bindings ∧
      (∀ parameter before frozen,
        active.slots (fileSlot spec.wrapper.parameter) = some (.owned parameter) →
        active.heap[parameter]? = some ⟨.binding before, frozen⟩ →
        next.heap[parameter]? = some ⟨.binding (some (.scalar (.int spec.wrapper.rebound))), frozen⟩) ∧
      ∀ arguments : List (Binding × Value),
        Defaults.Body.Frame plan.body.block plan.body.free next.heap.size
          (activate next (plan.body.declaration spec.wrapper.codes) captures arguments) := by
  obtain ⟨captures, installed, live⟩ := activate_installs plan childId caller assigned
  obtain ⟨_, _, independently, _, _, progress⟩ := Defaults.Escape.returns_with_total program available spec.wrapper
    names.wrapper childId (plan.body.declaration spec.wrapper.codes) found rfl spec.additional caller assigned
    captures installed live
  obtain ⟨actual, values, same, count, cell, kept, cells, rebound⟩ :=
    progress _ _ (Defaults.Escape.returns_with_unique independently source)
  cases same
  refine ⟨values, captures, count, installed, cell, kept.slots, ?_, rebound, ?_⟩
  · cases source
    rfl
  · intro arguments
    exact Defaults.Body.captured_frame plan.body _ (Defaults.Escape.code_length spec.wrapper) next _
      captures installed cells arguments

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped

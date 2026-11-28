module

public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Site
public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Wrapper.Heap
public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Entry
public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Forwarding
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body

open Silmaril.Languages.Starlark (Binding)
open Silmaril.Languages.Starlark.Modules (fileSlot globalSlot)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Assignment (LexicalBlock)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Lists (State Capture Value)

theorem root_free {owned globals : List String} {reads : List Binding} {free : List FreeName}
    (selected : Selects ⟨owned, [], globals⟩ reads free) (entry : FreeName) (present : entry ∈ free) :
    ∃ name ∈ globals, entry = ⟨globalSlot name, globalSlot name⟩ := by
  induction selected with
  | nil => cases present
  | owned _ _ ih => exact ih present
  | enclosing origin selection ih =>
    cases origin with
    | enclosing _ impossible => cases impossible
  | module origin _ ih =>
    rcases List.mem_cons.mp present with rfl | later
    · cases origin with
      | module _ _ known => exact ⟨_, known, rfl⟩
    · exact ih later

theorem instantiate_selected {owned globals : List String} {reads : List Binding} {free : List FreeName}
    (selected : Selects ⟨owned, [], globals⟩ reads free) (caller : State) (layout : ModuleSlots globals caller) :
    ∃ captures, Installs caller free captures := by
  apply Forwarding.installs_of_addresses
  intro entry member
  obtain ⟨name, known, rfl⟩ := root_free selected entry member
  obtain ⟨address, _, _, owned, _⟩ := layout.usable name known
  exact ⟨globalSlot name, address, rfl, .inl owned⟩

theorem instantiates {globals : List String} {definition : Definition} (plan : Plan globals definition)
    (caller : State) (layout : ModuleSlots globals caller) :
    ∃ captures, Installs caller plan.free captures :=
  instantiate_selected plan.selects caller layout

/-- The generic frame theorem accepts owned or forwarded captures whose
address has a live binding cell in the current caller heap. -/
theorem activate_frame (block : LexicalBlock) (declaration : Declaration)
    (slots : declaration.signature.slots ++ declaration.locals = block.owned.map fileSlot)
    (caller : State) (captures : List Capture) (assigned : List (Binding × Value))
    (selected : ∀ binding, (⟨binding, binding⟩ : FreeName) ∈ declaration.free →
      binding ∉ declaration.signature.slots ++ declaration.locals ∧
      ∃ capture, captures.find? (fun entry => entry.binding == binding) = some capture ∧
        capture.binding = binding ∧ capture.localCell = (binding.scope == .local) ∧
        ∃ value frozen, caller.heap[capture.address]? = some ⟨.binding value, frozen⟩) :
    Frame block declaration.free caller.heap.size (activate caller declaration captures assigned) := by
  let active := activate caller declaration captures assigned
  have usable := Entry.activate_owned_cells caller declaration captures assigned
  constructor
  · intro name known
    have member : fileSlot name ∈ declaration.signature.slots ++ declaration.locals := by
      rw [slots]
      exact List.mem_map_of_mem known
    obtain ⟨address, owned⟩ := Capture.activate_owned caller declaration captures assigned _ member
    obtain ⟨value, frozen, stored⟩ := usable _ _ owned
    exact ⟨address, value, frozen, Wrapper.activation_fresh caller declaration captures assigned _ _ owned, owned, stored⟩
  · intro binding known
    obtain ⟨outside, capture, found, same, flag, value, frozen, stored⟩ := selected binding known
    have below := (Array.getElem?_eq_some_iff.mp stored).choose
    have own := Capture.activate_capture caller declaration captures capture assigned
      (by simpa only [same] using found) (by simpa only [same] using outside)
    rw [same, flag] at own
    exact ⟨capture.address, value, frozen, below, own,
      (Wrapper.activation_preserves caller declaration captures assigned _ below).trans stored⟩

theorem signature_slots (parameters : Defaults.Parameters) (locals : List String) (codes : List Lowering.Expr)
    (length : codes.length = parameters.optional.length) :
    (parameters.signature codes).slots ++ locals.map fileSlot = (parameters.names ++ locals).map fileSlot := by
  have named := List.map_fst_zip (l₁ := parameters.optional.map (fileSlot ∘ Prod.fst))
    (l₂ := codes) (by simp [length])
  simp [Defaults.Parameters.signature, Defaults.Parameters.names,
    Signature.slots, Signature.named, requiredSignature, List.map_map, Function.comp_def] at named ⊢
  rw [named]

theorem declaration_slots {globals enclosing : List String} {definition : Definition}
    (plan : Plan globals definition enclosing) (codes : List Lowering.Expr)
    (length : codes.length = definition.parameters.optional.length) :
    (plan.declaration codes).signature.slots ++ (plan.declaration codes).locals = plan.block.owned.map fileSlot :=
  signature_slots definition.parameters plan.locals codes length

theorem selected_frame (block : LexicalBlock) (declaration : Declaration)
    (slots : declaration.signature.slots ++ declaration.locals = block.owned.map fileSlot)
    {reads : List Binding} (selected : Selects block reads declaration.free) (caller owner : State)
    (captures : List Capture) (installed : Installs owner declaration.free captures)
    (cells : CaptureCells caller captures) (assigned : List (Binding × Value)) :
    Frame block declaration.free caller.heap.size (activate caller declaration captures assigned) := by
  apply activate_frame _ _ slots
  intro binding known
  refine ⟨?_, ?_⟩
  · rw [slots]
    intro member
    obtain ⟨name, owned, equal⟩ := List.mem_map.mp member
    exact Silmaril.Languages.Starlark.Modules.Resolve.Capture.selected_outside_owned selected _ known name owned equal.symm
  · obtain ⟨capture, found, name, receipt⟩ := Forwarding.find_receipt installed binding known
    have live := cells capture (List.mem_of_find?_eq_some found)
    have flag : capture.localCell = (binding.scope == .local) := by cases receipt <;> rfl
    exact ⟨capture, found, name, flag, live⟩

theorem captured_frame {globals enclosing : List String} {definition : Definition}
    (plan : Plan globals definition enclosing) (codes : List Lowering.Expr)
    (length : codes.length = definition.parameters.optional.length) (caller owner : State)
    (captures : List Capture) (installed : Installs owner plan.free captures)
    (cells : CaptureCells caller captures) (assigned : List (Binding × Value)) :
    Frame plan.block plan.free caller.heap.size (activate caller (plan.declaration codes) captures assigned) :=
  selected_frame plan.block (plan.declaration codes) (declaration_slots plan codes length)
    plan.selects caller owner captures installed cells assigned

theorem selected_cells {owned globals : List String} {reads : List Binding} {free : List FreeName}
    (selected : Selects ⟨owned, [], globals⟩ reads free)
    (caller : State) (layout : ModuleSlots globals caller) (captures : List Capture)
    (installed : Installs caller free captures) :
    CaptureCells caller captures := by
  have received {free : List FreeName} {captures : List Capture} (evidence : Installs caller free captures) :
      ∀ capture ∈ captures, ∃ entry ∈ free, ReceivesAddress caller entry capture := by
    induction evidence with
    | nil => simp
    | cons seen _ ih =>
      intro capture present
      rcases List.mem_cons.mp present with rfl | later
      · exact ⟨_, List.mem_cons_self, seen⟩
      · obtain ⟨entry, known, proof⟩ := ih capture later
        exact ⟨entry, List.mem_cons_of_mem _ known, proof⟩
  intro capture present
  obtain ⟨entry, member, address⟩ := received installed capture present
  obtain ⟨name, known, rfl⟩ := root_free selected entry member
  obtain ⟨index, value, frozen, owned, stored⟩ := layout.usable name known
  cases address with
  | ownedGlobal own =>
    have same := Option.some.inj (own.symm.trans owned)
    cases same
    exact ⟨_, _, stored⟩
  | capturedGlobal counterfeit =>
    rw [owned] at counterfeit
    cases counterfeit

theorem root_capture_cells {globals : List String} {definition : Definition} (plan : Plan globals definition)
    (caller : State) (layout : ModuleSlots globals caller) (captures : List Capture)
    (installed : Installs caller plan.free captures) :
    CaptureCells caller captures :=
  selected_cells plan.selects caller layout captures installed

theorem capture_cells_preserved {state next : State} {captures : List Capture}
    (kept : Bindings.Preserves state next) (cells : CaptureCells state captures) :
    CaptureCells next captures := by
  intro capture present
  obtain ⟨value, frozen, cell⟩ := cells capture present
  exact ⟨value, frozen, kept.cells _ _ cell trivial⟩

theorem capture_cells_written (state : State) (target : Binding) (value : Value)
    {captures : List Capture} (cells : CaptureCells state captures) :
    CaptureCells (state.write target value) captures := by
  intro capture present
  obtain ⟨before, frozen, cell⟩ := cells capture present
  by_cases same : state.slots target = some (.owned capture.address)
  · have valid := (Array.getElem?_eq_some_iff.mp cell).choose
    refine ⟨some value, frozen, ?_⟩
    simp only [State.write, same, cell]
    exact Array.getElem?_setIfInBounds_self_of_lt valid
  · exact ⟨before, frozen, (RootCall.write_other_cell _ _ _ _ same).trans cell⟩

theorem returned_keeps (caller : State) (declaration : Declaration) (captures : List Capture)
    (assigned : List (Binding × Value)) (out : Silmaril.Languages.Starlark.Lists.Outcome
      Silmaril.Languages.Starlark.Lists.Iteration.Flow)
    (kept : Keeps caller.heap.size (activate caller declaration captures assigned)
      (Silmaril.Languages.Starlark.Lists.Iteration.finishState out)) :
    Keeps caller.heap.size caller
      (Silmaril.Languages.Starlark.Lists.Iteration.finishState (Leaf.returnTo caller out)) := by
  have preserved (address : Nat) (cell : Silmaril.Languages.Starlark.Lists.Cell) (low : address < caller.heap.size)
      (stored : caller.heap[address]? = some cell) :
      (Silmaril.Languages.Starlark.Lists.Iteration.finishState out).heap[address]? = some cell := by
    have active := (Wrapper.activation_preserves caller declaration captures assigned address low).trans stored
    exact kept.2 address cell low active
  cases out <;> exact ⟨rfl, preserved⟩

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body

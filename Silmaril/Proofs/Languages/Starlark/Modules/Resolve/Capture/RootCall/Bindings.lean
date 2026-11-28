module

public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall.Operands
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Entry

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall

open Silmaril.Languages.Starlark (Binding)
open Silmaril.Languages.Starlark.Lists (State Address Capture Outcome)
open Silmaril.Languages.Starlark.Modules (Catalog enter globalSlot)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Block (ModuleBinders)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.RootCall
open Silmaril.Languages.Starlark.Functions

local notation "Value" => Silmaril.Languages.Starlark.Lists.Value
local notation "ModuleCode" => Silmaril.Languages.Starlark.Modules.Command

private theorem distinct_after_allocate (names : List Binding) (state : State)
    (distinct : DistinctOwned state)
    (within : ∀ name address, state.slots name = some (.owned address) → address < state.heap.size) :
    DistinctOwned (names.foldl State.allocateSlot state) := by
  induction names generalizing state with
  | nil => exact distinct
  | cons name names ih =>
    have slots (key : Binding) (address : Address)
        (found : (state.allocateSlot name).slots key = some (.owned address)) :
        (key = name ∧ address = state.heap.size) ∨ (key ≠ name ∧ state.slots key = some (.owned address)) := by
      by_cases same : key = name <;> simp_all [State.allocateSlot]
    apply ih
    · intro a b address first second
      rcases slots a address first with ⟨rfl, rfl⟩ | ⟨_, left⟩ <;>
        rcases slots b _ second with ⟨rfl, equal⟩ | ⟨_, right⟩
      · rfl
      · exact (Nat.lt_irrefl _ (within _ _ right)).elim
      · exact (Nat.lt_irrefl _ (equal ▸ within _ _ left)).elim
      · exact distinct _ _ _ left right
    · intro key address found
      rcases slots key address found with ⟨_, rfl⟩ | ⟨_, old⟩
      · simp [State.allocateSlot]
      · simpa [State.allocateSlot] using Nat.lt_succ_of_lt (within _ _ old)

theorem enter_distinct (source : Silmaril.Languages.Starlark.Modules.Source) (caller : State) :
    DistinctOwned (enter source caller) := by
  unfold enter
  exact distinct_after_allocate _ _ (by intro a b address found; cases found)
    (by intro name address found; cases found)

private theorem write_slots (state : State) (binding : Binding) (value : Value) :
    (state.write binding value).slots = state.slots := by
  unfold State.write
  split <;> try rfl
  split <;> rfl

theorem activation_distinct (state : State) (declaration : Declaration)
    (captures : List Capture) (assigned : List (Binding × Value)) :
    DistinctOwned (activate state declaration captures assigned) := by
  have distinctWrites (arguments : List (Binding × Value)) (frame : State) (distinct : DistinctOwned frame) :
      DistinctOwned (arguments.foldl (fun next (binding, value) => next.write binding value) frame) := by
    induction arguments generalizing frame with
    | nil => exact distinct
    | cons argument rest ih =>
      apply ih
      simpa only [DistinctOwned, write_slots] using distinct
  apply distinctWrites
  apply distinct_after_allocate
  · intro a b address owned _
    change capturedSlots captures a = some (.owned address) at owned
    cases found : captures.find? (fun entry => entry.binding == a) <;> simp [capturedSlots, found] at owned
  · intro name address owned
    change capturedSlots captures name = some (.owned address) at owned
    cases found : captures.find? (fun entry => entry.binding == name) <;> simp [capturedSlots, found] at owned

theorem write_other_cell (state : State) (binding : Binding) (value : Value) (address : Address)
    (other : state.slots binding ≠ some (.owned address)) :
    (state.write binding value).heap[address]? = state.heap[address]? := by
  unfold State.write
  split <;> try rfl
  rename_i target slot
  split <;> try rfl
  have diff : target ≠ address := by
    intro same
    exact other (same ▸ slot)
  simp [diff]

theorem activate_unassigned (state : State) (declaration : Declaration) (captures : List Capture)
    (arguments : List (Binding × Value))
    (binding : Binding) (declared : binding ∈ declaration.signature.slots ++ declaration.locals)
    (unassigned : ∀ argument ∈ arguments, argument.1 ≠ binding) :
    let active := activate state declaration captures arguments
    ∃ address, active.slots binding = some (.owned address) ∧ active.heap[address]? = some ⟨.binding none, false⟩ := by
  let initial : State := { state with bindings := fun _ => none, slots := capturedSlots captures }
  let blank := (declaration.signature.slots ++ declaration.locals).foldl State.allocateSlot initial
  obtain ⟨address, owned, stored⟩ := Entry.allocate_blank
    (declaration.signature.slots ++ declaration.locals) initial binding (.inl declared)
  have distinct : DistinctOwned blank := activation_distinct state declaration captures []
  have remains (assigned : List (Binding × Value)) (frame : State)
      (unassigned : ∀ argument ∈ assigned, argument.1 ≠ binding) (separate : DistinctOwned frame)
      (slot : frame.slots binding = some (.owned address)) (cell : frame.heap[address]? = some ⟨.binding none, false⟩) :
      let reached := assigned.foldl (fun current (target, value) => current.write target value) frame
      reached.slots binding = some (.owned address) ∧ reached.heap[address]? = some ⟨.binding none, false⟩ := by
    induction assigned generalizing frame with
    | nil => exact ⟨slot, cell⟩
    | cons argument rest ih =>
      have different : frame.slots argument.1 ≠ some (.owned address) :=
        fun same => unassigned argument List.mem_cons_self (separate _ _ _ same slot)
      have atNext := write_slots frame argument.1 argument.2
      exact ih _ (fun arg member => unassigned arg (List.mem_cons_of_mem _ member))
        (by simpa only [DistinctOwned, atNext] using separate) (atNext ▸ slot)
        ((write_other_cell frame argument.1 argument.2 address different).trans cell)
  exact ⟨address, remains arguments blank unassigned distinct owned stored⟩

private theorem write_function_cell (state : State) (binding : Binding) (value : Value)
    (address : Address) (closure : Silmaril.Languages.Starlark.Lists.Closure) (frozen : Bool)
    (cell : state.heap[address]? = some ⟨.function closure, frozen⟩) :
    (state.write binding value).heap[address]? = some ⟨.function closure, frozen⟩ := by
  by_cases owner : state.slots binding = some (.owned address)
  · simp [State.write, owner, cell]
  · exact (write_other_cell state binding value address owner).trans cell

theorem write_keeps_live (state : State) (name destination : String) (value : Value)
    {address : Address} {id : Nat} {captures : List Capture} {frozen : Bool} {defaults : List (Binding × Value)}
    (distinct : DistinctOwned state) (live : Live state name address id captures frozen defaults)
    (unrelated : destination ≠ name) :
    DistinctOwned (state.write (globalSlot destination) value) ∧
      Live (state.write (globalSlot destination) value) name address id captures frozen defaults := by
  obtain ⟨⟨owner, slot⟩, read, cell⟩ := live
  have other : state.slots (globalSlot destination) ≠ some (.owned owner) := by
    intro found
    exact unrelated (congrArg Binding.name (distinct _ _ _ found slot))
  have same := write_slots state (globalSlot destination) value
  refine ⟨by simpa only [DistinctOwned, same] using distinct, ⟨⟨owner, same ▸ slot⟩, ?_, ?_⟩⟩
  simpa only [State.bindingValue, same, slot, Silmaril.Languages.Starlark.Lists.Slot.address,
    write_other_cell state _ value owner other] using read
  exact write_function_cell state _ value _ _ _ cell

theorem writes_run_and_keep (program : Program) (host : Catalog)
    {globals : List String} {name : String} {state final : State}
    {source : List Command} {code : List ModuleCode}
    {address : Address} {id : Nat} {captures : List Capture} {frozen : Bool}
    (writes : Writes globals name state source code final)
    (distinct : DistinctOwned state) (live : Live state name address id captures frozen) :
    Silmaril.Languages.Starlark.Modules.Runs program host state code (.ok () final) ∧
      DistinctOwned final ∧ Live final name address id captures frozen := by
  induction writes with
  | nil => exact ⟨.done, distinct, live⟩
  | @cons state final destination operand code value rest commands unrelated related evaluated writes ih =>
    have ⟨nextDistinct, nextLive⟩ := write_keeps_live state name destination value distinct live unrelated
    obtain ⟨later, finalDistinct, finalLive⟩ := ih nextDistinct nextLive
    have rhs := evaluates_operand program (List.range program.size) (fun _ _ _ => False) related evaluated
    have assignment : Exec program (List.range program.size) state (.assignExpr (globalSlot destination) code)
        (.ok .next (state.write (globalSlot destination) value)) :=
      .assignExpr (.evaluates (fun _ _ _ impossible => impossible.elim) rhs)
    have step : Silmaril.Languages.Starlark.Modules.Executes program host state
        (.exec (.assignExpr destination code)) (.ok () (state.write (globalSlot destination) value)) :=
      .exec (code := .assignExpr destination code) assignment
    exact ⟨.step step later, finalDistinct, finalLive⟩

private theorem defined_slots (program : Program) (state next : State) (target : Binding) (id : Nat)
    (created : define program target id [] state = .ok .next next) : next.slots = state.slots := by
  unfold define at created
  split at created <;> try contradiction
  split at created <;> try contradiction
  cases created
  exact write_slots _ _ _

private theorem definition_declared {commands : List Command} {globals : List String} (chain : Forwarding.Chain)
    (binders : ModuleBinders commands globals)
    (site : Command.define chain.name (.required chain.parameters) chain.body ∈ commands) :
    chain.name ∈ globals := by
  induction binders with
  | nil => cases site
  | cons first rest ih =>
    rcases List.mem_cons.mp site with rfl | later
    · cases first
      exact List.mem_append_left _ List.mem_cons_self
    · exact List.mem_append_right _ (ih later)

theorem root_live {commands : List Command} {globals : List String}
    {linked : Program} {resolved : ResolvedModule} {chain : Forwarding.Chain}
    {head : Forwarding.Frame} {frames : List Forwarding.Frame}
    (binders : ModuleBinders commands globals) (checked : resolve commands linked = .ok resolved)
    (emits : Forwarding.Emits globals [] chain (head :: frames))
    (site : Command.define chain.name (.required chain.parameters) chain.body ∈ commands)
    (caller : State) (id : Nat) (found : resolved.program[id]? = some head.declaration) :
    let initial := enter resolved.source caller
    ∃ next captures,
      Exec resolved.program (List.range resolved.program.size) initial (.define (globalSlot chain.name) id) (.ok .next next) ∧
      DistinctOwned next ∧ Live next chain.name initial.heap.size id captures false := by
  let initial := enter resolved.source caller
  obtain ⟨next, captures, _, ran, read, cell⟩ := Entry.checked_root_definition binders checked emits site caller id found
  have defaults : defaultOperands resolved.program id = [] := by
    simp [defaultOperands, found, Forwarding.Frame.declaration, requiredSignature, Signature.defaulted, Signature.named,
      List.filterMap_map]
  have created : define resolved.program (globalSlot chain.name) id [] initial = .ok .next next := by
    simpa [run, denoteBody, defaults, pure, EStateM.pure, Outcome.resume] using ran
  have same := defined_slots _ _ _ _ _ created
  obtain ⟨address, owner, _⟩ := Entry.checked_global_cell binders checked caller chain.name (definition_declared chain binders site)
  exact ⟨next, captures, (exec_iff_denoteBody _ _ _ _ _).mpr ran,
    by simpa only [DistinctOwned, same] using enter_distinct resolved.source caller,
    ⟨⟨address, same ▸ owner⟩, read, cell⟩⟩

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall

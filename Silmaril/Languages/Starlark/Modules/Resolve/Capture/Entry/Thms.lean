module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Entry.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Forwarding.Thms
public import Silmaril.Languages.Starlark.Modules.Resolve.Thms
public import Silmaril.Languages.Starlark.Functions.Thms
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Entry

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Entry

open Lists (Address Capture State)
open Functions
open Block (ModuleBinders)
open Forwarding (Chain Emits)

/-- Every declared parameter or local has a live owned cell after activation,
including after writing the bound arguments. -/
theorem activated_cell (state : State) (frame : Forwarding.Frame) (captures : List Capture)
    (arguments : List (Binding × Lists.Value)) (name : String) (declared : name ∈ frame.owned) :
    let active := activate state frame.declaration captures arguments
    ∃ address value frozen, active.slots (fileSlot name) = some (.owned address) ∧
      active.heap[address]? = some ⟨.binding value, frozen⟩ :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Entry.activated_cell
    state frame captures arguments name declared

/-- The checked global list agrees with independent load-free binder collection. -/
theorem checked_module_globals {commands : List Command} {globals : List String}
    {linked : Program} {resolved : ResolvedModule}
    (declares : ModuleBinders commands globals) (checked : resolve commands linked = .ok resolved) :
    resolved.source.globals = globals :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Entry.checked_module_globals
    declares checked

theorem entered_cells (source : Modules.Source) (caller : State) :
    (∀ binding address, (enter source caller).slots binding = some (.owned address) → caller.heap.size ≤ address) ∧
    ∀ (address : Nat) cell, caller.heap[address]? = some cell → (enter source caller).heap[address]? = some cell :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Entry.entered_cells source caller

theorem entered_blank (source : Modules.Source) (caller : State) (binding : Binding)
    (declared : binding ∈ source.globals.map globalSlot ++ source.fileNames.map fileSlot) :
    ∃ address, (enter source caller).slots binding = some (.owned address) ∧
      (enter source caller).heap[address]? = some ⟨.binding none, false⟩ :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Entry.entered_blank source caller binding declared

/-- Module entry allocates an uninitialized owned cell for each declared global. -/
theorem checked_global_cell {commands : List Command} {globals : List String}
    {linked : Program} {resolved : ResolvedModule}
    (declares : ModuleBinders commands globals) (checked : resolve commands linked = .ok resolved)
    (caller : State) (name : String) (global : name ∈ globals) :
    ∃ address, (enter resolved.source caller).slots (globalSlot name) = some (.owned address) ∧
      (enter resolved.source caller).heap[address]? = some ⟨.binding none, false⟩ :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Entry.checked_global_cell
    declares checked caller name global

/-- Module entry distinguishes a declared but uninitialized name from an absent name. -/
theorem checked_global_read {commands : List Command} {globals : List String}
    {linked : Program} {resolved : ResolvedModule}
    (declares : ModuleBinders commands globals) (checked : resolve commands linked = .ok resolved)
    (caller : State) (name : String) (global : name ∈ globals) :
    (enter resolved.source caller).bindingValue (globalSlot name) = .error (.uninitialized (globalSlot name)) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Entry.checked_global_read
    declares checked caller name global

/-- Every list of evaluated positional actuals gives a binding result. -/
theorem binds_total (names : List String) (values : List Lists.Value) : ∃ result, Binds names values result :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Entry.binds_total
    names values

/-- The independent required-positional rules compute exactly the checked binder result. -/
theorem required_binds {names : List String} {values : List Lists.Value}
    {result : Except Lists.Error (List (Binding × Lists.Value))}
    (checked : (requiredSignature names).validate = .ok ()) (binds : Binds names values result) :
    bindArguments (requiredSignature names) [] ⟨values, []⟩ =
      result.map (fun assigned => ⟨assigned, [], []⟩) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Entry.required_binds
    checked binds

/-- Checked intake validates every signature in the final declaration table. -/
theorem checked_signature {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) (declaration : Declaration) (index : Nat)
    (found : resolved.program[index]? = some declaration) : declaration.signature.validate = .ok () :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Entry.checked_signature checked declaration index found

/-- Checked module intake validates the signature of each declaration table entry.
For required positional calls, preparation follows the independent binding result.
The availability premise is the finite call descent guard. -/
theorem checked_prepare {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) (available : List DeclarationId) (frame : Forwarding.Frame)
    (id : DeclarationId) (permitted : id ∈ available) (state : State) (address : Address)
    (captures : List Capture) (frozen : Bool) (values : List Lists.Value)
    (result : Except Lists.Error (List (Binding × Lists.Value)))
    (stored : state.heap[address]? = some ⟨.function ⟨id, captures, []⟩, frozen⟩)
    (found : resolved.program[id]? = some frame.declaration) (binds : Binds frame.parameters values result) :
    prepareExpanded resolved.program available ⟨values, []⟩ (.function address) state =
      match result with
      | .ok assigned => .ok (.closure ⟨id, permitted, frame.code⟩) (activate state frame.declaration captures assigned)
      | .error error => .error error state :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Entry.checked_prepare
    checked available frame id permitted state address captures frozen values result stored found binds

/-- Instantiate a root declaration at module entry. The declarative binders and
capture plan supply the destination and capture addresses. -/
theorem checked_root_definition {commands : List Command} {globals : List String}
    {linked : Program} {resolved : ResolvedModule} {chain : Chain} {head : Forwarding.Frame} {rest : List Forwarding.Frame}
    (declares : ModuleBinders commands globals) (checked : resolve commands linked = .ok resolved)
    (emitted : Emits globals [] chain (head :: rest))
    (site : Command.define chain.name (.required chain.parameters) chain.body ∈ commands)
    (caller : State) (id : Nat) (found : resolved.program[id]? = some head.declaration) :
    let initial := enter resolved.source caller
    ∃ next captures, Installs initial head.free captures ∧
      run resolved.program (.define (globalSlot chain.name) id) initial = .ok .next next ∧
      next.bindingValue (globalSlot chain.name) = .ok (.function initial.heap.size) ∧
      next.heap[initial.heap.size]? = some ⟨.function ⟨id, captures, []⟩, false⟩ :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Entry.checked_root_definition
    declares checked emitted site caller id found

/-- Continue directly from a root definition to call preparation. The table
lookup supplies initial availability and independent binding supplies the
activation arguments. Actual operand evaluation is a separate step. -/
theorem checked_root_dispatch {commands : List Command} {globals : List String}
    {linked : Program} {resolved : ResolvedModule} {chain : Chain} {head : Forwarding.Frame} {rest : List Forwarding.Frame}
    (declares : ModuleBinders commands globals) (checked : resolve commands linked = .ok resolved)
    (emitted : Emits globals [] chain (head :: rest))
    (site : Command.define chain.name (.required chain.parameters) chain.body ∈ commands)
    (caller : State) (id : Nat) (found : resolved.program[id]? = some head.declaration)
    {values : List Lists.Value} {result : Except Lists.Error (List (Binding × Lists.Value))}
    (binds : Binds head.parameters values result) :
    let initial := enter resolved.source caller
    let available := List.range resolved.program.size
    ∃ next captures, ∃ permitted : id ∈ available,
      Installs initial head.free captures ∧
      Exec resolved.program available initial (.define (globalSlot chain.name) id) (.ok .next next) ∧
      next.bindingValue (globalSlot chain.name) = .ok (.function initial.heap.size) ∧
      prepareExpanded resolved.program available ⟨values, []⟩ (.function initial.heap.size) next =
        match result with
        | .ok assigned =>
          .ok (.closure ⟨id, permitted, head.code⟩) (activate next head.declaration captures assigned)
        | .error error => .error error next :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Entry.checked_root_dispatch
    declares checked emitted site caller id found binds

/-- Reading an uninitialized declared global at entry fails with the entry frame
and heap. The proof constructs the resolved operational derivation and uses adequacy. -/
theorem checked_entry_read_error {commands : List Command} {globals : List String}
    {linked : Program} {resolved : ResolvedModule}
    (declares : ModuleBinders commands globals) (checked : resolve commands linked = .ok resolved)
    (caller : State) (name : String) (global : name ∈ globals) :
    let initial := enter resolved.source caller
    run resolved.program (.evalExpr (.atom (.read (.bound (globalSlot name))))) initial =
      .error (.uninitialized (globalSlot name)) initial :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Entry.checked_entry_read_error
    declares checked caller name global

/-- If the first normalized command reads a declared global, execution
reaches its uninitialized cell and restores the caller with the entry heap. -/
theorem checked_first_read_error {rest : List Command} {globals : List String} {name : String}
    {linked : Program} {resolved : ResolvedModule}
    (declares : ModuleBinders (.eval (.scalar (.read name)) :: rest) globals)
    (checked : resolve (.eval (.scalar (.read name)) :: rest) linked = .ok resolved)
    (legal : name.toList.head? ≠ some '$') (global : name ∈ globals)
    (host : Catalog) (caller : State) :
    let initial := enter resolved.source caller
    runModule (.eval (.scalar (.read name)) :: rest) host caller linked =
      .ok (.error (.runtime (.uninitialized (globalSlot name)))
        (restoreThread caller initial)) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Entry.checked_first_read_error
    declares checked legal global host caller

/-- The same first-command failure has a derivation in the module rules. -/
theorem first_read_initializes {rest : List Command} {globals : List String} {name : String}
    {linked : Program} {resolved : ResolvedModule}
    (declares : ModuleBinders (.eval (.scalar (.read name)) :: rest) globals)
    (checked : resolve (.eval (.scalar (.read name)) :: rest) linked = .ok resolved)
    (legal : name.toList.head? ≠ some '$') (global : name ∈ globals)
    (host : Catalog) (caller : State) :
    Initializes (.eval (.scalar (.read name)) :: rest) host caller linked
      (.ok (.error (.runtime (.uninitialized (globalSlot name)))
        (restoreThread caller (enter resolved.source caller)))) :=
  (initializes_iff_runModule _ _ _ _ _).mpr (checked_first_read_error declares checked legal global host caller)

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Entry

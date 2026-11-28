module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Forwarding.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Thms
public import Mathlib.Data.List.Chain
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Forwarding

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Forwarding

open Functions (Program FreeName activate)
open Lists (State Address)

/-- Flattening the lexical context preserves existence of an owner. The
declarative lookup records which enclosing block owns the name. -/
theorem nearest_iff (name : String) (outer : List (List String)) :
    name ∈ outer.flatten ↔ ∃ distance, Nearest name outer distance :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Forwarding.nearest_iff name outer

/-- The actual compiler emits the independently selected declaration at
each level. Its table appends child definitions before their parents. -/
theorem compile_chain {globals : List String} {program : Program}
    {outer : List (List String)} {chain : Chain} (accepted : Accepted globals program outer chain) :
    ∃ head rest, Emits globals outer chain (head :: rest) ∧
      compileBody (parentContext globals outer) chain.definition program =
        .ok (⟨.define (fileSlot chain.name) (EmittedProgram program rest).size, head.free.map FreeName.source⟩,
          EmittedProgram program (head :: rest)) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Forwarding.compile_chain accepted

/-- Compilation also records the child ID actually used by each wrapper. -/
theorem compile_chain_linked {globals : List String} {program : Program}
    {outer : List (List String)} {chain : Chain} (accepted : Accepted globals program outer chain) :
    ∃ head rest, Emits globals outer chain (head :: rest) ∧ Links program chain (head :: rest) ∧
      compileBody (parentContext globals outer) chain.definition program =
        .ok (⟨.define (fileSlot chain.name) (EmittedProgram program rest).size, head.free.map FreeName.source⟩,
          EmittedProgram program (head :: rest)) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Forwarding.compile_chain_linked accepted

/-- Compilation identifies the lexical block used by the emitted leaf. -/
theorem compile_chain_scoped {globals : List String} {program : Program}
    {outer : List (List String)} {chain : Chain} (accepted : Accepted globals program outer chain) :
    ∃ head rest, Emits globals outer chain (head :: rest) ∧ Links program chain (head :: rest) ∧
      ScopedLeaves globals outer chain (head :: rest) ∧
      compileBody (parentContext globals outer) chain.definition program =
        .ok (⟨.define (fileSlot chain.name) (EmittedProgram program rest).size, head.free.map FreeName.source⟩,
          EmittedProgram program (head :: rest)) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Forwarding.compile_chain_scoped accepted

theorem emitted_declaration (program : Program) (frames : List Frame) (frame : Frame)
    (present : frame ∈ frames) : ∃ id : Nat, (EmittedProgram program frames)[id]? = some frame.declaration :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Forwarding.emitted_declaration program frames frame present

/-- A root in a load-free module captures only declared globals. -/
theorem root_capture {globals : List String} {chain : Chain} {head : Frame} {rest : List Frame}
    (emitted : Emits globals [] chain (head :: rest)) (entry : FreeName) (present : entry ∈ head.free) :
    ∃ name ∈ globals, entry = reference (globalSlot name) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Forwarding.root_capture emitted entry present

theorem passes_along {globals : List String} {outer : List (List String)}
    {chain : Chain} {frames : List Frame} (emitted : Emits globals outer chain frames) :
    frames.IsChain Passes :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Forwarding.passes_along emitted

theorem scoped_frames {globals : List String} {outer : List (List String)} {chain : Chain}
    {frames : List Frame} (emitted : Emits globals outer chain frames) :
    ∀ frame ∈ frames, frame.WellScoped :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Forwarding.scoped_frames emitted

/-- A leaf's local capture appears at each intervening definition up to
its nearest owner. An owner in the chain supplies its own slot. -/
theorem nearest_route {globals : List String} {outer : List (List String)} {chain : Chain}
    {frames : List Frame} {name : String} {distance : Nat}
    (emitted : Emits globals outer chain frames)
    (demand : ∀ leaf ∈ frames.getLast?, reference (fileSlot name) ∈ leaf.free)
    (nearest : Nearest name (frames.reverse.map Frame.owned ++ outer) distance) :
    LocalRoute name outer frames.reverse distance :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Forwarding.nearest_route emitted demand nearest

theorem forwarded_prefix {name : String} {outer : List (List String)} {frames : List Frame} {distance : Nat}
    (route : LocalRoute name outer frames distance) :
    ∀ frame ∈ frames.take distance, reference (fileSlot name) ∈ frame.free ∧ name ∉ frame.owned :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Forwarding.forwarded_prefix route

/-- A resolved module-global reference is carried by every declaration
between the module and the leaf. -/
theorem global_route {globals : List String} {outer : List (List String)} {chain : Chain}
    {frames : List Frame} (emitted : Emits globals outer chain frames) (name : String)
    (demand : ∀ leaf ∈ frames.getLast?, reference (globalSlot name) ∈ leaf.free) :
    ∀ frame ∈ frames, reference (globalSlot name) ∈ frame.free :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Forwarding.global_route emitted name demand

theorem installs_of_addresses (state : State) (free : List FreeName)
    (addresses : ∀ entry ∈ free, ∃ binding address, entry = reference binding ∧ HasAddress state binding address) :
    ∃ captures, Installs state free captures :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Forwarding.installs_of_addresses state free addresses

/-- Lookup in the installed vector recovers the defining-frame receipt. -/
theorem find_receipt {state : State} {free : List FreeName} {captures : List Lists.Capture}
    (installed : Installs state free captures) (binding : Binding) (present : reference binding ∈ free) :
    ∃ capture, captures.find? (fun entry => entry.binding == binding) = some capture ∧
      capture.binding = binding ∧ ReceivesAddress state (reference binding) capture :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Forwarding.find_receipt installed binding present

/-- Allocating the parent's frame supplies all its child's capture slots.
The parent receives its own free addresses as input. -/
theorem child_installs (parent child : Frame) (owner current : State)
    (captures : List Lists.Capture) (arguments : List (Binding × Lists.Value))
    (installed : Installs owner parent.free captures) (connected : Passes parent child)
    (childScoped : child.WellScoped) :
    ∃ received, Installs (activate current parent.declaration captures arguments) child.free received :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Forwarding.child_installs parent child owner current
    captures arguments installed connected childScoped

/-- An owned definition target and installed captures suffice for creation
and activation of a frame in the invocation path. -/
theorem invoke_frame (program : Program) (frame : Frame) (id : Nat) (state : State) (target : Binding)
    (address : Address) (before : Option Lists.Value) (frozen : Bool)
    (captures : List Lists.Capture) (arguments : List (Binding × Lists.Value))
    (found : program[id]? = some frame.declaration) (installed : Installs state frame.free captures)
    (owned : state.slots target = some (.owned address))
    (cell : state.heap[address]? = some ⟨.binding before, frozen⟩) :
    ∃ created, Invokes program state [frame] (activate created frame.declaration captures arguments) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Forwarding.invoke_frame program frame id state target
    address before frozen captures arguments found installed owned cell

theorem invokes_append {program : Program} {start middle finish : State} {first rest : List Frame}
    (firstRun : Invokes program start first middle) (suffix : Invokes program middle rest finish) :
    Invokes program start (first ++ rest) finish :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Forwarding.invokes_append firstRun suffix

/-- The defining slot's address survives every creation and activation on
the forwarding prefix, from the nearest owner toward the leaf. -/
theorem local_address {program : Program} {owner final : State} {frames : List Frame}
    {name : String} {outer : List (List String)} {distance : Nat}
    (route : LocalRoute name outer frames distance)
    (invoked : Invokes program owner (frames.take distance).reverse final) (address : Address)
    (initial : HasAddress owner (fileSlot name) address) :
    HasAddress final (fileSlot name) address ∧
      ((frames.take distance).reverse ≠ [] → final.slots (fileSlot name) = some (.captured address true)) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Forwarding.local_address route invoked address initial

/-- The module address survives each forwarding step with its global tag. -/
theorem global_address {program : Program} {owner final : State} {frames : List Frame}
    {globals : List String} {outer : List (List String)} {chain : Chain}
    (emitted : Emits globals outer chain frames) (name : String)
    (demand : ∀ leaf ∈ frames.getLast?, reference (globalSlot name) ∈ leaf.free)
    (invoked : Invokes program owner frames final) (address : Address)
    (initial : HasAddress owner (globalSlot name) address) :
    HasAddress final (globalSlot name) address ∧
      (frames ≠ [] → final.slots (globalSlot name) = some (.captured address false)) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Forwarding.global_address emitted name demand
    invoked address initial

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Forwarding

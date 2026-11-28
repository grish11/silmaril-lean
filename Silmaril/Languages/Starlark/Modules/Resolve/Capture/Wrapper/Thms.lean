module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Wrapper.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.RootCall.Thms
public import Silmaril.Languages.Starlark.Modules.Thms
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Wrapper.Commands
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Wrapper.Heap

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Wrapper

open Functions
open Lists (Address Capture Outcome State)
open Forwarding (Chain Emits Links EmittedProgram Accepted)
open Block (ModuleBinders)
open Assignment (InOrder)

local notation "ClosureFrame" => Forwarding.Frame
local notation "NormalizedExpr" => Functions.Lowering.Resolve.SourceExpr

/-- A leading root definition reaches its checked command and allocates
the live closure with the addresses supplied by fresh module entry. -/
theorem checked_root_object (after : List Command) (chain : Chain) (globals : List String)
    (linked : Program) (resolved : ResolvedModule)
    (binders : ModuleBinders (.define chain.name (.required chain.parameters) chain.body :: after) globals)
    (checked : resolve (.define chain.name (.required chain.parameters) chain.body :: after) linked = .ok resolved)
    (accepted : ∀ program, Accepted globals program [] chain)
    (suffix : RootCall.Segment globals after) (caller : State) :
    let initial := enter resolved.source caller
    ∃ seed head rest next captures, Emits globals [] chain (head :: rest) ∧ Links seed chain (head :: rest) ∧
      KeepsTable seed resolved.program (head :: rest) ∧
      resolved.source.commands[0]? = some (.exec (.define chain.name (EmittedProgram seed rest).size)) ∧
      Exec resolved.program (List.range resolved.program.size) initial
        (.define (globalSlot chain.name) (EmittedProgram seed rest).size) (.ok .next next) ∧
      next.bindingValue (globalSlot chain.name) = .ok (.function initial.heap.size) ∧
      ClosureAt next initial.heap.size (EmittedProgram seed rest).size head captures false :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Wrapper.checked_root_object
    after chain globals linked resolved binders checked accepted suffix caller

/-- Each wrapper activation supplies the addresses for the child it defines. -/
theorem wrapper_total {seed : Program} {globals : List String} {outer : List (List String)}
    {name : String} {params : List String} {child : Chain} {frame childFrame : ClosureFrame} {rest : List ClosureFrame}
    (emits : Emits globals outer (.wrapper name params child) (frame :: childFrame :: rest))
    (caller : State) (captures : List Capture) (assigned : List (Binding × Lists.Value))
    (environment : ∃ owner, Installs owner frame.free captures) :
    ∃ selected, ReturnsChild seed caller child frame childFrame rest captures assigned selected
      (.ok (.function (activate caller frame.declaration captures assigned).heap.size)
        (restoreCaller caller (installChild (activate caller frame.declaration captures assigned)
          child.name (EmittedProgram seed rest).size selected))) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Wrapper.wrapper_total
    emits caller captures assigned environment

/-- The independent source wrapper returns the allocated child address.
The exact body execution and post-restoration child cell follow from
its lexical layout and the checked declaration entries. -/
theorem wrapper_body {seed program : Program} {name : String} {params : List String}
    {caller : State} {child : Chain} {frame childFrame : ClosureFrame} {rest : List ClosureFrame}
    {captures selected : List Capture} {assigned : List (Binding × Lists.Value)}
    {nextAddress : Address} {next : State} (available : List DeclarationId)
    (links : Links seed (.wrapper name params child) (frame :: childFrame :: rest))
    (keeps : KeepsTable seed program (frame :: childFrame :: rest))
    (returns : ReturnsChild seed caller child frame childFrame rest captures assigned selected
      (.ok (.function nextAddress) next)) :
    let active := activate caller frame.declaration captures assigned
    ∃ final, Exec program available active frame.code (.ok (.returned (.function nextAddress)) final) ∧
      next = restoreCaller caller final ∧
      ClosureAt next nextAddress (EmittedProgram seed rest).size childFrame selected false :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Wrapper.wrapper_body
    available links keeps returns

/-- A bounded sequence of evaluated positional calls admits a wrapper path.
Its result is either the surviving escaped closure or a binding error. -/
theorem walk_total {seed program : Program} {globals : List String} {outer : List (List String)}
    {state : State} {chain : Chain} {frame : ClosureFrame} {rest : List ClosureFrame}
    {address : Address} {captures : List Capture} {frozen : Bool}
    (emits : Emits globals outer chain (frame :: rest)) (links : Links seed chain (frame :: rest))
    (keeps : KeepsTable seed program (frame :: rest))
    (closure : ClosureAt state address (EmittedProgram seed rest).size frame captures frozen)
    (operands : List (List Lists.Value)) (bounded : operands.length ≤ rest.length) :
    ∃ out, Walk seed state chain (frame :: rest) address captures operands out :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Wrapper.walk_total
    emits links keeps closure operands bounded

/-- Each invocation on that path agrees with resolved preparation, body
execution, and restoration. No resolved body execution is a premise. -/
theorem checked_walk {seed : Program} {commands : List Command} {linked : Program}
    {resolved : ResolvedModule} {globals : List String} {outer : List (List String)} {state : State}
    {chain : Chain} {frame : ClosureFrame} {rest : List ClosureFrame} {address : Address} {captures : List Capture}
    {frozen : Bool} {operands : List (List Lists.Value)} {out : Outcome Lists.Value}
    (checked : resolve commands linked = .ok resolved)
    (emits : Emits globals outer chain (frame :: rest)) (links : Links seed chain (frame :: rest))
    (keeps : KeepsTable seed resolved.program (frame :: rest))
    (closure : ClosureAt state address (EmittedProgram seed rest).size frame captures frozen)
    (walk : Walk seed state chain (frame :: rest) address captures operands out) :
    NativeWalk resolved.program state address operands out :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Wrapper.checked_walk
    checked emits links keeps closure walk

/-- The existing call and body denotations yield the exact same outcome
for each resolved wrapper path. -/
theorem native_walk_denotes {program : Program} {state : State} {address : Address}
    {operands : List (List Lists.Value)} {out : Outcome Lists.Value}
    (native : NativeWalk program state address operands out) :
    denoteWalk program operands (.function address) state = out :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Wrapper.native_walk_denotes
    native

/-- At the actual checked command position, evaluate a call to a named
wrapper and assign its escaped child. A binding failure skips the write. -/
theorem checked_wrapper_assignment {seed : Program} {before after : List Command} {linked : Program}
    {resolved : ResolvedModule} {globals : List String} {outer : List (List String)} {name wrapperName : String} {parameters : List String}
    {child : Chain} {frame childFrame : ClosureFrame} {rest : List ClosureFrame} {state : State}
    {address : Address} {captures : List Capture} {frozen : Bool}
    {positional : List NormalizedExpr} {actuals : List Lowering.Expr} {values : List Lists.Value}
    (destination : String)
    (binders : ModuleBinders
      (before ++ .assign destination (.call (.scalar (.read name)) positional [] none none) :: after) globals)
    (checked : resolve (before ++ .assign destination (.call (.scalar (.read name)) positional [] none none) :: after)
      linked = .ok resolved)
    (callee : RootCall.Operand globals (.scalar (.read name)) (.atom (.read (.bound (globalSlot name)))))
    (arguments : InOrder (RootCall.Operand globals) positional actuals)
    (evaluated : RootCall.EvaluatesOperands state positional (.ok values state))
    (binding : state.bindingValue (globalSlot name) = .ok (.function address))
    (emits : Emits globals outer (.wrapper wrapperName parameters child) (frame :: childFrame :: rest))
    (links : Links seed (.wrapper wrapperName parameters child) (frame :: childFrame :: rest))
    (keeps : KeepsTable seed resolved.program (frame :: childFrame :: rest))
    (closure : ClosureAt state address (EmittedProgram seed (childFrame :: rest)).size frame captures frozen)
    (host : Modules.Catalog) :
    ∃ code out, resolved.source.commands[before.length]? = some code ∧
      Modules.Executes resolved.program host state code out ∧
      ((∃ error, Entry.Binds frame.parameters values (.error error) ∧ out = .error (.runtime error) state) ∨
        (∃ assigned selected nextAddress next,
          Entry.Binds frame.parameters values (.ok assigned) ∧
          ReturnsChild seed state child frame childFrame rest captures assigned selected (.ok (.function nextAddress) next) ∧
          out = .ok () (next.write (globalSlot destination) (.function nextAddress)) ∧
          ClosureAt (next.write (globalSlot destination) (.function nextAddress))
            nextAddress (EmittedProgram seed rest).size childFrame selected false)) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Wrapper.checked_wrapper_assignment
    destination binders checked callee arguments evaluated binding emits links keeps closure host

/-- A reached operand error in an assigned call skips invocation and
leaves the destination untouched with the operand's residual state. -/
theorem checked_assignment_operand_error {before after : List Command} {linked : Program} {resolved : ResolvedModule}
    {globals : List String} {callee : NormalizedExpr} {positional : List NormalizedExpr}
    {function : Lowering.Expr} {actuals : List Lowering.Expr} {state final : State}
    {error : Lists.Error}
    (destination : String)
    (binders : ModuleBinders (before ++ .assign destination (.call callee positional [] none none) :: after) globals)
    (checked : resolve (before ++ .assign destination (.call callee positional [] none none) :: after) linked =
      .ok resolved)
    (related : RootCall.Operand globals callee function)
    (arguments : InOrder (RootCall.Operand globals) positional actuals)
    (evaluated : RootCall.EvaluatesOperands state (callee :: positional) (.error error final))
    (host : Modules.Catalog) :
    ∃ code, resolved.source.commands[before.length]? = some code ∧
      Modules.Executes resolved.program host state code (.error (.runtime error) final) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Wrapper.checked_assignment_operand_error
    destination binders checked related arguments evaluated host

/-- Compose the reached source steps at their checked indices. After a
reached error the resolved suffix remains unevaluated. -/
theorem prefix_sound {SourceCommand : Type}
    {step : Nat → State → SourceCommand → Modules.Result Unit → Prop}
    (program : Program) (host : Modules.Catalog) (code : List Modules.Command)
    (sound : ∀ index state command out, step index state command out →
      ∃ compiled, code[index]? = some compiled ∧ Modules.Executes program host state compiled out)
    {index : Nat} {state : State} {source : List SourceCommand} {out : Modules.Result Unit}
    (reached : ReachedPrefix step index state source out) :
    Modules.Runs program host state ((code.drop index).take source.length) out :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Wrapper.prefix_sound
    program host code sound reached

/-- Transfer a complete reached source derivation to checked module
execution and its denotation, using the existing publication or error
restoration boundary. -/
theorem checked_finish {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    {step : Nat → State → Command → Modules.Result Unit → Prop}
    (checked : resolve commands linked = .ok resolved) (host : Modules.Catalog) (caller : State)
    (sound : ∀ index state command out, step index state command out →
      ∃ compiled, resolved.source.commands[index]? = some compiled ∧
        Modules.Executes resolved.program host state compiled out)
    {out : Modules.Result Unit} (reached : ReachedPrefix step 0 (enter resolved.source caller) commands out) :
    Initializes commands host caller linked (.ok (finish resolved.source caller out)) ∧
      runModule commands host caller linked = .ok (finish resolved.source caller out) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Wrapper.checked_finish
    checked host caller sound reached

/-- Activating a declaration keeps every earlier cell in the heap. -/
theorem activation_preserves (caller : State) (declaration : Declaration)
    (captures : List Capture) (assigned : List (Binding × Lists.Value)) (index : Nat)
    (low : index < caller.heap.size) :
    (activate caller declaration captures assigned).heap[index]? = caller.heap[index]? :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Wrapper.activation_preserves
    caller declaration captures assigned index low

/-- Activation and a local write leave pre-existing heap addresses intact. -/
theorem activated_write_preserves (caller : State) (frame : Forwarding.Frame) (captures : List Capture)
    (assigned : List (Binding × Lists.Value)) (target : Binding) (value : Lists.Value) (index : Nat)
    (low : index < caller.heap.size) :
    ((activate caller frame.declaration captures assigned).write target value).heap[index]? = caller.heap[index]? :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Wrapper.activated_write_preserves
    caller frame captures assigned target value index low

/-- A successful wrapper call preserves the caller slots and every cell
that was in the heap before activation. -/
theorem returned_preserves {seed : Program} {caller : State}
    {child : Chain} {frame childFrame : ClosureFrame}
    {rest : List ClosureFrame} {captures selected : List Capture} {assigned : List (Binding × Lists.Value)}
    {address : Address} {next : State}
    (returned : ReturnsChild seed caller child frame childFrame rest captures assigned selected
      (.ok (.function address) next)) :
    next.slots = caller.slots ∧
      ∀ index, index < caller.heap.size → next.heap[index]? = caller.heap[index]? :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Wrapper.returned_preserves
    returned

/-- An owned target from the caller can hold the escaped closure after the
wrapper finishes. Reading the target yields the new closure address. -/
theorem returned_assigns {seed : Program} {caller : State}
    {child : Chain} {frame childFrame : ClosureFrame}
    {rest : List ClosureFrame} {captures selected : List Capture} {assigned : List (Binding × Lists.Value)}
    {address : Address} {next : State}
    (returned : ReturnsChild seed caller child frame childFrame rest captures assigned selected
      (.ok (.function address) next))
    (destination : Binding) (slot : Address) (before : Option Lists.Value) (frozen : Bool)
    (owned : caller.slots destination = some (.owned slot))
    (cell : caller.heap[slot]? = some ⟨.binding before, frozen⟩) :
    (next.write destination (.function address)).bindingValue destination = .ok (.function address) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Wrapper.returned_assigns
    returned destination slot before frozen owned cell

/-- Starting from a checked leading definition in a fresh module frame,
derive the exact wrapper path and its denotation. Actual values are inputs. -/
theorem checked_root_walk (after : List Command) (chain : Chain) (globals : List String)
    (linked : Program) (resolved : ResolvedModule)
    (binders : ModuleBinders (.define chain.name (.required chain.parameters) chain.body :: after) globals)
    (checked : resolve (.define chain.name (.required chain.parameters) chain.body :: after) linked = .ok resolved)
    (accepted : ∀ program, Accepted globals program [] chain)
    (suffix : RootCall.Segment globals after) (caller : State)
    (operands : List (List Lists.Value)) (bounded : operands.length ≤ wrapperCount chain) :
    let initial := enter resolved.source caller
    ∃ seed head rest next captures out,
      resolved.source.commands[0]? = some (.exec (.define chain.name (EmittedProgram seed rest).size)) ∧
      Exec resolved.program (List.range resolved.program.size) initial
        (.define (globalSlot chain.name) (EmittedProgram seed rest).size) (.ok .next next) ∧
      Walk seed next chain (head :: rest) initial.heap.size captures operands out ∧
      NativeWalk resolved.program next initial.heap.size operands out ∧
      denoteWalk resolved.program operands (.function initial.heap.size) next = out :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Wrapper.checked_root_walk
    after chain globals linked resolved binders checked accepted suffix caller operands bounded

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Wrapper

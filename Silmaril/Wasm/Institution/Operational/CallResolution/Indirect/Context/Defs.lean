module

public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Native.Defs
public import Silmaril.Wasm.SingleThreaded.Determinism.Head

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context

open Execution
open Execution.Runtime (Frame FuncAddr Value)
open CallContinuation.OuterCall (CallTarget)
open CallContinuation.OuterCall.Ranked
open CallContinuation.OuterCall.Ranked.Graph (Function Program)
open CallContinuation.OuterCall.Computed
open Wasm.Lime1.Execution (values)
open Wasm.SingleThreaded.Det (noHost)

/-- Data shared by the two native readings of one indirect invocation. -/
structure Invocation where
  site : Site
  caller : Frame
  selector : BitVec 32
  saved : List Value
  args : List Value
  address : FuncAddr
  callee : Function

structure Invocation.Checked (call : Invocation) (program : Program) : Prop where
  graph : program.checkDirect = true
  site : call.site.check program call.caller = true
  resolved : call.site.resolve program call.selector = some (.resolved call.address)
  found : program.lookup call.address = some call.callee
  typed : call.args.map Value.type = call.site.signature.params

/-- The graph renderer shares the direct-call descriptor. Its index is unused
after resolution, and the caller need not have a function at that index. -/
def Invocation.target (call : Invocation) : CallTarget :=
  ⟨⟨0⟩, call.address, call.callee.declaration⟩

def Invocation.entered (call : Invocation) : Graph.Phase :=
  .label (call.callee.declaration.frame call.args).locals (.running call.callee.initial call.callee.code)

def Invocation.coreCallee {H : Type} (call : Invocation) (s : Core.Store H)
    (rest : List Core.Admin) (phase : Graph.Phase) : Core.Config H :=
  ⟨s, call.caller.toCore, Core.vals (call.saved.map Value.toCore) ++ phase.render Graph.coreAdmin call.target ++ rest⟩

def Invocation.limeCallee {H : Type} (call : Invocation) (s : Wasm.Lime1.Execution.Store H)
    (rest : List Wasm.Lime1.Execution.Admin) (phase : Graph.Phase) : Wasm.Lime1.Execution.Config H :=
  ⟨s, call.caller, values call.saved ++ phase.render Graph.limeAdmin call.target ++ rest⟩

def Invocation.corePrefix {H : Type} (call : Invocation) (s : Core.Store H)
    (rest : List Core.Admin) : List (Core.Config H) :=
  ((Outcome.resolved call.address).coreTrace.map
    (coreConfig s call.caller call.site call.selector (call.saved ++ call.args) rest)) ++
    [call.coreCallee s rest call.entered]

def Invocation.limePrefix {H : Type} (call : Invocation) (s : Wasm.Lime1.Execution.Store H)
    (rest : List Wasm.Lime1.Execution.Admin) : List (Wasm.Lime1.Execution.Config H) :=
  [limeSource s call.caller call.site call.selector (call.saved ++ call.args) rest,
    limeResolved s call.caller (call.saved ++ call.args) rest (.resolved call.address),
    call.limeCallee s rest call.entered]

def Invocation.coreTrap {H : Type} (call : Invocation) (s : Core.Store H)
    (stack : List Value) (rest : List Core.Admin) : Core.Config H :=
  ⟨s, call.caller.toCore, Core.vals (stack.map Value.toCore) ++ .trap :: rest⟩

def Invocation.limeTrap {H : Type} (call : Invocation) (s : Wasm.Lime1.Execution.Store H)
    (stack : List Value) (rest : List Wasm.Lime1.Execution.Admin) : Wasm.Lime1.Execution.Config H :=
  ⟨s, call.caller, values stack ++ .trap :: rest⟩

/-- A step during callee execution has the entered frame at the hole in the
fixed caller context. The step that removes the frame delivers the outcome. -/
def Invocation.coreFrameStep {H : Type} (call : Invocation) (P : Numerics.Profile)
    (rest : List Core.Admin) (a b : Core.Config H) : Prop :=
  (∃ n f body, a.code = Core.vals (call.saved.map Value.toCore) ++ .frame n f body :: rest) ∧
    Core.Step P noHost a b

def Invocation.limeFrameStep {H : Type} (call : Invocation)
    (rest : List Wasm.Lime1.Execution.Admin) (a b : Wasm.Lime1.Execution.Config H) : Prop :=
  (∃ n f body, a.code = values call.saved ++ .frame n f body :: rest) ∧
    Wasm.Lime1.Execution.Step CallFrame.limeNoHost a b

/-- Finite native endpoints are in the resolution/entry prefix, under the
callee frame, at the handoff to the caller, or in native trap cleanup.
The frame guard bounds the execution on successful handoff. -/
def NativeRun {C : Type} (native frameStep : C → C → Prop) (entryTrace : List C)
    (entered trapped out : C) : Prop :=
  entryTrace.IsChain (fun a b => ∀ dst, native a dst ↔ dst = b) ∧
    (out ∈ entryTrace ∨ Relation.ReflTransGen frameStep entered out ∨
      (Relation.ReflTransGen frameStep entered trapped ∧ Relation.ReflTransGen native trapped out))

abbrev Invocation.CoreRun {H : Type} (call : Invocation) (P : Numerics.Profile)
    (s : Core.Store H) (rest : List Core.Admin) (out : Core.Config H) : Prop :=
  NativeRun (Core.Step P noHost) (call.coreFrameStep P rest) (call.corePrefix s rest)
    (call.coreCallee s rest call.entered) (call.coreTrap s call.saved rest) out

abbrev Invocation.LimeRun {H : Type} (call : Invocation)
    (s : Wasm.Lime1.Execution.Store H) (rest : List Wasm.Lime1.Execution.Admin)
    (out : Wasm.Lime1.Execution.Config H) : Prop :=
  NativeRun (Wasm.Lime1.Execution.Step CallFrame.limeNoHost) (call.limeFrameStep rest)
    (call.limePrefix s rest) (call.limeCallee s rest call.entered) (call.limeTrap s call.saved rest) out

/-- The corresponding endpoints reuse graph runs and the existing trap
discard rule. A successful return hands control back with the pending code
intact. -/
def Invocation.Run {A C : Type} (call : Invocation) (program : Program) (rest : List A)
    (entryTrace : List C) (render : Graph.Phase → C) (trap : List Value → List A → C) (out : C) : Prop :=
  out ∈ entryTrace ∨
    (∃ phase, program.FrameRuns call.address call.entered phase ∧
      Graph.Admitted program call.callee phase ∧ out = render phase) ∨
    (program.FrameRuns call.address call.entered (.done .trap) ∧
      ∃ kept remaining, Relation.ReflTransGen
        (fun (a b : List Value × List A) => Prefix.Discard a.1 a.2 b.1 b.2)
        (call.saved, rest) (kept, remaining) ∧ out = trap kept remaining)

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context

module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Host.Body.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Host.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.HostBody

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32

open Execution.Runtime (EvalCtx Frame MemAddr MemInst Value)
open Computed
open Wasm.V1.Execution

/-- A successful numeric step preserves the check for any typed continuation. -/
theorem check_prefix_preserves {locals stack next : List Value} {op : Prefix.Op}
    {rest : List Prefix.Op} {signature : Wasm.V1.FuncType} {resume : List NumType → Bool}
    (checked : checkHostPrefixWith (locals.map Value.type) (Prefix.stackTypes stack) (op :: rest) signature resume = true)
    (move : Prefix.Reduce locals stack op (.values next)) :
    checkHostPrefixWith (locals.map Value.type) (Prefix.stackTypes next) rest signature resume = true :=
  HostProofs.check_prefix_preserves checked move

/-- The graph continuation receives result types above the actual saved stack. -/
theorem check_prefix_resume {locals : List NumType} {saved args : List Value}
    {signature : Wasm.V1.FuncType} {resume : List NumType → Bool}
    (checked : checkHostPrefixWith locals (Prefix.stackTypes (saved ++ args)) [] signature resume = true)
    (typed : args.map Value.type = signature.params) :
    resume (signature.results.reverse ++ Prefix.stackTypes saved) = true :=
  HostProofs.check_prefix_resume checked typed

/-- The exhausted prefix exposes the ordered argument suffix and its typed continuation. -/
theorem check_prefix_arguments {locals : List NumType} {stack : List Value}
    {signature : Wasm.V1.FuncType} {resume : List NumType → Bool}
    (checked : checkHostPrefixWith locals (Prefix.stackTypes stack) [] signature resume = true) :
    ∃ saved args, stack = saved ++ args ∧ args.map Value.type = signature.params ∧
      resume (signature.results.reverse ++ Prefix.stackTypes saved) = true :=
  HostProofs.check_prefix_arguments checked

/-- Typed parameters and initialized defaults establish the active local types. -/
theorem HostPrefixTyped.entry {fn : Function} {args stack : List Value} {ops : List Prefix.Op}
    {signature : Wasm.V1.FuncType} {tail : List Op} {fallthrough : List NumType}
    {labels : List (List NumType)} (parameters : args.map Value.type = fn.declaration.params)
    (checked : fn.checkHostPrefix (Prefix.stackTypes stack) ops signature tail fallthrough labels = true) :
    HostPrefixTyped fn (fn.declaration.frame args) stack ops signature tail fallthrough labels :=
  HostProofs.prefix_entry parameters checked

/-- Successful numeric steps preserve the checked host suffix and its region continuation. -/
theorem HostPrefixTyped.preserve {fn : Function} {caller : Frame} {stack next : List Value}
    {op : Prefix.Op} {rest : List Prefix.Op} {signature : Wasm.V1.FuncType}
    {tail : List Op} {fallthrough : List NumType} {labels : List (List NumType)}
    (typed : HostPrefixTyped fn caller stack (op :: rest) signature tail fallthrough labels)
    (move : Prefix.Reduce caller.locals stack op (.values next)) :
    HostPrefixTyped fn caller next rest signature tail fallthrough labels :=
  HostProofs.prefix_preserves typed move

/-- At the reached site, split the actual operand stack into saved operands and
ordered host arguments. Typed delivery reestablishes the graph region check. -/
theorem HostPrefixTyped.arguments {H : Type} {fn : Function} {caller : Frame} {stack : List Value}
    {site : HostCall.V1.Site H} {s : Store H} {tail : List Op}
    {fallthrough : List NumType} {labels : List (List NumType)}
    (typed : HostPrefixTyped fn caller stack [] site.signature tail fallthrough labels)
    (linked : fn.declaration.module.funcs[site.index.toNat]? = some site.address)
    (allocated : s.funcs[site.address.value]? = some (.host site.signature site.target))
    (scalar : site.signature.results.length ≤ 1) :
    ∃ saved args, stack = saved ++ args ∧ site.Checked s caller args ∧
      ∀ payload : List Value, payload.map Value.type = site.signature.results →
        fn.checkRegion (Prefix.stackTypes (saved ++ payload)) fallthrough tail labels = true :=
  HostProofs.host_arguments typed linked allocated scalar

/-- A numeric prefix head takes exactly its existing step under any embedding.
A prefix trap is delivered before the source call can resolve. -/
theorem v1_host_prefix_step_iff {H : Type} {host : HostSemantics H} {s : Store H} {caller : Frame}
    {stack : List Value} {op : Prefix.Op} {tail : List Admin} {dst : Config H} :
    Step host ⟨s, caller, values stack ++ Prefix.emit v1Syntax op :: tail⟩ dst ↔
      ∃ out, Prefix.Reduce caller.locals stack op out ∧
        dst = ⟨s, caller, Prefix.outcomeCode values .trap tail out⟩ :=
  HostProofs.prefix_step_iff

/-- Pending host delivery under entered labels and frames is exactly a declared
return, including a trap with its store, or a declared divergence self-step. -/
theorem v1_host_pending_step_iff {H : Type} {host : HostSemantics H} {site : HostCall.V1.Site H}
    {s : Store H} {outer : Frame} {k : EvalCtx Wasm.V1.Instr} {saved args : List Value}
    {tail : List Admin} {dst : Config H} (checked : site.Checked s (k.activeFrame outer) args) :
    Step host ⟨s, outer, k.plug value (site.pending s (k.activeFrame outer) saved args tail).code⟩ dst ↔
      (∃ s' r, host site.target s args (.returned s' r) ∧
        dst = ⟨s', outer, k.plug value (HostCall.V1.resumed s' (k.activeFrame outer) saved tail r).code⟩) ∨
      (host site.target s args .diverged ∧
        dst = ⟨s, outer, k.plug value (site.pending s (k.activeFrame outer) saved args tail).code⟩) :=
  HostProofs.host_pending_step_iff checked

/-- Existing ready graph code cannot park at a host callout. -/
theorem ReadyFor.internal_iff {H : Type} {host : HostSemantics H} {mode : MemoryMode}
    {program : Program} {memory : MemAddr} {calls : CallMode} {base : Store H}
    {initial : MemInst} (layout : Layout program base memory initial) {state : State} {rank : Nat}
    (ready : ReadyFor mode program memory calls rank initial.data.size state) {dst : Config H} :
    Step host (render base memory initial state) dst ↔
      Internal (render base memory initial state) dst :=
  HostProofs.ready_internal_iff layout ready

/-- An admitted host-free continuation keeps its finite graph correspondence
in any host embedding. -/
theorem v1_graph_run_with_host_iff {H : Type} {host : HostSemantics H} {mode : MemoryMode} {calls : CallMode}
    {program : Program} {memory : MemAddr} {base : Store H} {initial : MemInst}
    (checked : program.checkV1 memory mode calls = true) (layout : Layout program base memory initial)
    (matched : mode.matches initial) {src : State} {rank : Nat}
    (ready : ReadyFor mode program memory calls rank initial.data.size src) {dst : Config H} :
    Steps host (render base memory initial src) dst ↔
      ∃ out, RunsAt mode program memory src out ∧ ReadyFor mode program memory calls rank initial.data.size out ∧
        dst = render base memory initial out :=
  HostProofs.ready_run_iff checked layout matched ready

/-- An arbitrary finite prefix from the reached host invocation either ends at
the invocation or follows one declared return into a checked continuation.
The surrounding context must preserve the graph guard for the delivered code. -/
theorem v1_host_graph_run_iff {H : Type} {host : HostSemantics H} {site : HostCall.V1.Site H}
    {mode : MemoryMode} {calls : CallMode} {program : Program} {memory : MemAddr}
    {base : Store H} {initial : MemInst} {bytes : ByteArray}
    (checked : program.checkV1 memory mode calls = true) (layout : Layout program base memory initial)
    (matched : mode.matches initial) (extent : mode.extent initial.data.size bytes)
    {k : EvalCtx Wasm.V1.Instr} {outer : Frame} {saved args : List Value} {tail : List Admin}
    {rank outerRank : Nat}
    (siteChecked : site.Checked (storeWithBytes base memory initial bytes) (k.activeFrame outer) args)
    (contract : site.ReturnContract host (HostStoreEffect mode memory initial)
      (storeWithBytes base memory initial bytes) args)
    (tailAllowed : CodeAllowedFor mode program memory calls rank (k.activeFrame outer).module tail)
    (wrap : ∀ code, CodeAllowedFor mode program memory calls rank (k.activeFrame outer).module code →
      CodeAllowedFor mode program memory calls outerRank outer.module (k.plug value code))
    {dst : Config H} :
    let live := storeWithBytes base memory initial bytes
    let pending : Config H := ⟨live, outer, k.plug value (site.pending live (k.activeFrame outer) saved args tail).code⟩
    Steps host pending dst ↔ dst = pending ∨
      ∃ s' r next out, host site.target live args (.returned s' r) ∧
        HostCall.V1.ResultTyped site.signature.results r ∧
        s' = storeWithBytes base memory initial next ∧ bytes.size ≤ next.size ∧
        ReadyFor mode program memory calls outerRank initial.data.size
          ⟨next, outer, k.plug value (values saved ++ result r ++ tail)⟩ ∧
        RunsAt mode program memory ⟨next, outer, k.plug value (values saved ++ result r ++ tail)⟩ out ∧
        ReadyFor mode program memory calls outerRank initial.data.size out ∧ dst = render base memory initial out :=
  HostProofs.host_graph_run_iff checked layout matched extent siteChecked contract tailAllowed wrap

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32

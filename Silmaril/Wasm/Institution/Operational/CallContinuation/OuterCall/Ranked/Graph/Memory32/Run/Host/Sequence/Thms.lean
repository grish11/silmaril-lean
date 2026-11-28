module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Host.Sequence.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.HostSequence
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.HostControl

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.HostEntry.Sequence

open Execution.Runtime (EvalCtx Frame MemAddr MemInst Result Value)
open Wasm.V1.Execution

variable {H : Type} {seq : Sequence H} {host : HostSemantics H} {mode : MemoryMode}
  {program : Program} {memory : MemAddr} {calls : CallMode} {base : Store H} {initial : MemInst}
  {start : ByteArray} {outer : Frame} {args : List Value} {source : Source H}

/-- Exact reduction at the innermost label with every enclosing stack prefix
and continuation retained. The source checker supplies these labels as the
control path is entered. -/
theorem v1_label_context_iff {H : Type} {host : HostSemantics H} {s : Store H} {outer : Frame}
    (seq : Sequence H) (args : List Value) (labels : List (OpenLabel H)) {body : List Admin} {dst : Config H} :
    Step host ⟨s, outer, (seq.context args labels).plug value body⟩ dst ↔
      ∃ nextStore nextFrame code,
        Step host ⟨s, outer, [.frame (OpenLabel.labelArity seq.root.function labels) (seq.root.function.declaration.frame args)
          [.label (OpenLabel.labelArity seq.root.function labels) (seq.labelCode labels) body]]⟩
          ⟨nextStore, outer, [.frame (OpenLabel.labelArity seq.root.function labels) nextFrame code]⟩ ∧
        dst = ⟨nextStore, outer, [.frame seq.root.function.declaration.results.length nextFrame
          ((seq.insert labels).plug value code)]⟩ :=
  ControlProofs.scoped_step seq args labels

/-- A contracted return restores the live store and the checked continuation.
A value result feeds the next segment. A trap retains the returned bytes
through cleanup of the remaining code. -/
theorem return_ready (checked : seq.Checked mode program memory calls base outer args source)
    (layout : Layout program base memory initial) (contract : seq.Contract host mode memory initial base source)
    {bytes : ByteArray} {saved actual : List Value} {site : HostCall.V1.Site H}
    {later : List (HostSegment H)} {labels : List (OpenLabel H)} {tail : Option (Source H)} {after : Store H} {r : Execution.Runtime.Result}
    (ready : seq.Ready mode program memory calls initial (.pending bytes saved actual site later labels tail) source)
    (returned : host site.target (storeWithBytes base memory initial bytes) actual (.returned after r)) :
    ∃ next, after = storeWithBytes base memory initial next ∧ bytes.size ≤ next.size ∧ HostCall.V1.ResultTyped site.signature.results r ∧
      Layout program after memory { initial with data := next } ∧
      seq.Ready mode program memory calls initial (seq.delivered outer args next saved later r labels tail) source :=
  Proofs.return_ready checked layout contract ready returned

/-- The typed continuation and live-store invariant is preserved by each edge. -/
theorem Edge.ready (graphChecked : program.checkV1 memory mode calls = true)
    (checked : seq.Checked mode program memory calls base outer args source)
    (layout : Layout program base memory initial) (extent : mode.extent initial.data.size start)
    (contract : seq.Contract host mode memory initial base source) {src dst : Phase H}
    (edge : seq.Edge host mode program memory base initial start outer args src dst)
    (ready : seq.Ready mode program memory calls initial src source) :
    seq.Ready mode program memory calls initial dst source :=
  Proofs.preserves graphChecked checked layout extent contract edge ready

/-- The checked loop target carries no branch payload, even when normal
fallthrough delivers a scalar result. -/
theorem loop_restart_payload {bytes : ByteArray} {stack saved : List Value} {results : List NumType}
    {result : Option NumType} {region tail : Source H} {skipped : List Admin} {rest : List (OpenLabel H)}
    (ready : seq.Ready mode program memory calls initial
      (.branching bytes stack ⟨⟨0⟩, results⟩ skipped (.loop saved region tail result :: rest)) source) : results = [] := by
  have found : some [] = some results := (decide_eq_true_eq.mp ready.2.1).1
  exact (Option.some.inj found).symm

/-- Normal completion delivers exactly the checked result above the saved
operands, in the active frame with the current Memory32. -/
theorem v1_loop_fallthrough_iff {bytes : ByteArray} {saved stack : List Value} {result : Option NumType}
    {region tail : Source H} {labels : List (OpenLabel H)} {dst : Config H}
    (ready : seq.Ready mode program memory calls initial (.completed bytes stack (.loop saved region tail result) labels) source) :
    Step host (seq.render base memory initial start outer args (.completed bytes stack (.loop saved region tail result) labels)) dst ↔
      stack.map Value.type = result.toList ∧
        dst = seq.render base memory initial start outer args (seq.beginBody outer args bytes (saved ++ stack) labels tail) :=
  Proofs.loop_fallthrough_step ready

/-- A depth-zero branch to a live parameterless loop reinstalls its source loop under
the same frame and enclosing operands. Opening the label is a later step. -/
theorem v1_loop_restart_iff {bytes : ByteArray} {stack saved : List Value} {results : List NumType}
    {result : Option NumType} {region tail : Source H} {skipped : List Admin} {rest : List (OpenLabel H)} {dst : Config H} :
    Step host (seq.render base memory initial start outer args
      (.branching bytes stack ⟨⟨0⟩, results⟩ skipped (.loop saved region tail result :: rest))) dst ↔
      dst = seq.render base memory initial start outer args (.loop bytes saved region tail rest result) :=
  Proofs.loop_restart_step

/-- At depth zero in the implicit label, the native branch erases the
scratch operands and skipped suffix. The typed payload is still inside the
frame, which the native frame-completion step later removes. -/
theorem v1_function_branch_step_iff {bytes : ByteArray} {stack : List Value}
    {results : List NumType} {skipped : List Admin} {dst : Config H}
    (ready : seq.Ready mode program memory calls initial (.branching bytes stack ⟨⟨0⟩, results⟩ skipped []) source) :
    Step host (seq.render base memory initial start outer args (.branching bytes stack ⟨⟨0⟩, results⟩ skipped [])) dst ↔
      ∃ extra payload, stack = extra ++ payload ∧ payload.map Value.type = seq.root.function.declaration.results ∧
        dst = ⟨storeWithBytes base memory initial bytes, outer, seq.afterLabel args [] (values payload)⟩ :=
  Proofs.function_branch_typed ready

/-- Exact successors preserve native resolution, delivery and cleanup steps
for every reached site. -/
theorem v1_step_iff (graphChecked : program.checkV1 memory mode calls = true)
    (checked : seq.Checked mode program memory calls base outer args source)
    (layout : Layout program base memory initial) (matched : mode.matches initial)
    (extent : mode.extent initial.data.size start) (contract : seq.Contract host mode memory initial base source)
    {src : Phase H} (ready : seq.Ready mode program memory calls initial src source) {dst : Config H} :
    Step host (seq.render base memory initial start outer args src) dst ↔
      ∃ next, seq.Edge host mode program memory base initial start outer args src next ∧
        seq.Ready mode program memory calls initial next source ∧ dst = seq.render base memory initial start outer args next :=
  Proofs.step_iff graphChecked checked layout matched extent contract ready

/-- Trap cleanup cannot resume a host computation. It discards labels and
their continuations until the remaining code can run in the host-free graph. -/
theorem trapped_run {bytes : ByteArray} {saved : List Value} {tail : List Admin} {labels : List (OpenLabel H)} {dst : Phase H}
    (run : seq.Runs host mode program memory base initial start outer args (.trapped bytes saved tail labels) dst) :
    (∃ saved rest scopes, dst = .trapped bytes saved rest scopes) ∨ ∃ state, dst = .graph state :=
  Proofs.trapped_run run

/-- Finite endpoint correspondence through any number of source sites. -/
theorem v1_run_iff (graphChecked : program.checkV1 memory mode calls = true)
    (checked : seq.Checked mode program memory calls base outer args source)
    (layout : Layout program base memory initial) (matched : mode.matches initial)
    (extent : mode.extent initial.data.size start) (contract : seq.Contract host mode memory initial base source)
    {src : Phase H} (ready : seq.Ready mode program memory calls initial src source) {dst : Config H} :
    Steps host (seq.render base memory initial start outer args src) dst ↔
      ∃ next, seq.Runs host mode program memory base initial start outer args src next ∧
        seq.Ready mode program memory calls initial next source ∧ dst = seq.render base memory initial start outer args next :=
  Proofs.run_iff graphChecked checked layout matched extent contract ready

/-- The checked sequence starts at the ordinary source call. No entered frame
or pending callout is supplied. -/
theorem v1_call_run_iff (graphChecked : program.checkV1 memory mode calls = true)
    (checked : seq.Checked mode program memory calls base outer args source)
    (layout : Layout program base memory initial) (matched : mode.matches initial)
    (extent : mode.extent initial.data.size start) (contract : seq.Contract host mode memory initial base source)
    {dst : Config H} :
    Steps host ⟨storeWithBytes base memory initial start, outer, values args ++ [.source (.call seq.root.index)]⟩ dst ↔
      ∃ next, seq.Runs host mode program memory base initial start outer args (.call source) next ∧
        seq.Ready mode program memory calls initial next source ∧ dst = seq.render base memory initial start outer args next :=
  v1_run_iff (src := .call source) graphChecked checked layout matched extent contract rfl

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.HostEntry.Sequence

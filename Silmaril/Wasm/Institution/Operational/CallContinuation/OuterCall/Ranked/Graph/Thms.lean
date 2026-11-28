module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Rules
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Typing

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph

open Execution.Runtime (FuncAddr Value)

/-- Recover the ordered operand suffix selected by the top-first stack check. -/
theorem SuffixTyped.split {stack : List Value} {params : List NumType}
    (typed : SuffixTyped params stack) :
    ∃ saved args, stack = saved ++ args ∧ args.map Value.type = params :=
  Proofs.split_suffix typed

theorem Program.lookup_table (program : Program) (address : FuncAddr) :
    program.table.lookup address = (program.lookup address).map Function.entry :=
  Proofs.lookup_table program address

theorem Program.target_resolved {program : Program} (checked : program.check = true)
    {address : FuncAddr} {fn : Function} {target : CallTarget}
    (found : program.lookup address = some fn) (used : target ∈ fn.targets) :
    program.order target.address address :=
  Proofs.target_resolved checked found used

/-- Unfold exactly one activation. Recursive premises refer to the same
judgment at the target address, where rank descent is already justified. -/
theorem Program.edgeAt_iff {program : Program} (checked : program.check = true)
    {address : FuncAddr} {fn : Function} {a b : Phase} {kind : LabelKind} (found : program.lookup address = some fn) :
    program.EdgeAt checked address kind a b ↔
      Layer fn (fun target => program.Edge checked target.address) a b kind :=
  Proofs.edge_iff checked found

theorem Program.edge_iff {program : Program} (checked : program.check = true)
    {address : FuncAddr} {fn : Function} {a b : Phase} (found : program.lookup address = some fn) :
    program.Edge checked address a b ↔
      Layer fn (fun target => program.Edge checked target.address) a b :=
  program.edgeAt_iff checked found

/-- Every successor while a call is active comes from exactly one step of its
child. The parent's saved operands and continuation are carried by `attach`. -/
theorem Program.activeAt_iff {program : Program} (checked : program.check = true)
    {address : FuncAddr} {fn : Function} (found : program.lookup address = some fn)
    {target : CallTarget} (used : target ∈ fn.targets) {a : Phase} (live : a.Active)
    {locals saved : List Value} {rest : List Op} {b : Phase} {kind : LabelKind} :
    program.EdgeAt checked address kind (.label locals (.active saved target a rest)) b ↔
      ∃ out, program.Edge checked target.address a out ∧ b = .label locals (Body.attach saved target rest out) :=
  Proofs.active_iff checked found used live

theorem Program.active_iff {program : Program} (checked : program.check = true)
    {address : FuncAddr} {fn : Function} (found : program.lookup address = some fn)
    {target : CallTarget} (used : target ∈ fn.targets) {a : Phase} (live : a.Active)
    {locals saved : List Value} {rest : List Op} {b : Phase} :
    program.Edge checked address (.label locals (.active saved target a rest)) b ↔
      ∃ out, program.Edge checked target.address a out ∧ b = .label locals (Body.attach saved target rest out) :=
  program.activeAt_iff checked found used live

theorem Program.lift_child {program : Program} (checked : program.check = true)
    {address : FuncAddr} {fn : Function} (found : program.lookup address = some fn)
    {target : CallTarget} (used : target ∈ fn.targets) {a b : Phase} (live : a.Active)
    {locals saved : List Value} {rest : List Op} (run : program.Runs checked target.address a b) :
    program.Runs checked address (.label locals (.active saved target a rest))
      (.label locals (Body.attach saved target rest b)) :=
  Proofs.lift_child checked found used live run

/-- Resolve the checked direct call, run its child, and deliver the child's
ordered values or trap to the caller's unchanged continuation. -/
theorem Program.compose_call {program : Program} (checked : program.check = true)
    {address : FuncAddr} {fn : Function} (found : program.lookup address = some fn)
    {target : CallTarget} (used : target ∈ fn.targets) {locals saved operands : List Value} {rest : List Op}
    (count : operands.length = target.declaration.params.length) {result : Nested.Result}
    (run : program.Runs checked target.address (.invoke operands) (.done result)) :
    program.Runs checked address (.label locals (.running (saved ++ operands) (.call target :: rest)))
      (.label locals (Body.attach saved target rest (.done result))) :=
  (Relation.ReflTransGen.single ((Program.edge_iff checked found).mpr
    (.dispatch locals saved operands target rest used count))).trans (Program.lift_child checked found used (by trivial) run)

theorem Program.check_function {program : Program} (checked : program.check = true)
    {address : FuncAddr} {fn : Function} (found : program.lookup address = some fn) : fn.check = true :=
  Proofs.check_function checked found

theorem Program.scalar_result {program : Program} (checked : program.checkV1 = true)
    {address : FuncAddr} {fn : Function} (found : program.lookup address = some fn) :
    fn.declaration.results.length ≤ 1 :=
  Proofs.scalar_result checked found

theorem Program.linked_target {program : Program} (checked : program.check = true)
    {address : FuncAddr} {fn : Function} {target : CallTarget}
    (found : program.lookup address = some fn) (used : target ∈ fn.targets) :
    ∃ callee, program.lookup target.address = some callee ∧ callee.declaration = target.declaration ∧
      fn.declaration.module.funcs[target.index.toNat]? = some target.address :=
  Proofs.linked_target checked found used

theorem Function.split_if {fn : Function} {fallthrough : List NumType} {enclosing : EnclosingLabels} {kind : LabelKind} {stack : List Value}
    {result : Option NumType} {thenBody elseBody rest : List Op}
    (typed : fn.WellTyped stack (.if_ result thenBody elseBody :: rest) fallthrough enclosing kind) :
    ∃ (saved : List Value) (condition : BitVec 32), stack = saved ++ [Value.int .i32 condition] :=
  Proofs.split_if typed

theorem Function.split_indexed_if {fn : Function} {fallthrough : List NumType} {enclosing : EnclosingLabels}
    {kind : LabelKind} {stack : List Value} {index : TypeIdx} {signature : Wasm.V1.FuncType}
    {thenBody elseBody rest : List Op}
    (typed : fn.WellTyped stack (.indexedIf index signature thenBody elseBody :: rest) fallthrough enclosing kind) :
    ∃ (operands : List Value) (condition : BitVec 32), stack = operands ++ [Value.int .i32 condition] :=
  Proofs.split_indexed_if typed

/-- Each arm checks as an indexed block under the same operands and continuation. -/
theorem Function.indexed_if_arms {fn : Function} {fallthrough : List NumType} {enclosing : EnclosingLabels}
    {kind : LabelKind} {operands : List Value} {condition : BitVec 32} {index : TypeIdx}
    {signature : Wasm.V1.FuncType} {thenBody elseBody rest : List Op}
    (typed : fn.WellTyped (operands ++ [Value.int .i32 condition])
      (.indexedIf index signature thenBody elseBody :: rest) fallthrough enclosing kind) :
    fn.WellTyped operands (.indexedBlock index signature thenBody :: rest) fallthrough enclosing kind ∧
    fn.WellTyped operands (.indexedBlock index signature elseBody :: rest) fallthrough enclosing kind :=
  Proofs.indexed_if_arms typed

theorem Function.split_br_if {fn : Function} {fallthrough : List NumType} {enclosing : EnclosingLabels} {kind : LabelKind} {stack : List Value}
    {result : List NumType} {depth : LabelIdx} {rest : List Op}
    (typed : fn.WellTyped stack (.brIf depth result :: rest) fallthrough enclosing kind) :
    ∃ (saved : List Value) (condition : BitVec 32), stack = saved ++ [Value.int .i32 condition] :=
  Proofs.split_br_if typed

theorem Function.split_br_table {fn : Function} {fallthrough : List NumType} {enclosing : EnclosingLabels} {kind : LabelKind} {stack : List Value}
    {result : List NumType} {depths : List LabelIdx} {fallback : LabelIdx} {rest : List Op}
    (typed : fn.WellTyped stack (.brTable depths fallback result :: rest) fallthrough enclosing kind) :
    ∃ (saved : List Value) (selector : BitVec 32), stack = saved ++ [Value.int .i32 selector] :=
  Proofs.split_br_table typed

theorem checked_branch {fn : Function} {fallthrough : List NumType} {enclosing : EnclosingLabels} {kind : LabelKind}
    {stack : List Value} {depth : LabelIdx} {result : List NumType} {rest : List Op}
    (typed : fn.WellTyped stack (.br depth result :: rest) fallthrough enclosing kind) :
    (branchTargets fallthrough enclosing kind)[depth.toNat]? = some result ∧ SuffixTyped result stack :=
  Proofs.checked_branch typed

theorem branch_here_result {fallthrough : List NumType} {enclosing : EnclosingLabels} {kind : LabelKind} {result : List NumType}
    (found : (branchTargets fallthrough enclosing kind)[(⟨0⟩ : LabelIdx).toNat]? = some result) :
    kind.inputs fallthrough = result :=
  Proofs.branch_here_result found

theorem Program.admitted_step {program : Program} (checked : program.check = true)
    {address : FuncAddr} {fn : Function} {a b : Phase} (found : program.lookup address = some fn)
    (ready : Admitted program fn a) (move : program.Edge checked address a b) : Admitted program fn b :=
  Proofs.admitted_step checked address found ready move

theorem Program.admitted_run {program : Program} (checked : program.check = true)
    {address : FuncAddr} {fn : Function} {a b : Phase} (found : program.lookup address = some fn)
    (ready : Admitted program fn a) (run : program.Runs checked address a b) : Admitted program fn b := by
  induction run with
  | refl => exact ready
  | tail _ move ih => exact program.admitted_step checked found ih move

theorem Program.nesting_of_admitted {program : Program} (checked : program.check = true)
    {address : FuncAddr} {fn : Function} {phase : Phase} (found : program.lookup address = some fn)
    (ready : Admitted program fn phase) : program.table.Nesting (phase.frames address) :=
  Proofs.nesting_of_admitted checked found ready

theorem Program.check_direct_of_ranked {program : Program} (checked : program.check = true) :
    program.checkDirect = true :=
  Proofs.check_direct_of_ranked checked

/-- Exact local rules for a single step through the current source configuration. -/
theorem Program.frameEdgeAt_iff {program : Program} {address : FuncAddr} {fn : Function} {a b : Phase}
    {kind : LabelKind} (found : program.lookup address = some fn) :
    program.FrameEdgeAt address kind a b ↔ Layer fn (fun target => program.FrameEdge target.address) a b kind :=
  Proofs.frame_edge_iff found

theorem Program.frameEdge_iff {program : Program} {address : FuncAddr} {fn : Function} {a b : Phase}
    (found : program.lookup address = some fn) :
    program.FrameEdge address a b ↔ Layer fn (fun target => program.FrameEdge target.address) a b :=
  program.frameEdgeAt_iff found

theorem Program.frameEdgeAt_iff_ranked {program : Program} (checked : program.check = true)
    {address : FuncAddr} {kind : LabelKind} {a b : Phase} :
    program.FrameEdgeAt address kind a b ↔ program.EdgeAt checked address kind a b :=
  Proofs.frame_edge_iff_ranked checked address

theorem Program.frame_admitted_step {program : Program} (checked : program.checkDirect = true)
    {address : FuncAddr} {fn : Function} {a b : Phase} (found : program.lookup address = some fn)
    (ready : Admitted program fn a) (move : program.FrameEdge address a b) : Admitted program fn b :=
  Proofs.frame_admitted_step checked _ rfl found ready move

theorem Program.frame_admitted_run {program : Program} (checked : program.checkDirect = true)
    {address : FuncAddr} {fn : Function} {a b : Phase} (found : program.lookup address = some fn)
    (ready : Admitted program fn a) (run : program.FrameRuns address a b) : Admitted program fn b := by
  induction run with
  | refl => exact ready
  | tail _ move ih => exact program.frame_admitted_step checked found ih move

theorem Program.frame_lift_child {program : Program} {address : FuncAddr} {fn : Function}
    (found : program.lookup address = some fn) {target : CallTarget} (used : target ∈ fn.targets)
    {a b : Phase} (live : a.Active) {locals saved : List Value} {rest : List Op}
    (run : program.FrameRuns target.address a b) :
    program.FrameRuns address (.label locals (.active saved target a rest))
      (.label locals (Body.attach saved target rest b)) :=
  Proofs.frame_lift_child found used live run

theorem Program.frame_compose_call {program : Program} {address : FuncAddr} {fn : Function}
    (found : program.lookup address = some fn) {target : CallTarget} (used : target ∈ fn.targets)
    {locals saved operands : List Value} {rest : List Op}
    (count : operands.length = target.declaration.params.length) {result : Nested.Result}
    (run : program.FrameRuns target.address (.invoke operands) (.done result)) :
    program.FrameRuns address (.label locals (.running (saved ++ operands) (.call target :: rest)))
      (.label locals (Body.attach saved target rest (.done result))) :=
  (Relation.ReflTransGen.single ((program.frameEdge_iff found).mpr
    (.dispatch locals saved operands target rest used count))).trans (program.frame_lift_child found used (by trivial) run)

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph

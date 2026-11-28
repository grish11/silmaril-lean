module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Host.Entry.Defs
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Host.Body.Thms
import Silmaril.Wasm.Institution.Operational.HostCall.V1.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallFrame.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.Native.Thms
public import Silmaril.Wasm.V1.Execution.Inversion
import Silmaril.Wasm.Versions.Lime1.Execution.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Guard

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.HostEntry.Proofs

open Execution.Runtime (AdminInstr EvalCtx Frame FuncAddr MemAddr MemInst Value decomposeHead?)
open Computed
open Wasm.V1.Execution

theorem invoke_exact {H : Type} {host : HostSemantics H} {s : Store H} {outer : Frame}
    {address : FuncAddr} {decl : Declaration} {fn : Wasm.V1.Func} {args : List Value} {dst : Config H}
    (allocated : s.funcs[address.value]? = some (.wasm decl.type decl.module fn))
    (arity : args.length = decl.params.length) (scalar : decl.results.length ≤ 1) :
    Step host ⟨s, outer, values args ++ [.invoke address]⟩ dst ↔
      dst = ⟨s, outer, [.frame decl.results.length ⟨args ++ fn.locals.map Value.zero, decl.module⟩
        [.label decl.results.length [] (expression fn.body)]]⟩ := by
  constructor
  · intro step
    have noCallout : ∀ call, ¬ CalloutAt ⟨s, outer, values args ++ [.invoke address]⟩ call := by
      intro call located
      have found := exists_callout_iff.mp ⟨call, located⟩
      simp [decompose?, decomposeFrom?_invoke_cons, decomposeHead?, allocated] at found
    have internal := (Step.internal_iff_of_not_callout noCallout).mp step
    have mapped := internal.toLime (target := CallFrame.limeNoHost) (fun _ _ _ _ impossible => impossible)
    have found : (s.mapCode Wasm.V1.Func.toLime).funcs[address.value]? =
        some (.wasm decl.type decl.module fn.toLime) := by
      simp [Execution.Runtime.Store.mapCode_funcs_getElem?, allocated, Execution.Runtime.FuncInst.mapCode]
    have entered := (CallFrame.lime_invoke_wasm_exact found arity).mp
      (by simpa [Config.toLime, codeToLime_append, map_values, codeToLime_cons,
        Execution.Runtime.AdminInstr.map] using mapped)
    apply CallContinuation.config_toLime_injective H
    simpa [Config.toLime, codeToLime_cons, Execution.Runtime.AdminInstr.map, map_expression,
      Wasm.V1.Func.toLime, Declaration.type] using entered
  · rintro rfl
    exact .invokeWasm s outer address decl.type decl.module fn args allocated arity scalar

/-- Invert the already-entered function frame and its initial label. The frame
itself cannot exit while its leading instruction is the function label. -/
theorem frame_label_step {H : Type} {host : HostSemantics H} {s : Store H}
    {outer f : Frame} {n : Nat} {cont : Wasm.V1.Expr} {body : List Admin} {dst : Config H} :
    Step host ⟨s, outer, [.frame n f [.label n cont body]]⟩ dst ↔
      (∃ nextStore nextFrame nextBody,
        Step host ⟨s, f, body⟩ ⟨nextStore, nextFrame, nextBody⟩ ∧
        dst = ⟨nextStore, outer, [.frame n nextFrame [.label n cont nextBody]]⟩) ∨
      (∃ after, PureStep [.label n cont body] after ∧ dst = ⟨s, outer, [.frame n f after]⟩) := by
  constructor
  · intro move
    obtain ⟨outerEq, inside | ⟨after, pure, _, _⟩⟩ := move.frame_inv (p := []) (q := []) rfl
    · obtain ⟨f', code, sub, codeEq⟩ := inside
      rcases sub.label_inv (p := []) (q := []) rfl with
        ⟨next, step, eq⟩ | ⟨next, pure, storeEq, frameEq, eq⟩
      · exact .inl ⟨dst.store, f', next, step, by cases dst; simp_all [values]⟩
      · exact .inr ⟨next, pure, by cases dst; simp_all [values]⟩
    · exact (pure.not_callHead_frame rfl (by simp) (.label n cont body)).elim
  · rintro (⟨_, _, _, step, rfl⟩ | ⟨_, pure, rfl⟩)
    · exact .frame (.label step n cont) n outer
    · exact .frame (.pure _ _ pure) n outer

theorem first_source (stack : List Value) (i : Wasm.V1.Instr) (tail : List Admin)
    (nonvalue : asValue? (.source i) = none) :
    firstRedex (values stack ++ .source i :: tail) = some (.source i) := by
  simp [firstRedex_cons, nonvalue]

private theorem label_exit {n : Nat} {cont : Wasm.V1.Expr} {before body after : List Admin}
    (pure : PureStep before after) (shape : before = [.label n cont body]) :
    (firstRedex body = none ∧ after = body) ∨
      (∃ depth, firstRedex body = some (.source (.br depth))) ∨
      firstRedex body = some (.source .return_) ∨ (body = [.trap] ∧ after = [.trap]) := by
  cases pure
  case labelDone n' cont' vs =>
    obtain ⟨-, -, rfl⟩ : n' = n ∧ cont' = cont ∧ values vs = body := by simpa using shape
    exact .inl ⟨firstRedex_values vs, rfl⟩
  case labelBranch n' cont' extra vs tail count =>
    obtain ⟨-, -, rfl⟩ : n' = n ∧ cont' = cont ∧
        values extra ++ values vs ++ [.source (.br ⟨0⟩)] ++ tail = body := by simpa using shape
    exact .inr (.inl ⟨⟨0⟩, by
      simpa only [values_append, List.append_assoc, List.singleton_append] using
        first_source (extra ++ vs) (.br ⟨0⟩) tail rfl⟩)
  case labelBranchOuter n' cont' vs tail depth outer =>
    obtain ⟨-, -, rfl⟩ : n' = n ∧ cont' = cont ∧
        values vs ++ [.source (.br depth)] ++ tail = body := by simpa using shape
    exact .inr (.inl ⟨depth, by
      simpa only [List.append_assoc, List.singleton_append] using first_source vs (.br depth) tail rfl⟩)
  case labelReturn n' cont' vs tail =>
    obtain ⟨-, -, rfl⟩ : n' = n ∧ cont' = cont ∧
        values vs ++ [.source .return_] ++ tail = body := by simpa using shape
    exact .inr (.inr (.inl (by
      simpa only [List.append_assoc, List.singleton_append] using first_source vs .return_ tail rfl)))
  case labelTrap n' cont' =>
    obtain ⟨-, -, eq⟩ : n' = n ∧ cont' = cont ∧ [AdminInstr.trap] = body := by simpa using shape
    exact .inr (.inr (.inr ⟨eq.symm, rfl⟩))
  all_goals simp [values] at shape

theorem label_values {n : Nat} {cont : Wasm.V1.Expr} {stack : List Value} {before after : List Admin}
    (pure : PureStep before after) (shape : before = [.label n cont (values stack)]) :
    after = values stack := by
  rcases label_exit pure shape with ⟨_, done⟩ | ⟨_, branch⟩ | ret | ⟨trap, _⟩
  · exact done
  · simp at branch
  · simp at ret
  · have head := congrArg firstRedex trap
    simp at head

theorem label_source_live {n : Nat} {cont : Wasm.V1.Expr} {body after : List Admin} {i : Wasm.V1.Instr}
    (pure : PureStep [.label n cont body] after) (head : firstRedex body = some (.source i))
    (noBranch : ∀ l, i ≠ .br l) (noReturn : i ≠ .return_) : False := by
  rcases label_exit pure rfl with ⟨done, _⟩ | ⟨depth, branch⟩ | ret | ⟨trap, _⟩
  · rw [head] at done
    cases done
  · rw [head] at branch
    exact noBranch depth (by injection branch with eq; injection eq)
  · rw [head] at ret
    exact noReturn (by injection ret with eq; injection eq)
  · rw [trap] at head
    simp at head

private theorem label_trapped {n : Nat} {cont : Wasm.V1.Expr} {saved : List Value} {tail after : List Admin}
    (pure : PureStep [.label n cont (values saved ++ .trap :: tail)] after) :
    saved = [] ∧ tail = [] ∧ after = [.trap] := by
  have head : firstRedex (values saved ++ .trap :: tail) = some .trap := by simp
  rcases label_exit pure rfl with ⟨done, _⟩ | ⟨_, branch⟩ | ret | ⟨body, eq⟩
  · rw [head] at done
    cases done
  · rw [head] at branch
    cases branch
  · rw [head] at ret
    cases ret
  · obtain ⟨eqSaved, _, eqTail⟩ := values_cons_inj (ws := saved) (ws' := []) (rest := tail)
      (rest' := []) (x := .trap) (y := .trap) rfl rfl (by simpa [values] using body)
    exact ⟨eqSaved, eqTail, eq⟩

private theorem discard_step_iff {H : Type} {host : HostSemantics H} {s : Store H} {f : Frame}
    {saved : List Value} {tail : List Admin} {dst : Config H} :
    Step host ⟨s, f, values saved ++ .trap :: tail⟩ dst ↔
      ∃ kept rest, Prefix.Discard saved tail kept rest ∧ dst = ⟨s, f, values kept ++ .trap :: rest⟩ := by
  rw [Step.internal_iff_of_not_callout]
  · change Step CallFrame.v1NoHost _ _ ↔ _
    simpa using (Prefix.v1_discard_iff (fun x : Admin => x) (s := s) (f := f) (stack := saved) (tail := tail) (dst := dst))
  · intro c hc
    have found := exists_callout_iff.mp ⟨c, hc⟩
    simp [decompose?] at found

theorem literal_expression (stack : List Value) :
    expression (stack.map Graph.v1CodeSyntax.ops.value) = values stack := by
  induction stack with
  | nil => rfl
  | cons v rest ih =>
    cases v with
    | mk type bits => cases type <;> exact congrArg (List.cons _) ih

theorem numeric_expression (ops : List Prefix.Op) :
    expression (ops.map (Prefix.emit Graph.v1CodeSyntax.ops)) = ops.map (Prefix.emit v1Syntax) := by
  induction ops with
  | nil => rfl
  | cons op ops ih =>
    cases op <;> simp only [List.map_cons, expression, Prefix.emit, Graph.v1CodeSyntax, v1Syntax]
    all_goals exact congrArg (List.cons _) ih

private theorem entry_body {H : Type} (entry : HostEntry H) :
    expression entry.v1Func.body = values entry.function.initial ++
      entry.operands.map (Prefix.emit v1Syntax) ++ .source (.call entry.site.index) :: entry.tail := by
  change expression (entry.function.initial.map Graph.v1CodeSyntax.ops.value ++
      entry.operands.map (Prefix.emit Graph.v1CodeSyntax.ops) ++
      .call entry.site.index :: v1Code entry.function.code) = _
  rw [expression_append, expression_append, literal_expression, numeric_expression]
  rfl

/-- Numeric steps preserve the enclosing frame, function label and source tail. -/
theorem framed_numeric_step {H : Type} {host : HostSemantics H} {s : Store H}
    {outer f : Frame} {n : Nat} {cont : Wasm.V1.Expr} {stack : List Value} {op : Prefix.Op} {tail : List Admin} {dst : Config H} :
    Step host ⟨s, outer, [.frame n f [.label n cont (values stack ++ Prefix.emit v1Syntax op :: tail)]]⟩ dst ↔
      (∃ next, Prefix.Reduce f.locals stack op (.values next) ∧
        dst = ⟨s, outer, [.frame n f [.label n cont (values next ++ tail)]]⟩) ∨
      (∃ saved, Prefix.Reduce f.locals stack op (.trap saved) ∧
        dst = ⟨s, outer, [.frame n f [.label n cont (values saved ++ .trap :: tail)]]⟩) := by
  rw [frame_label_step]
  constructor
  · rintro (⟨nextStore, nextFrame, body, step, eq⟩ | ⟨after, premature, eq⟩)
    · obtain ⟨out, moves, state⟩ := v1_host_prefix_step_iff.mp step
      obtain ⟨rfl, rfl, rfl⟩ := Execution.Runtime.Config.mk.inj state
      cases out with
      | values next => exact .inl ⟨next, moves, eq⟩
      | trap saved => exact .inr ⟨saved, moves, eq⟩
    · exfalso
      cases op <;> apply label_source_live premature
      all_goals first
        | exact first_source stack _ _ rfl
        | intro depth eq; cases eq
        | intro eq; cases eq
  · rintro (⟨next, move, rfl⟩ | ⟨saved, move, rfl⟩)
    · exact .inl ⟨_, _, _, v1_host_prefix_step_iff.mpr ⟨.values next, move, rfl⟩, rfl⟩
    · exact .inl ⟨_, _, _, v1_host_prefix_step_iff.mpr ⟨.trap saved, move, rfl⟩, rfl⟩

theorem framed_direct_step {H : Type} {host : HostSemantics H} {s : Store H}
    {outer f : Frame} {n : Nat} {stack : List Value} {index : FuncIdx} {address : FuncAddr}
    {tail : List Admin} {dst : Config H} (linked : f.module.funcs[index.toNat]? = some address) :
    Step host ⟨s, outer, [.frame n f [.label n [] (values stack ++ .source (.call index) :: tail)]]⟩ dst ↔
      dst = ⟨s, outer, [.frame n f [.label n [] (values stack ++ .invoke address :: tail)]]⟩ := by
  rw [frame_label_step]
  constructor
  · rintro (⟨nextStore, nextFrame, body, step, eq⟩ | ⟨after, premature, _⟩)
    · have same := (HostCall.V1.direct_step_iff linked).mp step
      obtain ⟨rfl, rfl, rfl⟩ := Execution.Runtime.Config.mk.inj same
      exact eq
    · exact (label_source_live premature (first_source _ _ _ rfl)
        (fun _ impossible => by cases impossible) (by intro impossible; cases impossible)).elim
  · rintro rfl
    exact .inl ⟨_, _, _, (HostCall.V1.direct_step_iff linked).mpr rfl, rfl⟩

theorem framed_trapped_step {H : Type} {host : HostSemantics H} {s : Store H}
    {outer f : Frame} {n : Nat} {cont : Wasm.V1.Expr} {saved : List Value} {tail : List Admin} {dst : Config H} :
    Step host ⟨s, outer, [.frame n f [.label n cont (values saved ++ .trap :: tail)]]⟩ dst ↔
      (∃ kept rest, Prefix.Discard saved tail kept rest ∧
        dst = ⟨s, outer, [.frame n f [.label n cont (values kept ++ .trap :: rest)]]⟩) ∨
      (saved = [] ∧ tail = [] ∧ dst = ⟨s, outer, [.frame n f [.trap]]⟩) := by
  rw [frame_label_step]
  constructor
  · rintro (⟨nextStore, nextFrame, body, step, eq⟩ | ⟨after, closes, eq⟩)
    · obtain ⟨kept, rest, discard, state⟩ := discard_step_iff.mp step
      obtain ⟨rfl, rfl, rfl⟩ := Execution.Runtime.Config.mk.inj state
      exact .inl ⟨kept, rest, discard, eq⟩
    · obtain ⟨rfl, rfl, rfl⟩ := label_trapped closes
      exact .inr ⟨rfl, rfl, eq⟩
  · rintro (⟨kept, rest, discard, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    · exact .inl ⟨_, _, _, discard_step_iff.mpr ⟨kept, rest, discard, rfl⟩, rfl⟩
    · exact .inr ⟨_, .labelTrap n cont, rfl⟩

/-- Lift an exact step correspondence with a preserved ready predicate to
arbitrary finite endpoints. -/
theorem finite_run_iff {H : Type} {A : Type} {host : HostSemantics H} (render : A → Config H)
    (edge : A → A → Prop) (ready : A → Prop)
    (exactStep : ∀ {src dst}, ready src → (Step host (render src) dst ↔
      ∃ next, edge src next ∧ ready next ∧ dst = render next))
    (preserved : ∀ {src dst}, edge src dst → ready src → ready dst)
    {src : A} (initial : ready src) {dst : Config H} :
    Steps host (render src) dst ↔
      ∃ next, Relation.ReflTransGen edge src next ∧ ready next ∧ dst = render next := by
  constructor
  · intro run
    generalize eq : render src = initialCfg at run
    induction run using Relation.ReflTransGen.head_induction_on generalizing src with
    | refl => exact ⟨src, .refl, initial, eq.symm⟩
    | head step rest ih =>
      rw [← eq] at step
      obtain ⟨middle, first, midReady, midEq⟩ := (exactStep initial).mp step
      obtain ⟨next, steps, finalReady, finalEq⟩ := ih midReady midEq.symm
      exact ⟨next, steps.head first, finalReady, finalEq⟩
  · rintro ⟨next, run, finalReady, rfl⟩
    clear finalReady
    have both : Steps host (render src) (render next) ∧ ready next := by
      induction run with
      | refl => exact ⟨.refl, initial⟩
      | tail _ move ih =>
        obtain ⟨steps, midReady⟩ := ih
        have nextReady := preserved move midReady
        exact ⟨steps.tail ((exactStep midReady).mpr ⟨_, move, nextReady, rfl⟩), nextReady⟩
    exact both.1

section Execution

variable {H : Type} {entry : HostEntry H} {host : HostSemantics H} {mode : MemoryMode}
  {program : Program} {memory : MemAddr} {calls : CallMode} {base : Store H} {initial : MemInst}
  {bytes : ByteArray} {outer : Frame} {args : List Value}

local notation "live" => storeWithBytes base memory initial bytes
local notation "renderPhase" => entry.render base memory initial bytes outer args
local notation "active" => entry.function.declaration.frame args
local notation "arity" => entry.function.declaration.results.length

private theorem call_step {dst : Config H} (checked : entry.Checked mode program memory calls base outer args) :
    Step host (renderPhase .call) dst ↔ dst = renderPhase .invoke :=
  HostCall.V1.direct_step_iff (tail := []) checked.resolved

private theorem enter_step {dst : Config H} (checked : entry.Checked mode program memory calls base outer args) :
    Step host (renderPhase .invoke) dst ↔ dst = renderPhase (.computing entry.function.initial entry.operands) := by
  have count : args.length = entry.function.declaration.params.length := by
    simpa using congrArg List.length checked.parameters
  have allocated : (storeWithBytes base memory initial bytes).funcs[entry.address.value]? =
      some (.wasm entry.function.declaration.type entry.function.declaration.module entry.v1Func) := checked.allocated
  have locals : entry.v1Func.locals = entry.function.declaration.locals := rfl
  simpa only [render, entry_body, context, EvalCtx.plug, locals, Declaration.frame]
    using (invoke_exact (host := host) (outer := outer) (dst := dst) allocated count checked.scalar)

private theorem numeric_step {stack : List Value} {op : Prefix.Op} {rest : List Prefix.Op} {dst : Config H} :
    Step host (renderPhase (.computing stack (op :: rest))) dst ↔
      (∃ next, Prefix.Reduce (active).locals stack op (.values next) ∧
        dst = renderPhase (.computing next rest)) ∨
      (∃ saved, Prefix.Reduce (active).locals stack op (.trap saved) ∧
        dst = renderPhase (.trapped saved (rest.map (Prefix.emit v1Syntax) ++ .source (.call entry.site.index) :: entry.tail))) := by
  simp only [render, context, EvalCtx.plug, List.map_cons, List.append_assoc, List.cons_append]
  exact framed_numeric_step

private theorem host_resolve_step {saved actual : List Value} {dst : Config H}
    (checked : entry.Checked mode program memory calls base outer args) :
    Step host (renderPhase (.computing (saved ++ actual) [])) dst ↔ dst = renderPhase (.pending saved actual) := by
  simpa only [render, context, EvalCtx.plug, HostCall.V1.Site.pending, List.map_nil, List.append_nil] using
    (framed_direct_step (n := arity) (f := active) (s := live) (outer := outer)
      (stack := saved ++ actual) (tail := entry.tail) (host := host) (dst := dst) checked.linkedHost)

private theorem trapped_step {saved : List Value} {tail : List Admin} {dst : Config H} :
    Step host (renderPhase (.trapped saved tail)) dst ↔
      (∃ kept rest, Prefix.Discard saved tail kept rest ∧ dst = renderPhase (.trapped kept rest)) ∨
      (saved = [] ∧ tail = [] ∧
        dst = renderPhase (.graph ⟨bytes, outer, [.frame arity active [.trap]]⟩)) :=
  framed_trapped_step

private theorem checked_site {actual : List Value}
    (checked : entry.Checked mode program memory calls base outer args)
    (typed : actual.map Value.type = entry.site.signature.params) :
    entry.site.Checked live active actual :=
  ⟨checked.linkedHost, checked.allocatedHost, typed, checked.scalarHost⟩

private theorem pending_step {saved actual : List Value} {dst : Config H}
    (checked : entry.Checked mode program memory calls base outer args)
    (typed : actual.map Value.type = entry.site.signature.params) :
    Step host (renderPhase (.pending saved actual)) dst ↔
      (∃ s' r, host entry.site.target live actual (.returned s' r) ∧
        dst = ⟨s', outer, (entry.context args).plug value (values saved ++ result r ++ entry.tail)⟩) ∨
      (host entry.site.target live actual .diverged ∧ dst = renderPhase (.pending saved actual)) :=
  v1_host_pending_step_iff (k := entry.context args) (outer := outer)
    (saved := saved) (tail := entry.tail) (checked_site (bytes := bytes) checked typed)

private theorem tail_checked (checked : entry.Checked mode program memory calls base outer args) :
    CodeAllowedFor mode program memory calls entry.function.rank (active).module entry.tail := by
  apply RunProofs.tail_allowed (fn := entry.function) ?_ checked.slot checked.supportedTail
  intro target used
  obtain ⟨callee, found, _, resolved, permitted⟩ := checked.linkedTail target used
  exact ⟨callee, found, resolved, permitted⟩

private theorem wrap_checked (checked : entry.Checked mode program memory calls base outer args)
    {code : List Admin}
    (guard : CodeAllowedFor mode program memory calls entry.function.rank (active).module code) :
    CodeAllowedFor mode program memory calls (entry.function.rank + 1) outer.module
      ((entry.context args).plug value code) := by
  have rank : calls.permits (entry.function.rank + 1) entry.function.rank := by
    cases calls <;> simp [CallMode.permits]
  exact RunProofs.single_allowed.mpr
    (.enteredFrame checked.scalar rank (RunProofs.single_allowed.mpr (.label checked.scalar guard)))

theorem bytes_unique (layout : Layout program base memory initial) {left right : ByteArray}
    (same : storeWithBytes base memory initial left = storeWithBytes base memory initial right) :
    left = right := by
  have memoryEq := congrArg (fun s : Store H => s.memories[memory.value]?) same
  rw [(layout.with_bytes left).memory, (layout.with_bytes right).memory, Option.some.injEq] at memoryEq
  exact congrArg MemInst.data memoryEq

private theorem exhausted_ready {saved actual : List Value}
    (ready : entry.Ready mode program memory calls initial args (.computing (saved ++ actual) []))
    (typed : actual.map Value.type = entry.site.signature.params) :
    entry.Ready mode program memory calls initial args (.pending saved actual) := by
  exact ⟨typed, check_prefix_resume (show HostPrefixTyped .. from ready).code typed⟩


theorem preserves (graphChecked : program.checkV1 memory mode calls = true)
    (checked : entry.Checked mode program memory calls base outer args)
    (layout : Layout program base memory initial) (extent : mode.extent initial.data.size bytes)
    (contract : entry.Contract host mode memory initial live) {src dst : Phase}
    (edge : entry.Edge host mode program memory base initial bytes outer args src dst)
    (ready : entry.Ready mode program memory calls initial args src) :
    entry.Ready mode program memory calls initial args dst := by
  cases edge with
  | enter => exact HostPrefixTyped.entry checked.parameters checked.typedBody
  | numeric move => exact HostPrefixTyped.preserve ready move
  | hostResolve typed => exact exhausted_ready ready typed
  | closeTrap =>
    have rank : calls.permits (entry.function.rank + 1) entry.function.rank := by
      cases calls <;> simp [CallMode.permits]
    exact ⟨extent, RunProofs.single_allowed.mpr
      (.enteredFrame checked.scalar rank (RunProofs.single_allowed.mpr .trap))⟩
  | @returned saved actual s' result bytes' behavior stored =>
    obtain ⟨next, _, _, _, after, rendered⟩ := layout.host_return extent (contract actual ready.1) behavior
      (saved := saved) (tail_checked checked)
    have same : s' = storeWithBytes base memory initial next := congrArg (fun cfg : Config H => cfg.store) rendered
    have equal := bytes_unique layout (same.symm.trans stored)
    subst next
    exact ⟨after.1, wrap_checked checked after.2⟩
  | diverged _ => exact ready
  | graph move => exact move.ready graphChecked ready
  | resolve | prefixTrap _ | discard _ => trivial

private theorem sound (graphChecked : program.checkV1 memory mode calls = true)
    (checked : entry.Checked mode program memory calls base outer args)
    (layout : Layout program base memory initial) (matched : mode.matches initial)
    {src dst : Phase} (edge : entry.Edge host mode program memory base initial bytes outer args src dst)
    (ready : entry.Ready mode program memory calls initial args src) :
    Step host (renderPhase src) (renderPhase dst) := by
  cases edge with
  | resolve => exact (call_step checked).mpr rfl
  | enter => exact (enter_step checked).mpr rfl
  | numeric move => exact numeric_step.mpr (.inl ⟨_, move, rfl⟩)
  | prefixTrap move => exact numeric_step.mpr (.inr ⟨_, move, rfl⟩)
  | discard move => exact trapped_step.mpr (.inl ⟨_, _, move, rfl⟩)
  | closeTrap => exact trapped_step.mpr (.inr ⟨rfl, rfl, rfl⟩)
  | hostResolve _ => exact (host_resolve_step checked).mpr rfl
  | returned behavior stored =>
    exact (pending_step checked ready.1).mpr (.inl ⟨_, _, behavior, by cases stored; rfl⟩)
  | diverged behavior => exact (pending_step checked ready.1).mpr (.inr ⟨behavior, rfl⟩)
  | graph move =>
    exact Step.of_internal ((v1_step_iff_at graphChecked layout matched ready).mpr
      ⟨_, move, move.ready graphChecked ready, rfl⟩)

private theorem readback (graphChecked : program.checkV1 memory mode calls = true)
    (checked : entry.Checked mode program memory calls base outer args)
    (layout : Layout program base memory initial) (matched : mode.matches initial)
    (extent : mode.extent initial.data.size bytes)
    (contract : entry.Contract host mode memory initial live)
    {src : Phase} (ready : entry.Ready mode program memory calls initial args src) {dst : Config H}
    (step : Step host (renderPhase src) dst) :
    ∃ next, entry.Edge host mode program memory base initial bytes outer args src next ∧
      dst = renderPhase next := by
  cases src with
  | call => exact ⟨_, .resolve, (call_step checked).mp step⟩
  | invoke => exact ⟨_, .enter, (enter_step checked).mp step⟩
  | computing stack remaining =>
    cases remaining with
    | nil =>
      have typed : HostPrefixTyped entry.function active stack [] entry.site.signature entry.function.code
          entry.function.declaration.results entry.function.entryLabels := ready
      obtain ⟨saved, actual, rfl, resolved, _⟩ :=
        typed.arguments (site := entry.site) (s := live) checked.linkedHost checked.allocatedHost checked.scalarHost
      exact ⟨_, .hostResolve resolved.arguments, (host_resolve_step checked).mp step⟩
    | cons op rest =>
      rcases numeric_step.mp step with ⟨next, moved, eq⟩ | ⟨saved, trapped, eq⟩
      · exact ⟨_, .numeric moved, eq⟩
      · exact ⟨_, .prefixTrap trapped, eq⟩
  | trapped saved tail =>
    rcases trapped_step.mp step with ⟨kept, rest, discarded, eq⟩ | ⟨rfl, rfl, eq⟩
    · exact ⟨_, .discard discarded, eq⟩
    · exact ⟨_, .closeTrap, eq⟩
  | pending saved actual =>
    rcases (pending_step checked ready.1).mp step with ⟨after, r, returned, eq⟩ | ⟨diverged, eq⟩
    · have effect := (contract actual ready.1 after r returned).2
      obtain ⟨next, stored, _, _, _⟩ := layout.host_store extent effect
      exact ⟨_, .returned returned stored, eq.trans (by cases stored; rfl)⟩
    · exact ⟨_, .diverged diverged, eq⟩
  | graph state =>
    have internal := (ReadyFor.internal_iff layout ready).mp step
    obtain ⟨next, moved, _, eq⟩ := (v1_step_iff_at graphChecked layout matched ready).mp internal
    exact ⟨.graph next, .graph moved, eq⟩

theorem step_iff (graphChecked : program.checkV1 memory mode calls = true)
    (checked : entry.Checked mode program memory calls base outer args)
    (layout : Layout program base memory initial) (matched : mode.matches initial)
    (extent : mode.extent initial.data.size bytes)
    (contract : entry.Contract host mode memory initial live)
    {src : Phase} (ready : entry.Ready mode program memory calls initial args src) {dst : Config H} :
    Step host (renderPhase src) dst ↔
      ∃ next, entry.Edge host mode program memory base initial bytes outer args src next ∧
        entry.Ready mode program memory calls initial args next ∧ dst = renderPhase next := by
  constructor
  · intro step
    obtain ⟨next, moved, eq⟩ := readback graphChecked checked layout matched extent contract ready step
    exact ⟨next, moved, preserves graphChecked checked layout extent contract moved ready, eq⟩
  · rintro ⟨next, moved, _, rfl⟩
    exact sound graphChecked checked layout matched moved ready

private theorem prefix_progress (checked : entry.Checked mode program memory calls base outer args)
    {stack : List Value} {ops : List Prefix.Op}
    (ready : entry.Ready mode program memory calls initial args (.computing stack ops)) :
    (∃ saved actual, entry.Ready mode program memory calls initial args (.pending saved actual) ∧
      Steps host (renderPhase (.computing stack ops)) (renderPhase (.pending saved actual))) ∨
    (∃ saved tail, Steps host (renderPhase (.computing stack ops)) (renderPhase (.trapped saved tail))) := by
  induction ops generalizing stack with
  | nil =>
    have typed : HostPrefixTyped entry.function active stack [] entry.site.signature entry.function.code
        entry.function.declaration.results entry.function.entryLabels := ready
    obtain ⟨saved, actual, rfl, linked, _⟩ :=
      typed.arguments (site := entry.site) (s := live) checked.linkedHost checked.allocatedHost checked.scalarHost
    exact .inl ⟨saved, actual, exhausted_ready ready linked.arguments, .single ((host_resolve_step checked).mpr rfl)⟩
  | cons op rest ih =>
    have typed : HostPrefixTyped entry.function active stack (op :: rest) entry.site.signature entry.function.code
        entry.function.declaration.results entry.function.entryLabels := ready
    have checkedCode := typed.code
    generalize shape : Prefix.check (entry.function.declaration.params ++ entry.function.declaration.locals)
      (Prefix.stackTypes stack) (op :: rest) = result
    have computed : ∃ types, result = some types := by
      cases result with
      | none => simp [Function.checkHostPrefix, checkHostPrefixWith, shape] at checkedCode
      | some types => exact ⟨types, rfl⟩
    obtain ⟨types, eq⟩ := computed
    have wellTyped : Prefix.WellTyped (active).locals stack (op :: rest) types.reverse := by
      simpa only [Prefix.WellTyped, typed.locals, List.reverse_reverse] using shape.trans eq
    obtain ⟨out, moved⟩ := Prefix.progress wellTyped
    cases out with
    | values next =>
      have step : Step host (renderPhase (.computing stack (op :: rest))) (renderPhase (.computing next rest)) :=
        numeric_step.mpr (.inl ⟨next, moved, rfl⟩)
      rcases ih (HostPrefixTyped.preserve typed moved) with ⟨saved, actual, pending, run⟩ | ⟨saved, tail, run⟩
      · exact .inl ⟨saved, actual, pending, run.head step⟩
      · exact .inr ⟨saved, tail, run.head step⟩
    | trap saved =>
      exact .inr ⟨saved, _, .single (numeric_step.mpr (.inr ⟨saved, moved, rfl⟩))⟩

theorem reaches_site (checked : entry.Checked mode program memory calls base outer args) :
    (∃ saved actual, entry.Ready mode program memory calls initial args (.pending saved actual) ∧
      Steps host (renderPhase .call) (renderPhase (.pending saved actual))) ∨
    (∃ saved tail, Steps host (renderPhase .call) (renderPhase (.trapped saved tail))) := by
  have entered : Step host (renderPhase .invoke) (renderPhase (.computing entry.function.initial entry.operands)) :=
    (enter_step checked).mpr rfl
  have resolved : Step host (renderPhase .call) (renderPhase .invoke) := (call_step checked).mpr rfl
  have ready : entry.Ready mode program memory calls initial args
      (.computing entry.function.initial entry.operands) :=
    HostPrefixTyped.entry checked.parameters checked.typedBody
  rcases prefix_progress checked ready with ⟨saved, actual, typed, run⟩ | ⟨saved, tail, run⟩
  · exact .inl ⟨saved, actual, typed, (run.head entered).head resolved⟩
  · exact .inr ⟨saved, tail, (run.head entered).head resolved⟩

theorem run_iff (graphChecked : program.checkV1 memory mode calls = true)
    (checked : entry.Checked mode program memory calls base outer args)
    (layout : Layout program base memory initial) (matched : mode.matches initial)
    (extent : mode.extent initial.data.size bytes)
    (contract : entry.Contract host mode memory initial live)
    {src : Phase} (ready : entry.Ready mode program memory calls initial args src) {dst : Config H} :
    Steps host (renderPhase src) dst ↔
      ∃ next, entry.Runs host mode program memory base initial bytes outer args src next ∧
        entry.Ready mode program memory calls initial args next ∧ dst = renderPhase next :=
  finite_run_iff renderPhase _ _
    (fun {_ _} h => step_iff graphChecked checked layout matched extent contract h)
    (fun step h => preserves graphChecked checked layout extent contract step h) ready

end Execution
end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.HostEntry.Proofs

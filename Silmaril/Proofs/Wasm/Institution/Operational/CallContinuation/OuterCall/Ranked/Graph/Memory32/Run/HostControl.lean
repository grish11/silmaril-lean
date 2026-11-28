module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Host.Sequence.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.HostEntry
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Guard
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Host.Body.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Thms
import Silmaril.Wasm.Institution.Operational.BranchExit.Native.Thms
import Silmaril.Wasm.V1.Execution.Inversion
import Silmaril.Wasm.Versions.Lime1.Execution.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.HostEntry.Sequence.ControlProofs

open Execution.Runtime (AdminInstr EvalCtx Frame Value)
open Computed
open Wasm.V1.Execution

variable {H : Type}

theorem context_code (seq : Sequence H) (args : List Value) (labels : List (OpenLabel H)) (body : List Admin) :
    (seq.context args labels).plug value body =
      [.frame seq.root.function.declaration.results.length (seq.root.function.declaration.frame args)
        ((seq.insert labels).plug value [.label (OpenLabel.labelArity seq.root.function labels) (seq.labelCode labels) body])] := by
  simp only [Sequence.context, EvalCtx.plug, EvalCtx.plug_comp]

private theorem composed_frame (left right : EvalCtx Wasm.V1.Instr) (f : Frame) :
    (left.comp right).activeFrame f = right.activeFrame (left.activeFrame f) := by
  induction left generalizing f with
  | hole => rfl
  | seq _ _ _ ih => exact ih f
  | label _ _ _ ih => exact ih f
  | frame _ fr _ ih => exact ih fr

theorem active_frame (seq : Sequence H) (args : List Value) (labels : List (OpenLabel H)) (outer : Frame) :
    (seq.context args labels).activeFrame outer = seq.root.function.declaration.frame args := by
  have preserve (labels : List (OpenLabel H)) (f : Frame) :
      (seq.insert labels).activeFrame f = f := by
    induction labels with
    | nil => rfl
    | cons label rest ih =>
      simp only [Sequence.insert, composed_frame, EvalCtx.activeFrame, ih]
  simp only [Sequence.context, EvalCtx.activeFrame, composed_frame, preserve]

theorem open_code (seq : Sequence H) (args : List Value) (labels : List (OpenLabel H))
    (label : OpenLabel H) (body : List Admin) :
    (seq.context args (label :: labels)).plug value body =
      (seq.context args labels).plug value
        (values label.saved ++ .label label.branchTypes.length (seq.labelCode (label :: labels)) body :: (seq.tailCode label)) := by
  simp only [context_code, Sequence.insert, EvalCtx.plug_comp, EvalCtx.plug,
    OpenLabel.labelArity, List.append_assoc, List.singleton_append, values]

private theorem inserted_head (seq : Sequence H) (labels : List (OpenLabel H)) (n : Nat) (cont : Wasm.V1.Expr) (body : List Admin) :
    ∃ m continuation inside, firstRedex ((seq.insert labels).plug value [.label n cont body]) = some (.label m continuation inside) := by
  induction labels generalizing n cont body with
  | nil => exact ⟨n, cont, body, by simp [Sequence.insert, EvalCtx.plug]⟩
  | cons label rest ih =>
    simp only [Sequence.insert, EvalCtx.plug_comp, EvalCtx.plug]
    exact ih _ _ _

private theorem label_in_sequence {host : HostSemantics H} {s s' : Store H} {f f' : Frame}
    {saved : List Value} {n : Nat} {cont : Wasm.V1.Expr} {body tail out : List Admin} :
    Step host ⟨s, f, values saved ++ [.label n cont body] ++ tail⟩ ⟨s', f', out⟩ ↔
      ∃ code, Step host ⟨s, f, [.label n cont body]⟩ ⟨s', f', code⟩ ∧ out = values saved ++ code ++ tail := by
  constructor
  · intro step
    rcases step.label_inv (p := saved) (q := tail) (n := n) (cont := cont) (body := body) (by simp [List.append_assoc]) with
      ⟨inner, move, eq⟩ | ⟨after, pure, store, frame, eq⟩
    · refine ⟨_, .label move n cont, ?_⟩
      simpa only [List.append_assoc, List.singleton_append] using eq
    · cases store
      cases frame
      exact ⟨after, .pure _ _ pure, eq⟩
  · rintro ⟨code, move, rfl⟩
    exact .context move saved tail

private theorem insert_step {host : HostSemantics H} {s s' : Store H}
    {f f' : Frame} (seq : Sequence H) (labels : List (OpenLabel H)) {n : Nat} {cont : Wasm.V1.Expr} {body out : List Admin} :
    Step host ⟨s, f, (seq.insert labels).plug value [.label n cont body]⟩ ⟨s', f', out⟩ ↔
      ∃ code, Step host ⟨s, f, [.label n cont body]⟩ ⟨s', f', code⟩ ∧
        out = (seq.insert labels).plug value code := by
  induction labels generalizing n cont body with
  | nil => exact ⟨fun move => ⟨out, move, rfl⟩, fun ⟨_, move, rfl⟩ => move⟩
  | cons label rest ih =>
    simp only [Sequence.insert, EvalCtx.plug_comp, EvalCtx.plug]
    rw [ih]
    constructor
    · rintro ⟨code, move, eq⟩
      rcases move.label_inv (p := []) (q := []) rfl with ⟨inside, step, codeEq⟩ | ⟨_, pure, _, _, _⟩
      · obtain ⟨inner, localStep, insideEq⟩ := (label_in_sequence (saved := label.saved) (n := n) (cont := cont) (body := body) (tail := (seq.tailCode label))).mp step
        subst inside
        change code = _ at codeEq
        simp only [values, List.map_nil, List.nil_append] at codeEq
        exact ⟨inner, localStep, eq.trans (congrArg ((seq.insert rest).plug value) codeEq)⟩
      · have head : firstRedex (values label.saved ++ [.label n cont body] ++ (seq.tailCode label)) = some (.label n cont body) := by
          simp
        exact (pure.not_callHead_label rfl head (.label n cont body)).elim
    · rintro ⟨code, move, rfl⟩
      exact ⟨_, .label (.context move label.saved (seq.tailCode label)) _ (seq.labelCode rest), rfl⟩

/-- Peel the real enclosing labels to use the exact rule of the innermost
label. Replacing that label retains each enclosing operand prefix and tail. -/
theorem scoped_step {host : HostSemantics H} {s : Store H} {outer : Frame}
    (seq : Sequence H) (args : List Value) (labels : List (OpenLabel H)) {body : List Admin} {dst : Config H} :
    Step host ⟨s, outer, (seq.context args labels).plug value body⟩ dst ↔
      ∃ nextStore nextFrame code,
        Step host ⟨s, outer, [.frame (OpenLabel.labelArity seq.root.function labels) (seq.root.function.declaration.frame args)
          [.label (OpenLabel.labelArity seq.root.function labels) (seq.labelCode labels) body]]⟩
          ⟨nextStore, outer, [.frame (OpenLabel.labelArity seq.root.function labels) nextFrame code]⟩ ∧
        dst = ⟨nextStore, outer, [.frame seq.root.function.declaration.results.length nextFrame
          ((seq.insert labels).plug value code)]⟩ := by
  rw [context_code]
  constructor
  · intro step
    obtain ⟨same, within | ⟨_, pure, _, _⟩⟩ := step.frame_inv (p := []) (q := []) rfl
    · obtain ⟨next, body', move, after⟩ := within
      obtain ⟨code, inner, eq⟩ := (insert_step seq labels).mp move
      exact ⟨dst.store, next, code, .frame inner _ outer, by cases dst; simp_all [values]⟩
    · obtain ⟨n, cont, inside, head⟩ :=
        inserted_head seq labels (OpenLabel.labelArity seq.root.function labels) (seq.labelCode labels) body
      exact (pure.not_callHead_frame rfl head (.label n cont inside)).elim
  · rintro ⟨s', f', code, move, rfl⟩
    obtain ⟨_, within | ⟨_, pure, _, _⟩⟩ := move.frame_inv (p := []) (q := []) rfl
    · obtain ⟨next, inside, step, eq⟩ := within
      obtain ⟨rfl, rfl⟩ : f' = next ∧ code = inside := by simpa [values] using eq
      exact .frame ((insert_step seq labels).mpr ⟨code, step, rfl⟩) _ outer
    · exact (pure.not_callHead_frame rfl (by simp) (.label (OpenLabel.labelArity seq.root.function labels) (seq.labelCode labels) body)).elim

theorem scoped_result {A : Type} {host : HostSemantics H} {s : Store H} {outer : Frame}
    (seq : Sequence H) (args : List Value) (labels : List (OpenLabel H)) {body : List Admin} {dst : Config H}
    (moves : A → Prop) (output : A → List Admin)
    (atLabel : ∀ target, Step host ⟨s, outer, [.frame (OpenLabel.labelArity seq.root.function labels)
          (seq.root.function.declaration.frame args) [.label (OpenLabel.labelArity seq.root.function labels) (seq.labelCode labels) body]]⟩ target ↔
      ∃ outcome, moves outcome ∧ target = ⟨s, outer, [.frame (OpenLabel.labelArity seq.root.function labels)
        (seq.root.function.declaration.frame args) (output outcome)]⟩) :
    Step host ⟨s, outer, (seq.context args labels).plug value body⟩ dst ↔
      ∃ outcome, moves outcome ∧ dst = ⟨s, outer, [.frame seq.root.function.declaration.results.length
        (seq.root.function.declaration.frame args) ((seq.insert labels).plug value (output outcome))]⟩ := by
  rw [scoped_step seq args labels]
  constructor
  · rintro ⟨next, f, out, step, eq⟩
    obtain ⟨outcome, moved, config⟩ := (atLabel _).mp step
    obtain ⟨rfl, _, same⟩ := Execution.Runtime.Config.mk.inj config
    obtain ⟨rfl, rfl⟩ : f = seq.root.function.declaration.frame args ∧ out = output outcome := by simpa using same
    exact ⟨outcome, moved, eq⟩
  · rintro ⟨outcome, moved, rfl⟩
    exact ⟨_, _, _, (atLabel _).mpr ⟨outcome, moved, rfl⟩, rfl⟩

/-- A frame with a branch at its innermost label either delivers a
zero-depth suffix and label continuation or lowers the positive depth. The branch itself never
reduces inside the label. -/
theorem framed_branch_iff {host : HostSemantics H} {s : Store H} {outer active : Frame}
    {n : Nat} {cont : Wasm.V1.Expr} {stack : List Value} {depth : LabelIdx} {tail : List Admin} {dst : Config H} :
    Step host ⟨s, outer, [.frame n active [.label n cont (values stack ++ .source (.br depth) :: tail)]]⟩ dst ↔
      (∃ extra payload, stack = extra ++ payload ∧ payload.length = n ∧ depth.toNat = 0 ∧
        dst = ⟨s, outer, [.frame n active (values payload ++ expression cont)]⟩) ∨
      (0 < depth.toNat ∧ dst = ⟨s, outer, [.frame n active (values stack ++ [.source (.br (lowerLabel depth))])]⟩) := by
  rw [HostEntry.Proofs.frame_label_step]
  constructor
  · rintro (⟨s', f', code, step, _⟩ | ⟨code, pure, rfl⟩)
    · have translated := step.toLime (target := fun _ _ _ _ => True) (fun _ _ _ _ _ => trivial)
      exact (BranchExit.lime_br_vals_stuck (depth := depth) (stack := stack) (rest := codeToLime tail)
        (by simpa only [Config.toLime, codeToLime_append, map_values, codeToLime_cons, AdminInstr.map,
          Wasm.V1.Instr.toLime] using translated)).elim
    · have translated := (Step.pure (host := host) s active pure).toLime
          (target := fun _ _ _ _ => True) (fun _ _ _ _ _ => trivial)
      have moved := (BranchExit.lime_label_br_cont_iff (cont := cont.toLime) (n := n) (depth := depth) (stack := stack) (rest := codeToLime tail)).mp
        (by simpa only [Config.toLime, codeToLime_cons, codeToLime_append, codeToLime_nil, map_values,
          AdminInstr.map, Wasm.V1.Expr.toLime_eq_map, Wasm.V1.Instr.toLime] using translated)
      rcases moved with ⟨extra, payload, split, arity, zero, eq⟩ | ⟨positive, eq⟩
      · have same : (⟨s, active, code⟩ : Config H) = ⟨s, active, values payload ++ expression cont⟩ :=
          CallContinuation.config_toLime_injective H
            (by simpa only [Config.toLime, codeToLime_append, map_values, map_expression] using eq)
        exact .inl ⟨extra, payload, split, arity, zero, by cases same; rfl⟩
      · have same : (⟨s, active, code⟩ : Config H) = ⟨s, active, values stack ++ [.source (.br (lowerLabel depth))]⟩ :=
          CallContinuation.config_toLime_injective H
            (by simpa only [Config.toLime, codeToLime_append, codeToLime_cons, codeToLime_nil, map_values,
              AdminInstr.map, Wasm.V1.Instr.toLime, lowerLabel_toLime] using eq)
        exact .inr ⟨positive, by cases same; rfl⟩
  · rintro (⟨extra, payload, rfl, arity, zero, rfl⟩ | ⟨positive, rfl⟩)
    · have same : depth = ⟨0⟩ := Idx.toNat_injective zero
      subst depth
      exact .inr ⟨_, by simpa only [values_append, List.append_assoc, List.singleton_append] using
        (.labelBranch n cont extra payload tail arity : PureStep _ _), rfl⟩
    · exact .inr ⟨_, by simpa only [List.append_assoc, List.singleton_append] using
        (.labelBranchOuter n cont stack tail depth (Nat.ne_of_gt positive) : PureStep _ _), rfl⟩

private theorem framed_source_iff {host : HostSemantics H} {s : Store H} {outer f : Frame}
    {n : Nat} {cont : Wasm.V1.Expr} {stack : List Value} {instr : Wasm.V1.Instr} {tail after : List Admin} {dst : Config H}
    (nonvalue : asValue? (.source instr) = none) (noBranch : ∀ d, instr ≠ .br d) (noReturn : instr ≠ .return_)
    (localStep : ∀ target, Step host ⟨s, f, values stack ++ .source instr :: tail⟩ target ↔
      target = ⟨s, f, after⟩) :
    Step host ⟨s, outer, [.frame n f [.label n cont (values stack ++ .source instr :: tail)]]⟩ dst ↔
      dst = ⟨s, outer, [.frame n f [.label n cont after]]⟩ := by
  rw [HostEntry.Proofs.frame_label_step]
  constructor
  · rintro (⟨s', f', body, step, eq⟩ | ⟨code, pure, _⟩)
    · have reached := (localStep _).mp step
      obtain ⟨rfl, rfl, rfl⟩ := Execution.Runtime.Config.mk.inj reached
      exact eq
    · exact (HostEntry.Proofs.label_source_live pure
        (HostEntry.Proofs.first_source stack instr tail nonvalue) noBranch noReturn).elim
  · rintro rfl
    exact .inl ⟨s, f, after, (localStep _).mpr rfl, rfl⟩

theorem scoped_source_iff {host : HostSemantics H} {s : Store H} {outer : Frame}
    (seq : Sequence H) (args : List Value) (labels : List (OpenLabel H))
    {stack : List Value} {instr : Wasm.V1.Instr} {tail after : List Admin} {dst : Config H}
    (nonvalue : asValue? (.source instr) = none) (noBranch : ∀ d, instr ≠ .br d) (noReturn : instr ≠ .return_)
    (localStep : ∀ target, Step host ⟨s, seq.root.function.declaration.frame args, values stack ++ .source instr :: tail⟩ target ↔
      target = ⟨s, seq.root.function.declaration.frame args, after⟩) :
    Step host ⟨s, outer, (seq.context args labels).plug value (values stack ++ .source instr :: tail)⟩ dst ↔
      dst = ⟨s, outer, (seq.context args labels).plug value after⟩ := by
  rw [scoped_step seq args labels, context_code]
  constructor
  · rintro ⟨s', f', code, move, eq⟩
    have same := (framed_source_iff nonvalue noBranch noReturn localStep).mp move
    obtain ⟨rfl, _, frame⟩ := Execution.Runtime.Config.mk.inj same
    obtain ⟨rfl, rfl⟩ : f' = seq.root.function.declaration.frame args ∧ code = [.label (OpenLabel.labelArity seq.root.function labels) (seq.labelCode labels) after] :=
      by simpa using frame
    exact eq
  · rintro rfl
    exact ⟨_, _, _, (framed_source_iff nonvalue noBranch noReturn localStep).mpr rfl, rfl⟩

private theorem block_step {host : HostSemantics H} {s : Store H} {f : Frame}
    {saved : List Value} {result : Option NumType} {body : Wasm.V1.Expr}
    {tail : List Admin} {dst : Config H} :
    Step host ⟨s, f, values saved ++ .source (.block result body) :: tail⟩ dst ↔
      dst = ⟨s, f, values saved ++ .label result.toList.length [] (expression body) :: tail⟩ := by
  constructor
  · intro h
    have notParked : ∀ call, ¬ CalloutAt ⟨s, f, values saved ++ .source (.block result body) :: tail⟩ call := by
      intro call located
      have found := exists_callout_iff.mp ⟨call, located⟩
      simp [decompose?, asValue?] at found
    have internal := (Step.internal_iff_of_not_callout notParked).mp h
    have projected := internal.toLime (target := CallFrame.limeNoHost) (fun _ _ _ _ err => err)
    have type : Wasm.V1.BlockType.toLime result = Blocks.limeType result := by cases result <;> rfl
    have mapped := (Computed.lime_block_iff (result := result) (body := body.toLime)
      (stack := saved) (rest := codeToLime tail)).mp
      (by simpa only [Config.toLime, codeToLime_append, map_values, codeToLime_cons,
        AdminInstr.map, Wasm.V1.Instr.toLime, type] using projected)
    apply CallContinuation.config_toLime_injective H
    simpa only [Config.toLime, codeToLime_append, map_values, codeToLime_cons,
      AdminInstr.map, map_expression, AdminInstr.mapList, List.map_nil] using mapped
  · rintro rfl
    simpa only [List.append_assoc, List.singleton_append] using
      Step.context (Step.pure (host := host) s f (.block result body)) saved tail

theorem scoped_block_iff {host : HostSemantics H} {s : Store H} {outer : Frame}
    (seq : Sequence H) (args : List Value) (labels : List (OpenLabel H)) {stack : List Value}
    {result : Option NumType} {body : Wasm.V1.Expr} {tail : List Admin} {dst : Config H} :
    Step host ⟨s, outer, (seq.context args labels).plug value
      (values stack ++ .source (.block result body) :: tail)⟩ dst ↔
      dst = ⟨s, outer, (seq.context args labels).plug value
        (values stack ++ .label result.toList.length [] (expression body) :: tail)⟩ :=
  scoped_source_iff seq args labels rfl (by intro _ h; cases h) (by intro h; cases h) (fun _ => block_step)

private theorem loop_step {host : HostSemantics H} {s : Store H} {f : Frame}
    {saved : List Value} {result : Option NumType} {body : Wasm.V1.Expr} {tail : List Admin} {dst : Config H} :
    Step host ⟨s, f, values saved ++ .source (.loop result body) :: tail⟩ dst ↔
      dst = ⟨s, f, values saved ++ .label 0 [.loop result body] (expression body) :: tail⟩ := by
  constructor
  · intro move
    have noCallout : ∀ call, ¬ CalloutAt ⟨s, f, values saved ++ .source (.loop result body) :: tail⟩ call := by
      intro call located
      have found := exists_callout_iff.mp ⟨call, located⟩
      simp [decompose?, asValue?] at found
    have internal := (Step.internal_iff_of_not_callout noCallout).mp move
    have projected := internal.toLime (target := CallFrame.limeNoHost) (fun _ _ _ _ err => err)
    have type : Wasm.V1.BlockType.toLime result = Blocks.limeType result := by cases result <;> rfl
    have reduced := (Computed.lime_loop_iff (result := result) (body := body.toLime)
      (stack := saved) (rest := codeToLime tail)).mp
      (by simpa only [Config.toLime, codeToLime_append, map_values, codeToLime_cons, AdminInstr.map,
        Wasm.V1.Instr.toLime, type] using projected)
    apply CallContinuation.config_toLime_injective H
    simpa only [Config.toLime, codeToLime_append, map_values, codeToLime_cons, AdminInstr.map,
      map_expression, Wasm.V1.Instr.toLime, type, List.map_cons, List.map_nil] using reduced
  · rintro rfl
    simpa only [List.append_assoc, List.singleton_append] using
      Step.context (Step.pure (host := host) s f (.loop result body)) saved tail

theorem scoped_loop_iff {host : HostSemantics H} {s : Store H} {outer : Frame}
    (seq : Sequence H) (args : List Value) (labels : List (OpenLabel H)) {stack : List Value}
    {result : Option NumType} {body : Wasm.V1.Expr} {tail : List Admin} {dst : Config H} :
    Step host ⟨s, outer, (seq.context args labels).plug value
      (values stack ++ .source (.loop result body) :: tail)⟩ dst ↔
      dst = ⟨s, outer, (seq.context args labels).plug value
        (values stack ++ .label 0 [.loop result body] (expression body) :: tail)⟩ :=
  scoped_source_iff seq args labels rfl (by intro _ h; cases h) (by intro h; cases h) (fun _ => loop_step)

theorem scoped_get_iff {host : HostSemantics H} {s : Store H} {outer : Frame}
    (seq : Sequence H) (args : List Value) (labels : List (OpenLabel H))
    {stack : List Value} {index : LocalIdx} {v : Value} {tail : List Admin} {dst : Config H}
    (found : (seq.root.function.declaration.frame args).locals[index.toNat]? = some v) :
    Step host ⟨s, outer, (seq.context args labels).plug value (values stack ++ .source (.localGet index) :: tail)⟩ dst ↔
      dst = ⟨s, outer, (seq.context args labels).plug value (values (stack ++ [v]) ++ tail)⟩ := by
  apply scoped_source_iff seq args labels rfl (by intro _ h; cases h) (by intro h; cases h)
  intro target
  have exactPrefix := @v1_host_prefix_step_iff H host s (seq.root.function.declaration.frame args) stack (.get index) tail target
  constructor
  · intro step
    obtain ⟨answer, reduce, eq⟩ := exactPrefix.mp step
    have same := Prefix.reduce_unique reduce (.get found)
    rw [same] at eq
    exact eq
  · rintro rfl
    exact exactPrefix.mpr ⟨_, .get found, rfl⟩

theorem scoped_if_iff {host : HostSemantics H} {s : Store H} {outer : Frame}
    (seq : Sequence H) (args : List Value) (labels : List (OpenLabel H)) {stack : List Value} {condition : BitVec 32}
    {result : Option NumType} {left right : Wasm.V1.Expr} {tail : List Admin} {dst : Config H} :
    Step host ⟨s, outer, (seq.context args labels).plug value
      (values (stack ++ [Value.int .i32 condition]) ++ .source (.if_ result left right) :: tail)⟩ dst ↔
      dst = ⟨s, outer, (seq.context args labels).plug value
        (values stack ++ .source (.block result (if condition = 0 then right else left)) :: tail)⟩ := by
  apply scoped_source_iff seq args labels rfl (by intro _ h; cases h) (by intro h; cases h)
  intro target
  rw [Step.internal_iff_of_not_callout]
  · exact v1_if_select_iff
  · intro c located
    have found := exists_callout_iff.mp ⟨c, located⟩
    simp [decompose?, asValue?] at found

theorem scoped_br_if_iff {host : HostSemantics H} {s : Store H} {outer : Frame}
    (seq : Sequence H) (args : List Value) (labels : List (OpenLabel H))
    {saved : List Value} {condition : BitVec 32} {depth : LabelIdx} {tail : List Admin} {dst : Config H} :
    Step host ⟨s, outer, (seq.context args labels).plug value
      (values (saved ++ [Value.int .i32 condition]) ++ .source (.brIf depth) :: tail)⟩ dst ↔
      dst = ⟨s, outer, (seq.context args labels).plug value
        (values saved ++ (if condition = 0 then [] else [.source (.br depth)]) ++ tail)⟩ := by
  apply scoped_source_iff seq args labels rfl (by intro _ h; cases h) (by intro h; cases h)
  intro target
  constructor
  · intro move
    have noCallout : ∀ call, ¬ CalloutAt
        ⟨s, seq.root.function.declaration.frame args,
          values (saved ++ [Value.int .i32 condition]) ++ .source (.brIf depth) :: tail⟩ call := by
      intro call located
      have found := exists_callout_iff.mp ⟨call, located⟩
      simp [decompose?, asValue?] at found
    have internal := (Step.internal_iff_of_not_callout noCallout).mp move
    have projected := internal.toLime (target := CallFrame.limeNoHost) (fun _ _ _ _ err => err)
    have reduced := (Computed.lime_br_if_iff (saved := saved) (condition := condition) (depth := depth)
      (rest := codeToLime tail)).mp
        (by simpa only [Config.toLime, codeToLime_append, map_values, codeToLime_cons, AdminInstr.map,
          Wasm.V1.Instr.toLime] using projected)
    apply CallContinuation.config_toLime_injective H
    by_cases zero : condition = 0
    · rw [ite_eq_left zero] at reduced ⊢
      simpa only [Config.toLime, codeToLime_append, map_values, List.append_nil] using reduced
    · rw [ite_eq_right zero] at reduced ⊢
      simpa only [Config.toLime, codeToLime_append, map_values, codeToLime_cons, AdminInstr.map,
        Wasm.V1.Instr.toLime, codeToLime_nil, List.nil_append, List.singleton_append] using reduced
  · rintro rfl
    rw [values_append]
    by_cases zero : condition = 0
    · rw [ite_eq_left zero]
      subst condition
      simpa only [values, List.map_cons, List.map_nil, List.append_assoc, List.cons_append, List.nil_append] using!
        (Step.context (Step.pure (host := host) s (seq.root.function.declaration.frame args) (.brIfZero depth)) saved tail)
    · rw [ite_eq_right zero]
      simpa only [values, List.map_cons, List.map_nil, List.append_assoc, List.cons_append, List.nil_append] using
        (Step.context (Step.pure (host := host) s (seq.root.function.declaration.frame args)
          (.brIfNonzero depth condition zero)) saved tail)

theorem scoped_br_table_iff {host : HostSemantics H} {s : Store H} {outer : Frame}
    (seq : Sequence H) (args : List Value) (labels : List (OpenLabel H))
    {saved : List Value} {selector : BitVec 32} {depths : List LabelIdx} {fallback : LabelIdx} {dst : Config H} :
    Step host ⟨s, outer, (seq.context args labels).plug value
      (values (saved ++ [Value.int .i32 selector]) ++ [.source (.brTable depths fallback)])⟩ dst ↔
      dst = ⟨s, outer, (seq.context args labels).plug value
        (values saved ++ [.source (.br (depths[selector.toNat]?.getD fallback))])⟩ := by
  apply scoped_source_iff (tail := []) seq args labels rfl (by intro _ h; cases h) (by intro h; cases h)
  intro target
  have noCallout : ∀ call, ¬ CalloutAt
      ⟨s, seq.root.function.declaration.frame args,
        values (saved ++ [Value.int .i32 selector]) ++ [.source (.brTable depths fallback)]⟩ call := by
    intro call located
    have found := exists_callout_iff.mp ⟨call, located⟩
    simp [decompose?, asValue?] at found
  rw [Step.internal_iff_of_not_callout noCallout,
    ← Step.internal_iff_of_not_callout (host := CallFrame.v1NoHost) noCallout]
  exact v1_br_table_select_iff

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.HostEntry.Sequence.ControlProofs

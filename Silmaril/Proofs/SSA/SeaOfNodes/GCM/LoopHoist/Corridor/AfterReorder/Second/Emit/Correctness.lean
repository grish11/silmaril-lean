module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Saved.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Saved.Prefix.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit

open Silmaril.MLIR.Arith (Env Var Width)
open Silmaril.MLIR.CF (Block Cfg Edge Frame Terminator)
open Silmaril.MLIR.Pure (Code Operands)
open Silmaril.MLIR.SCF (For)
open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.GCM (EdgeSlot Target shape)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit
open Header.Earlier (operations)
open Header.Typed (edgePackets)
open Header.Sequence (State)
open Loop.MLIR.CF (Program TargetOp evalOp lower model)

variable {Input Γ Δ extra : List Width} {saved consumer carried result : Width}
variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}
variable {g : Program Input carried result entrySigs headerSigs}
variable {first : AfterReorder.Plan} {consumerOrigin : Nat}
variable {prepared : Prepared Input carried result} {moved : Emission Input carried result}

private theorem liftCode_operations (code : Block TargetOp (Label saved carried result extra) Γ [result])
    (rename : Rename Γ Δ) (keep : Var Δ consumer) :
    operations (liftCode rename keep code) = operations code := by
  induction code generalizing Δ with
  | terminator => rfl
  | letOp _ _ _ ih => simp only [liftCode, operations, ih]

theorem rewriteAt?_operations {code : Block TargetOp (Label saved carried result extra) Γ [result]}
    {index : Nat} {rename : Rename Γ Δ} {keep : Var Δ consumer}
    {out : Block TargetOp (Label saved carried result (consumer :: extra)) Δ [result]}
    (done : rewriteAt? index rename keep code = some out) :
    operations out = (operations code).eraseIdx index := by
  induction code generalizing index Δ with
  | terminator => simp [rewriteAt?] at done
  | @letOp _ _ width op operands rest ih =>
    cases index with
    | zero =>
      by_cases same : width = consumer
      · subst width
        simp [rewriteAt?] at done
        rw [← done]
        exact liftCode_operations rest (replaceBinding rename keep) keep
      · simp [rewriteAt?, same] at done
    | succ index =>
      simp only [rewriteAt?, Option.map_eq_some_iff] at done
      obtain ⟨next, edited, rfl⟩ := done
      simp only [operations, List.eraseIdx_cons_succ, ih edited]

theorem emitAt?_operations {args : List Width} {index : Nat}
    {cfg : Cfg TargetOp (Label saved carried result extra) Input [result]}
    {target : Cfg TargetOp (Label saved carried result (consumer :: extra)) Input [result]}
    {op : TargetOp args consumer} {operands : Operands ((extra ++ [saved]) ++ Input) args}
    (emitted : emitAt? cfg index op operands = some target) :
    operations (target.block .header) = (operations (cfg.block .header)).eraseIdx index := by
  obtain ⟨⟨leading, tail⟩, _, edited⟩ := Option.bind_eq_some_iff.mp emitted
  obtain ⟨header, rewrite, edited⟩ := Option.bind_eq_some_iff.mp edited
  cases exit : cfg.block .exit with
  | letOp => simp [exit] at edited
  | terminator term =>
    cases term with
    | br => simp [exit] at edited
    | condBr => simp [exit] at edited
    | ret returns =>
      simp only [exit] at edited
      cases edited
      exact rewriteAt?_operations rewrite

private theorem liftEdge_eval (rename : Rename Γ Δ) (keep : Var Δ consumer)
    (edge : Edge (Label saved carried result extra) Γ) (source : Env Γ) (target : Env Δ)
    (same : ∀ {w} (ref : Var Γ w), target.get (rename ref) = source.get ref) :
    (liftEdge rename keep edge).eval target = Saved.prependFrame (target.get keep) (edge.eval source) := by
  rcases edge with ⟨label, args⟩
  cases label
  · change (⟨.header, .cons (target.get keep) ((For.renameOperands rename args).eval target)⟩ :
        Frame (Label saved carried result (consumer :: extra))) = ⟨.header, .cons (target.get keep) (args.eval source)⟩
    rw [evalRenameOperands _ _ _ same]
  · change (⟨.exit, (For.renameOperands rename args).eval target⟩ :
        Frame (Label saved carried result (consumer :: extra))) = ⟨.exit, args.eval source⟩
    rw [evalRenameOperands _ _ _ same]

theorem liftTerm_eval (rename : Rename Γ Δ) (keep : Var Δ consumer)
    (term : Terminator (Label saved carried result extra) [result] Γ) (source : Env Γ) (target : Env Δ)
    (same : ∀ {w} (ref : Var Γ w), target.get (rename ref) = source.get ref) :
    (liftTerm rename keep term).eval target = (term.eval source).map (Saved.prependFrame (target.get keep)) id := by
  cases term with
  | br edge => simp [liftTerm, Terminator.eval, Sum.map, liftEdge_eval _ _ _ _ _ same]
  | ret args => simp [liftTerm, Terminator.eval, Sum.map, evalRenameOperands _ _ _ same]
  | condBr test onTrue onFalse =>
    simp only [liftTerm, Terminator.eval, same, liftEdge_eval _ _ _ _ _ same]
    cases (source.get test).getLsbD 0 <;> rfl

theorem liftCode_eval (code : Block TargetOp (Label saved carried result extra) Γ [result])
    (rename : Rename Γ Δ) (keep : Var Δ consumer) (source : Env Γ) (target : Env Δ)
    (same : ∀ {w} (ref : Var Γ w), target.get (rename ref) = source.get ref) :
    (liftCode rename keep code).eval evalOp (fun term env => Terminator.eval env term) target =
      (code.eval evalOp (fun term env => Terminator.eval env term) source).map (Saved.prependFrame (target.get keep)) id := by
  induction code generalizing Δ with
  | terminator term => exact liftTerm_eval rename keep term source target same
  | letOp op operands rest ih =>
    simp only [liftCode, Code.eval, evalRenameOperands _ _ _ same]
    apply ih
    intro _ ref
    cases ref with
    | here => rfl
    | there ref => exact same ref

private theorem liftCode_edgePackets (code : Block TargetOp (Label saved carried result extra) Γ [result])
    (rename : Rename Γ Δ) (keep : Var Δ consumer) (source : Env Γ) (target : Env Δ)
    (same : ∀ {w} (ref : Var Γ w), target.get (rename ref) = source.get ref) :
    (liftCode rename keep code).eval evalOp edgePackets target =
      (code.eval evalOp edgePackets source).map
        (fun packet => (packet.1, Saved.prependFrame (target.get keep) packet.2)) := by
  induction code generalizing Δ with
  | terminator term =>
    cases term <;> simp only [liftCode, Code.eval, liftTerm, edgePackets, List.map_cons, List.map_nil,
      liftEdge_eval _ _ _ _ _ same]
  | letOp op operands rest ih =>
    simp only [liftCode, Code.eval, evalRenameOperands _ _ _ same]
    apply ih
    intro _ ref
    cases ref with
    | here => rfl
    | there ref => exact same ref

theorem liftCode_target (code : Block TargetOp (Label saved carried result extra) Γ [result])
    (rename : Rename Γ Δ) (keep : Var Δ consumer) (slot : EdgeSlot) :
    (shape.ofBlock (liftCode rename keep code)).target slot =
      ((shape.ofBlock code).target slot).map liftTarget := by
  induction code generalizing Δ with
  | letOp op operands rest ih => exact ih (under rename) (.there keep)
  | terminator term =>
    cases term with
    | ret => cases slot <;> rfl
    | br edge =>
      rcases edge with ⟨label, _⟩
      cases label <;> cases slot <;> rfl
    | condBr test onTrue onFalse =>
      rcases onTrue with ⟨positive, _⟩
      rcases onFalse with ⟨negative, _⟩
      cases positive <;> cases negative <;> cases slot <;> rfl

theorem liftCode_targets_congr {Γ' Δ' : List Width}
    (left : Block TargetOp (Label saved carried result extra) Γ [result])
    (right : Block TargetOp (Label saved carried result extra) Γ' [result])
    (rename : Rename Γ Δ) (keep : Var Δ consumer) (rename' : Rename Γ' Δ') (keep' : Var Δ' consumer)
    (same : (shape.ofBlock left).target = (shape.ofBlock right).target) :
    (shape.ofBlock (liftCode rename keep left)).target = (shape.ofBlock (liftCode rename' keep' right)).target := by
  funext slot
  rw [liftCode_target, liftCode_target, same]

private theorem rewriteAt?_observations {code : Block TargetOp (Label saved carried result extra) Γ [result]}
    {index cut : Nat} {origins : Origins ((extra ++ [saved]) ++ Input) Γ}
    {candidate : Candidate Input saved carried result extra}
    (found : findCaptured? index cut origins code = some candidate)
    (inputs : Env ((extra ++ [saved]) ++ Input)) (source : Env Γ) (agree : CapturesAgree origins source inputs)
    (rename : Rename Γ Δ) (keep : Var Δ candidate.width) (target : Env Δ)
    (same : ∀ {w} (ref : Var Γ w), target.get (rename ref) = source.get ref)
    (value : target.get keep = evalOp candidate.op (candidate.inputs.eval inputs)) :
    ∃ rewritten, rewriteAt? index rename keep code = some rewritten ∧
      rewritten.eval evalOp (fun term env => Terminator.eval env term) target =
        (code.eval evalOp (fun term env => Terminator.eval env term) source).map
          (Saved.prependFrame (target.get keep)) id ∧
      rewritten.eval evalOp edgePackets target =
        (code.eval evalOp edgePackets source).map
          (fun packet => (packet.1, Saved.prependFrame (target.get keep) packet.2)) := by
  induction code generalizing index cut Δ with
  | terminator => simp [findCaptured?] at found
  | letOp op operands rest ih =>
    cases index with
    | zero =>
      cases capture : captureOrigins? origins operands with
      | none => simp [findCaptured?, capture] at found
      | some captured =>
        simp [findCaptured?, capture] at found
        subst candidate
        refine ⟨liftCode (replaceBinding rename keep) keep rest, by simp [rewriteAt?], ?_⟩
        have preserved : ∀ {w} (ref : Var (_ :: _) w),
            target.get (replaceBinding rename keep ref) =
              (Env.cons (target.get keep) source).get ref := by
          intro _ ref
          cases ref with
          | here => rfl
          | there ref => exact same ref
        constructor
        · rw [Code.eval, evalCaptureOrigins origins operands capture source inputs agree, ← value]
          exact liftCode_eval rest (replaceBinding rename keep) keep _ _ preserved
        · rw [Code.eval, evalCaptureOrigins origins operands capture source inputs agree, ← value]
          exact liftCode_edgePackets rest (replaceBinding rename keep) keep _ _ preserved
    | succ index =>
      have nextAgree : CapturesAgree (afterBinding origins (cut + 1))
          (.cons (evalOp op (operands.eval source)) source) inputs := by
        intro _ ref cap fromOrigin
        cases ref with
        | here => cases fromOrigin
        | there ref => exact agree ref cap fromOrigin
      obtain ⟨rewritten, rewrite, taken, packets⟩ := ih found _ nextAgree (under rename) (.there keep)
        (.cons (evalOp op (operands.eval source)) target) (by
          intro _ ref
          cases ref with
          | here => rfl
          | there ref => exact same ref) value
      refine ⟨.letOp op (For.renameOperands rename operands) rewritten, by simp [rewriteAt?, rewrite], ?_, ?_⟩
      · simpa only [Code.eval, Env.get, evalRenameOperands _ _ _ same] using taken
      · simpa only [Code.eval, Env.get, evalRenameOperands _ _ _ same] using packets

theorem rewriteAt?_eval {code : Block TargetOp (Label saved carried result extra) Γ [result]}
    {index cut : Nat} {origins : Origins ((extra ++ [saved]) ++ Input) Γ}
    {candidate : Candidate Input saved carried result extra}
    (found : findCaptured? index cut origins code = some candidate)
    (inputs : Env ((extra ++ [saved]) ++ Input)) (source : Env Γ) (agree : CapturesAgree origins source inputs)
    (rename : Rename Γ Δ) (keep : Var Δ candidate.width) (target : Env Δ)
    (same : ∀ {w} (ref : Var Γ w), target.get (rename ref) = source.get ref)
    (value : target.get keep = evalOp candidate.op (candidate.inputs.eval inputs)) :
    ∃ rewritten, rewriteAt? index rename keep code = some rewritten ∧
      rewritten.eval evalOp (fun term env => Terminator.eval env term) target =
        (code.eval evalOp (fun term env => Terminator.eval env term) source).map
          (Saved.prependFrame (target.get keep)) id := by
  obtain ⟨code, changed, taken, _⟩ := rewriteAt?_observations found inputs source agree rename keep target same value
  exact ⟨code, changed, taken⟩

private theorem header_agrees (first : BitVec saved.val) (old : BitVec carried.val) (input : Env Input) :
    CapturesAgree savedOrigins (.cons first (.cons old input)) (.cons first input) :=
  Saved.origins_agree (.cons first .nil) old input

theorem emitAt?_entry {args : List Width} {op : TargetOp args consumer}
    {operands : Operands ((extra ++ [saved]) ++ Input) args}
    {cfg : Cfg TargetOp (Label saved carried result extra) Input [result]}
    {index : Nat} {target : Cfg TargetOp (Label saved carried result (consumer :: extra)) Input [result]}
    {leading : Saved.Prefix Input ((extra ++ [saved]) ++ Input)}
    {tail : Block TargetOp (Label saved carried result extra) ((extra ++ [saved]) ++ Input) [result]}
    (split : Saved.splitPrefix? cfg.entry (extra ++ [saved]) = some (leading, tail))
    (emitted : emitAt? cfg index op operands = some target) :
    target.entry = leading.wrap (.letOp op operands (liftCode Var.there .here tail)) := by
  cases rewritten : rewriteAt? (consumer := consumer) index Var.there .here (cfg.block .header) with
  | none => simp [emitAt?, split, rewritten] at emitted
  | some header =>
    cases exit : cfg.block .exit with
    | letOp => simp [emitAt?, split, rewritten, exit] at emitted
    | terminator term =>
      cases term with
      | br => simp [emitAt?, split, rewritten, exit] at emitted
      | condBr => simp [emitAt?, split, rewritten, exit] at emitted
      | ret returns =>
        simp [emitAt?, split, rewritten, exit] at emitted
        cases emitted
        rfl

theorem emitAt?_step
    {cfg : Cfg TargetOp (Label saved carried result extra) Input [result]}
    {candidate : Candidate Input saved carried result extra} {index : Nat}
    {target : Cfg TargetOp (Label saved carried result (candidate.width :: extra)) Input [result]}
    {input : Env Input} {values : Env (extra ++ [saved])}
    (matched : Saved.Prefix.Matches cfg.entry input values)
    (found : findCaptured? index 0 (Saved.origins (extra ++ [saved])) (cfg.block .header) = some candidate)
    (emitted : emitAt? cfg index candidate.op candidate.inputs = some target) :
    let value := evalOp candidate.op (candidate.inputs.eval (values.append input))
    Saved.StepRoutes cfg target input values value ∧
      Saved.Prefix.Matches target.entry input (.cons value values) := by
  obtain ⟨leading, tail, split, evaluates⟩ := matched
  let value := evalOp candidate.op (candidate.inputs.eval (values.append input))
  have header (latch : BitVec carried.val) :=
    rewriteAt?_eval found (values.append input) ((values.append (.cons latch .nil)).append input)
      (Saved.origins_agree values latch input) Var.there .here
      (.cons value ((values.append (.cons latch .nil)).append input)) (fun _ => rfl) rfl
  obtain ⟨rewritten, rewrite, _⟩ := header 0
  cases exit : cfg.block .exit with
  | letOp => simp [emitAt?, split, rewrite, exit] at emitted
  | terminator term =>
    cases term with
    | br => simp [emitAt?, split, rewrite, exit] at emitted
    | condBr => simp [emitAt?, split, rewrite, exit] at emitted
    | ret returns =>
      let liftedTail := liftCode (consumer := candidate.width) Var.there .here tail
      let newEntry := leading.wrap (.letOp candidate.op candidate.inputs liftedTail)
      have accepted : withBlocks newEntry rewritten returns = target := by
        simpa [emitAt?, split, rewrite, exit, newEntry, liftedTail] using emitted
      subst target
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [← Saved.splitPrefix?_wrap split]
        simp only [withBlocks, newEntry, Saved.Prefix.wrap_eval, evaluates, Code.eval]
        exact liftCode_eval tail Var.there .here (values.append input) (.cons value (values.append input))
          (fun _ => rfl)
      · rintro ⟨label, packet⟩
        cases label with
        | exit =>
          change _ = ((cfg.block .exit).eval evalOp (fun term env => Terminator.eval env term)
            (packet.append input)).map (Saved.prependFrame value) id
          rw [exit]
          rfl
        | header =>
          cases packet with
          | cons latch rest =>
            cases rest
            obtain ⟨code, foundCode, evaluation⟩ := header latch
            rw [rewrite] at foundCode
            cases foundCode
            exact evaluation
      · exact ⟨.snoc leading candidate.op candidate.inputs, liftedTail,
          Saved.splitPrefix?_snoc split candidate.op candidate.inputs liftedTail,
          by simp [Saved.Prefix.eval, evaluates, Env.append]⟩

theorem emitAt?_edgePackets
    {cfg : Cfg TargetOp (Label saved carried result extra) Input [result]}
    {candidate : Candidate Input saved carried result extra} {index : Nat}
    {target : Cfg TargetOp (Label saved carried result (candidate.width :: extra)) Input [result]}
    (found : findCaptured? index 0 (Saved.origins (extra ++ [saved])) (cfg.block .header) = some candidate)
    (emitted : emitAt? cfg index candidate.op candidate.inputs = some target)
    (input : Env Input) (values : Env (extra ++ [saved])) (latch : BitVec carried.val) :
    let value := evalOp candidate.op (candidate.inputs.eval (values.append input))
    let source := (values.append (.cons latch .nil)).append input
    (target.block .header).eval evalOp edgePackets (.cons value source) =
      ((cfg.block .header).eval evalOp edgePackets source).map
        (fun packet => (packet.1, Saved.prependFrame value packet.2)) := by
  let source := (values.append (.cons latch .nil)).append input
  let value := evalOp candidate.op (candidate.inputs.eval (values.append input))
  obtain ⟨header, rewrite, _, packets⟩ := rewriteAt?_observations found (values.append input) source
    (Saved.origins_agree values latch input) Var.there .here (.cons value source) (fun _ => rfl) rfl
  unfold emitAt? at emitted
  obtain ⟨⟨leading, tail⟩, _, edited⟩ := Option.bind_eq_some_iff.mp emitted
  simp only [rewrite] at edited
  cases exit : cfg.block .exit with
  | letOp => simp [exit] at edited
  | terminator term =>
    cases term with
    | br => simp [exit] at edited
    | condBr => simp [exit] at edited
    | ret =>
      simp [exit] at edited
      cases edited
      exact packets

private theorem emit_exists_and_routes (accepted : prepare? g first consumerOrigin = some prepared)
    (input : Env Input) :
    ∃ (target : TargetCfg prepared) (state : State Input carried result)
      (args : List Width) (producer : TargetOp args prepared.intermediate.1) (operands : Operands Input args)
      (tail : Block TargetOp (Label prepared.intermediate.1 carried result)
        (prepared.intermediate.1 :: Input) [result]),
      emit? prepared = some target ∧
      Header.Sequence.run? (Header.Sequence.initial (lower g)) first.header = some state ∧
      prepared.intermediate.2.entry = .letOp producer operands tail ∧
      target.entry = .letOp producer operands
        (.letOp prepared.consumer.op prepared.consumer.inputs (liftCode Var.there .here tail)) ∧
      rewriteAt? prepared.index Var.there .here (prepared.intermediate.2.block .header) =
        some (target.block .header) ∧
      target.block .exit = .terminator (.ret (.cons .here .nil)) ∧
      let saved := evalOp producer (operands.eval input)
      let value := evalOp prepared.consumer.op (prepared.consumer.inputs.eval (.cons saved input))
      RoutesWith state.cfg prepared.intermediate.2 input (.cons saved .nil) ∧
      StepRoutes prepared.intermediate.2 target input saved value := by
  obtain ⟨_, _, _, _, _, _, _, found, _⟩ := prepare?_placement accepted
  obtain ⟨state, args, producer, operands, tail, ran, entry, exit, routed⟩ :=
    prepare?_first_replay_routes accepted input
  let saved := evalOp producer (operands.eval input)
  let value := evalOp prepared.consumer.op (prepared.consumer.inputs.eval (.cons saved input))
  have header (old : BitVec carried.val) :=
    rewriteAt?_eval found (.cons saved input) (.cons saved (.cons old input)) (header_agrees saved old input)
      Var.there .here (.cons value (.cons saved (.cons old input))) (fun _ => rfl) rfl
  obtain ⟨rewritten, rewrite, _⟩ := header 0
  let target : TargetCfg prepared :=
    withBlocks (.letOp producer operands
      (.letOp prepared.consumer.op prepared.consumer.inputs (liftCode Var.there .here tail)))
      rewritten (.cons .here .nil)
  refine ⟨target, state, args, producer, operands, tail, ?_, ran, entry, rfl, rewrite, rfl,
    ⟨routed.entry, routed.block⟩, ?_, ?_⟩
  · simp [emit?, emitAt?, entry, rewrite, exit, target, Saved.splitPrefix?, Saved.Prefix.wrap]
  · rw [entry]
    exact liftCode_eval tail Var.there .here (.cons saved input) (.cons value (.cons saved input))
      (fun _ => rfl)
  · rintro ⟨label, packet⟩
    cases label with
    | exit =>
      change _ = ((prepared.intermediate.2.block .exit).eval evalOp
        (fun term env => Terminator.eval env term) (packet.append input)).map (carryConsumer value) id
      rw [exit]
      rfl
    | header =>
      cases packet with
      | cons old tail =>
        cases tail
        obtain ⟨code, foundCode, evaluation⟩ := header old
        rw [rewrite] at foundCode
        cases foundCode
        exact evaluation

theorem replay?_spec (accepted : replay? g first consumerOrigin = some moved) :
    prepare? g first consumerOrigin = some moved.prepared ∧
      emit? moved.prepared = some moved.cfg ∧ AfterReorder.replay? g first = some moved.prepared.intermediate := by
  obtain ⟨prepared, checked, rest⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨cfg, emitted, eq⟩ := Option.bind_eq_some_iff.mp rest
  cases eq
  exact ⟨checked, emitted, prepare?_replay_first checked⟩

private def zeroEnv : (widths : List Width) → Env widths
  | [] => .nil
  | _ :: widths => .cons 0 (zeroEnv widths)

theorem prepare?_emits (accepted : prepare? g first consumerOrigin = some prepared) :
    ∃ target, emit? prepared = some target := by
  obtain ⟨target, _, _, _, _, _, emitted, _⟩ := emit_exists_and_routes accepted (zeroEnv Input)
  exact ⟨target, emitted⟩

theorem replay?_routes (accepted : replay? g first consumerOrigin = some moved) (input : Env Input) :
    ∃ (args : List Width) (producer : TargetOp args moved.prepared.intermediate.1)
      (operands : Operands Input args) (tail : Block TargetOp (Label moved.prepared.intermediate.1 carried result)
        (moved.prepared.intermediate.1 :: Input) [result]),
      moved.prepared.intermediate.2.entry = .letOp producer operands tail ∧
      moved.cfg.entry = .letOp producer operands
        (.letOp moved.prepared.consumer.op moved.prepared.consumer.inputs (liftCode Var.there .here tail)) ∧
      rewriteAt? moved.prepared.index Var.there .here (moved.prepared.intermediate.2.block .header) =
        some (moved.cfg.block .header) ∧
      moved.cfg.block .exit = .terminator (.ret (.cons .here .nil)) ∧
      let saved := evalOp producer (operands.eval input)
      let value := evalOp moved.prepared.consumer.op (moved.prepared.consumer.inputs.eval (.cons saved input))
      StepRoutes moved.prepared.intermediate.2 moved.cfg input saved value := by
  obtain ⟨checked, emitted, _⟩ := replay?_spec accepted
  obtain ⟨target, _, args, producer, operands, tail, edit, _, entry, newEntry, header, exit, _, routed⟩ :=
    emit_exists_and_routes checked input
  rw [emitted] at edit
  cases edit
  exact ⟨args, producer, operands, tail, entry, newEntry, header, exit, routed⟩

theorem replay?_header_operations (accepted : replay? g first consumerOrigin = some moved) :
    operations (moved.cfg.block .header) =
      (operations (moved.prepared.intermediate.2.block .header)).eraseIdx moved.prepared.index := by
  obtain ⟨_, _, _, _, _, _, rewritten, _⟩ := replay?_routes accepted (zeroEnv Input)
  exact rewriteAt?_operations rewritten

theorem replay?_prefix_routes (accepted : replay? g first consumerOrigin = some moved) (input : Env Input) :
    ∃ (state : State Input carried result)
      (args : List Width) (producer : TargetOp args moved.prepared.intermediate.1)
      (operands : Operands Input args) (tail : Block TargetOp (Label moved.prepared.intermediate.1 carried result)
        (moved.prepared.intermediate.1 :: Input) [result]),
      Header.Sequence.run? (Header.Sequence.initial (lower g)) first.header = some state ∧
      moved.prepared.intermediate.2.entry = .letOp producer operands tail ∧
      let firstValue := evalOp producer (operands.eval input)
      let secondValue := evalOp moved.prepared.consumer.op (moved.prepared.consumer.inputs.eval (.cons firstValue input))
      RoutesWith state.cfg moved.prepared.intermediate.2 input (.cons firstValue .nil) ∧
      StepRoutes moved.prepared.intermediate.2 moved.cfg input firstValue secondValue ∧
      Saved.Prefix.Matches moved.cfg.entry input (.cons secondValue (.cons firstValue .nil)) := by
  obtain ⟨checked, emitted, _⟩ := replay?_spec accepted
  obtain ⟨target, state, args, producer, operands, tail, edit, ran, entry, newEntry, _, _, prior, step⟩ :=
    emit_exists_and_routes checked input
  rw [emitted] at edit
  cases edit
  refine ⟨state, args, producer, operands, tail, ran, entry, prior, step, ?_⟩
  rw [newEntry]
  refine ⟨.snoc (.snoc .nil producer operands) moved.prepared.consumer.op moved.prepared.consumer.inputs,
    liftCode Var.there .here tail, ?_, rfl⟩
  simp [Saved.splitPrefix?]

theorem replay?_packet_step (accepted : replay? g first consumerOrigin = some moved) (input : Env Input) :
    ∃ (state : State Input carried result)
      (args : List Width) (producer : TargetOp args moved.prepared.intermediate.1)
      (operands : Operands Input args) (tail : Block TargetOp (Label moved.prepared.intermediate.1 carried result)
        (moved.prepared.intermediate.1 :: Input) [result]),
      Header.Sequence.run? (Header.Sequence.initial (lower g)) first.header = some state ∧
      moved.prepared.intermediate.2.entry = .letOp producer operands tail ∧
      let firstValue := evalOp producer (operands.eval input)
      let secondValue := evalOp moved.prepared.consumer.op (moved.prepared.consumer.inputs.eval (.cons firstValue input))
      RoutesWith state.cfg moved.prepared.intermediate.2 input (.cons firstValue .nil) ∧
      StepRoutes moved.prepared.intermediate.2 moved.cfg input firstValue secondValue := by
  obtain ⟨state, args, producer, operands, tail, ran, entry, prior, step, _⟩ :=
    replay?_prefix_routes accepted input
  exact ⟨state, args, producer, operands, tail, ran, entry, prior, step⟩

theorem replay?_run_eq (accepted : replay? g first consumerOrigin = some moved)
    (input : Env Input) (fuel : Nat) :
    moved.cfg.run evalOp fuel input = moved.prepared.intermediate.2.run evalOp fuel input := by
  obtain ⟨_, _, _, _, _, _, _, prior, step⟩ := replay?_packet_step accepted input
  exact Saved.extend_run_eq prior step fuel

theorem replay?_budget (accepted : replay? g first consumerOrigin = some moved)
    (input : Env Input) (budget : Nat) :
    moved.cfg.run evalOp (budget + 3) input =
      (g.evalBackedges model budget (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input)).map
        (fun value => Env.cons value .nil) :=
  (replay?_run_eq accepted input _).trans (AfterReorder.replay?_budget (replay?_spec accepted).2.2 input budget)

open Silmaril.MLIR.CF.SwitchAssert (Cfg) in
theorem replay?_denotePart (accepted : replay? g first consumerOrigin = some moved) (input : Env Input) :
    (Cfg.embed moved.cfg).denotePart evalOp input = (Cfg.embed (lower g)).denotePart evalOp input := by
  calc
    _ = (Cfg.embed moved.prepared.intermediate.2).denotePart evalOp input := by
      apply Part.ext
      intro outcome
      simp only [Cfg.mem_denotePart_iff, Cfg.embed_run, replay?_run_eq accepted]
    _ = _ := AfterReorder.replay?_denotePart (replay?_spec accepted).2.2 input

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit

module

public import Silmaril.Proofs.Wasm.Execution.Core.Intrinsic.Typing
public import Silmaril.Wasm.SingleThreaded.Exec.Driver

public section

namespace Silmaril.Proofs.Wasm.Execution.Core.Intrinsic

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Numerics Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Execution.Core.Intrinsic Silmaril.Wasm.SingleThreaded.Det

variable {H : Type} {context : Context} {world : World H context}
  {locals input middle results : List IntType} {profile : Profile} {host : HostSemantics H}

private theorem eval_head (frame : LocalFrame world locals) (op : Op locals input middle)
    (stack : Values input) (tail : Code locals middle results) :
    ∃ kept args headCode,
      stack.erase.reverse = kept ++ args ∧
      Head profile world.store frame.erase args (.plain op.erase) ⟨world.store, frame.erase, headCode⟩ ∧
      ((op.eval frame.values stack).resume tail).erase =
        vals kept ++ headCode ++ expression tail.erase := by
  cases op with
  | nop =>
    refine ⟨stack.erase.reverse, [], [], by simp, ?_, by simp [Op.eval, Effect.resume, Control.erase]⟩
    exact .parametric .nop
  | @drop kind _ =>
    cases stack with
    | cons bits stack =>
      let value : Val := .num ⟨.int kind, bits⟩
      refine ⟨stack.erase.reverse, [value], [], by simp [Values.erase, value], ?_,
        by simp [Op.eval, Effect.resume, Control.erase]⟩
      exact .parametric (.drop value)
  | @localGet kind _ ref bound =>
    let value : Val := .num ⟨.int kind, ref.get frame.values⟩
    refine ⟨stack.erase.reverse, [], [value.toAdmin], by simp, ?_, ?_⟩
    · exact .variable (.localGet (slot_value ref frame.values))
    · simp [Op.eval, Effect.resume, Control.erase, Values.erase, value, List.append_assoc]
  | @intBin kind _ op =>
    cases stack with
    | cons rhs stack =>
      cases stack with
      | cons lhs stack =>
        let left : Val := .num ⟨.int kind, lhs⟩
        let right : Val := .num ⟨.int kind, rhs⟩
        cases h : intBinOp kind op lhs rhs with
        | ok bits =>
          refine ⟨stack.erase.reverse, [left, right], [.plain (.intConst kind bits)],
            by simp [Values.erase, left, right, List.append_assoc], .numeric (.intBinOp h), ?_⟩
          simp [Op.eval, h, Effect.resume, Control.erase, Values.erase, Val.toAdmin, List.append_assoc]
        | error _ =>
          refine ⟨stack.erase.reverse, [left, right], [.trap],
            by simp [Values.erase, left, right, List.append_assoc], .numeric (.intBinOpTrap h), ?_⟩
          simp [Op.eval, h, Effect.resume, Control.erase]
  | unreachable =>
    exact ⟨stack.erase.reverse, [], [.trap], by simp,
      .parametric .unreachable, rfl⟩

private theorem op_decompose (frame : LocalFrame world locals) (op : Op locals input middle)
    (stack : Values input) (tail : Code locals middle results) :
    ∃ kept args headCode,
      (Control.run stack (.seq op tail)).erase =
        vals kept ++ (vals args ++ .plain op.erase :: expression tail.erase) ∧
      Head profile world.store frame.erase args (.plain op.erase) ⟨world.store, frame.erase, headCode⟩ ∧
      (State.mk frame ((op.eval frame.values stack).resume tail)).erase =
        ⟨world.store, frame.erase, vals kept ++ headCode ++ expression tail.erase⟩ := by
  obtain ⟨kept, args, headCode, hs, hh, hout⟩ := eval_head (profile := profile) frame op stack tail
  exact ⟨kept, args, headCode,
    by simp [Control.erase, Code.erase, expression, hs, List.append_assoc], hh,
    by simp [State.erase, hout]⟩

private theorem no_context {saved ignored : List IntType} (stack : Values saved)
    (tail : Code locals ignored results) :
    (stack.isEmpty && tail.isEmpty) = true ↔ stack.erase.reverse = [] ∧ expression tail.erase = [] := by
  cases stack <;> cases tail <;> simp [Values.isEmpty, Code.isEmpty, Values.erase, Code.erase, expression]

theorem step_sound {state next : State world locals results} (h : state.step? = some next) :
    Step profile host state.erase next.erase := by
  obtain ⟨frame, control⟩ := state
  cases control with
  | run stack code =>
    cases code with
    | done => simp [State.step?, Control.step?] at h
    | seq op tail =>
      cases Option.some.inj h
      obtain ⟨kept, args, headCode, hs, hh, ht⟩ := op_decompose (profile := profile) frame op stack tail
      exact Step.of_noHost host (HeadDec.toStep ⟨kept, args, _, _,
        ⟨world.store, frame.erase, headCode⟩, hs, hh, ht⟩)
  | trapping stack tail =>
    by_cases empty : (stack.isEmpty && tail.isEmpty) = true
    · simp [State.step?, Control.step?, empty] at h
    · have eq : (⟨frame, .trapping .nil .done⟩ : State world locals results) = next := by
        simpa [State.step?, Control.step?, empty] using h
      subst next
      have hne : stack.erase.reverse ≠ [] ∨ expression tail.erase ≠ [] := by
        by_cases hs : stack.erase.reverse = []
        · exact .inr (fun ht => empty ((no_context stack tail).2 ⟨hs, ht⟩))
        · exact .inl hs
      exact .trapInstrs hne

private theorem op_not_control (op : Op locals input middle) :
    famOf (.plain op.erase) ≠ .control := by
  cases op <;> intro impossible <;> cases impossible

private theorem headDec_unique {oracle : GrowKind → Nat → Nat → Nat → Bool}
    {store : Store H} {frame : Frame} {source : List Admin} {target expected : Config H}
    {e : Admin} {kept args : List Val} {rest : List Admin} {head : Config H}
    (family : famOf e ≠ .control) (sourceEq : source = vals kept ++ (vals args ++ e :: rest))
    (headStep : Head (Profile.deterministic oracle) store frame args e head)
    (targetEq : expected = ⟨head.store, head.frame, vals kept ++ head.code ++ rest⟩)
    (step : HeadDec (Profile.deterministic oracle) store frame source target) : target = expected := by
  have first : fnv source = (kept ++ args, e :: rest) := by
    rw [sourceEq]; simp [fnv_cons_of_none headStep.good.val_none]
  obtain ⟨otherPrefix, otherArgs, op, otherRest, otherHead, hf, _, hh, rfl⟩ := fnv_headDec step
  rw [first] at hf
  obtain ⟨prefixEq, restEq⟩ := Prod.mk.inj hf
  obtain ⟨rfl, rfl⟩ := List.cons.inj restEq
  rcases append_eq_append_suffix prefixEq with ⟨extra, he⟩ | ⟨extra, he⟩
  · obtain ⟨rfl, rfl⟩ := Head.det_fam family headStep hh he
    have eq : args = otherArgs := by simpa using he
    subst otherArgs
    rw [targetEq, List.append_cancel_right prefixEq]
  · obtain ⟨rfl, rfl⟩ := Head.det_fam family hh headStep he
    have eq : otherArgs = args := by simpa using he
    subst otherArgs
    simp only [List.nil_append] at prefixEq
    rw [targetEq, List.append_cancel_right prefixEq]

theorem run_reflect {oracle : GrowKind → Nat → Nat → Nat → Bool}
    (frame : LocalFrame world locals) (stack : Values input) (code : Code locals input results)
    {target : Config H}
    (step : DStep oracle (State.mk frame (.run stack code)).erase target) :
    ∃ next : State world locals results,
      (State.mk frame (.run stack code)).step? = some next ∧ target = next.erase := by
  cases code with
  | done => exact (not_step_vals (by simpa [State.erase, Control.erase, Code.erase, expression] using step)).elim
  | seq op tail =>
    let next := State.mk frame ((op.eval frame.values stack).resume tail)
    obtain ⟨kept, args, headCode, hs, hh, ht⟩ :=
      op_decompose (profile := Profile.deterministic oracle) frame op stack tail
    refine ⟨next, rfl, ?_⟩
    rcases Step.decomp step with actual | bubble
    · exact headDec_unique (op_not_control op) hs hh ht actual
    · exact (headDec_bubble_false ⟨kept, args, _, _, ⟨world.store, frame.erase, headCode⟩,
        hs, hh, ht⟩ bubble).elim

theorem step_reflect {oracle : GrowKind → Nat → Nat → Nat → Bool}
    {state : State world locals results} {target : Config H}
    (step : DStep oracle state.erase target) :
    ∃ next, state.step? = some next ∧ Relation.ReflGen (DStep oracle) target next.erase := by
  obtain ⟨frame, control⟩ := state
  cases control with
  | run stack code =>
    obtain ⟨next, h, rfl⟩ := run_reflect frame stack code step
    exact ⟨next, h, .refl⟩
  | trapping stack tail =>
    have first : fnv (Control.trapping stack tail).erase =
        (stack.erase.reverse, .trap :: expression tail.erase) := by
      simp [Control.erase, fnv_cons_of_none (a := .trap) rfl]
    by_cases empty : (stack.isEmpty && tail.isEmpty) = true
    · obtain ⟨hs, ht⟩ := no_context stack tail |>.mp empty
      exact (not_step_trap (by simpa [State.erase, Control.erase, hs, ht] using step)).elim
    refine ⟨⟨frame, .trapping .nil .done⟩, by simp [State.step?, Control.step?, empty], ?_⟩
    rcases Step.decomp step with actual | bubble
    · obtain ⟨_, _, e, _, _, hf, _, hh, _⟩ := fnv_headDec actual
      change fnv (Control.trapping stack tail).erase = _ at hf
      rw [first] at hf
      exact (hh.good.ne_trap (List.cons.inj (Prod.mk.inj hf).2).1.symm).elim
    · obtain ⟨p, q, u, r, _, ⟨_, _, rfl⟩ | ⟨_, hf, _, _⟩⟩ := fnv_bubble bubble
      · exact bubble_to (.inl rfl)
      · change fnv (Control.trapping stack tail).erase = _ at hf
        rw [first] at hf
        cases (List.cons.inj (Prod.mk.inj hf).2).1

theorem result_sound {state : State world locals results} {result : Result}
    (h : state.result? = some result) :
    state.erase.code = result.toAdmin ∧ ∀ target, ¬ Step profile noHost state.erase target := by
  obtain ⟨frame, control⟩ := state
  cases control with
  | run stack code =>
    cases code with
    | seq op tail => simp [State.result?, Control.result?] at h
    | done =>
      cases Option.some.inj h
      refine ⟨by simp [State.erase, Control.erase, Code.erase, expression, Result.toAdmin],
        fun target step => ?_⟩
      exact not_step_vals (by simpa [State.erase, Control.erase, Code.erase, expression] using step)
  | trapping stack tail =>
    by_cases empty : (stack.isEmpty && tail.isEmpty) = true
    · have eq : Result.trap = result := by simpa [State.result?, Control.result?, empty] using h
      subst result
      obtain ⟨hs, ht⟩ := no_context stack tail |>.mp empty
      refine ⟨by simp [State.erase, Control.erase, Result.toAdmin, hs, ht], fun target step => ?_⟩
      exact not_step_trap (by simpa [State.erase, Control.erase, hs, ht] using step)
    · simp [State.result?, Control.result?, empty] at h

theorem runFor_sound (fuel : Nat) (state : State world locals results) :
    Steps profile host state.erase (state.runFor fuel).erase := by
  induction fuel generalizing state with
  | zero => exact .refl
  | succ fuel ih =>
    cases h : state.step? with
    | none => simpa [State.runFor, h] using (Relation.ReflTransGen.refl (r := Step profile host))
    | some next => simpa [State.runFor, h] using (ih next).head (step_sound h)

end Silmaril.Proofs.Wasm.Execution.Core.Intrinsic

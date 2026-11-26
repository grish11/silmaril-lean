module

public import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Continuation.Defs
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Thms
import Silmaril.Wasm.Institution.Operational.Blocks.Context.Thms
import Silmaril.Wasm.Lime1.Execution.Callout.Properties

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Continuation.Proofs

open Execution.Runtime (EvalCtx Frame Value)
open Wasm.Lime1.Execution
open CallContinuation.OuterCall

set_option backward.isDefEq.respectTransparency false

variable {H : Type} {s s' : Store H} {host : HostSemantics H} {outer active : Frame}
  {scope : Scope} {n : Nat} {cont : Wasm.Lime1.Expr} {body next : List Admin} {dst : Config H}

theorem frameContext_plug : (frameContext active scope).plug value body = framed active body scope := by
  induction scope generalizing body with
  | function => rfl
  | label _ _ _ _ _ ih =>
    rw [frameContext, EvalCtx.plug_comp, ih]
    rfl

theorem plug_invoke {saved : List Value} {ops : List (Op H)} :
    (invokeContext scope n cont active saved ops).plug value body =
      framed active [.label n cont (values saved ++ body ++ code ops)] scope := by
  rw [invokeContext, EvalCtx.plug_comp, frameContext_plug]
  rfl

theorem framed_step (move : Step host ⟨s, active, body⟩ ⟨s', active, next⟩) :
    Step host ⟨s, outer, framed active body scope⟩ ⟨s', outer, framed active next scope⟩ := by
  induction scope generalizing body next with
  | function arity => exact .frame move arity outer
  | label arity enclosing saved tail scope ih =>
    exact ih (.label (.context move saved tail) arity enclosing)

theorem noLabelCallout (absent : Execution.Runtime.decomposeFrom? coding s [] body = none) :
    decompose? (⟨s, outer, framed active [.label n cont body] scope⟩ : Config H) = none := by
  induction scope generalizing n cont body with
  | function => simp [decompose?, framed, absent]
  | label arity enclosing saved tail scope ih =>
    refine ih (n := arity) (cont := enclosing) (body := values saved ++ [.label n cont body] ++ tail) ?_
    simp [List.append_assoc, absent]

/-- Invert an internal step under any finite stack of enclosing labels.
Only the active label can step or exit. -/
theorem body_cases
    (move : Internal ⟨s, outer, framed active [.label n cont body] scope⟩ dst) :
    (∃ mid, Internal ⟨s, active, body⟩ mid ∧
      dst = ⟨mid.store, outer, framed mid.frame [.label n cont mid.code] scope⟩) ∨
    ∃ out, PureStep active.module.types [.label n cont body] out ∧
      dst = ⟨s, outer, framed active out scope⟩ := by
  induction scope generalizing n cont body with
  | function => exact Computed.lime_body_step_cases move
  | label arity enclosing saved tail scope ih =>
    have opened : Internal ⟨s, outer, framed active
        [.label arity enclosing (values saved ++ .label n cont body :: tail)] scope⟩ dst := by
      simpa only [framed, List.append_assoc, List.singleton_append] using move
    rcases ih opened with ⟨mid, inside, rfl⟩ | ⟨out, pop, _⟩
    · have inner := Blocks.Context.lime_label_cont_iff (s := s) (f := active) (dst := mid)
        (saved := saved) (rest := tail) (n := n) (cont := cont) (body := body)
      rcases inner.mp inside with ⟨after, step, rfl⟩ | ⟨out, pop, rfl⟩
      · exact .inl ⟨after, step, by simp only [framed, List.append_assoc, List.singleton_append]⟩
      · exact .inr ⟨out, pop, rfl⟩
    · exact (Computed.lime_label_stays (stack := saved) rfl (by simp) (by simp) (by simp) pop).elim

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Continuation.Proofs

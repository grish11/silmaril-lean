module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Defs
import Silmaril.Semantics.ITree.Trace.Finite.Explain.Thms
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Interface
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Named

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

open Silmaril.Elgot.ITree
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

variable {F : Type} [DecidableEq F] {signature : PrimitiveSignature F} {a b : Nat}
  {inputs : Fin a → PacketType} {outputs : Fin b → PacketType}
  (left right : Program signature inputs outputs)

theorem explain_refinement (input : Fin a) (packet : Denote (inputs input)) :
    (left.explainRefinementAt? right input packet = none ↔ left.refinementAt? right input packet = true) ∧
    ∀ trace, left.explainRefinementAt? right input packet = some trace →
      HasTrace (left.observe input packet) trace ∧ ¬ HasTrace (right.observe input packet) trace := by
  have checked := Finite.explain_spec
    (fun (key : signature.Request) => (signature.reply key.1).enumerate) (fun key => mem_enumerate (signature.reply key.1))
    left.states right.states left.mem_states right.mem_states left.step right.step
    (left.start input packet) (right.start input packet)
  refine ⟨by simpa only [Program.explainRefinementAt?, Option.map_eq_none_iff,
    Program.refinementAt?, Program.refinementBetween?] using
    checked.1, ?_⟩
  intro trace found
  obtain ⟨pre, stored, rfl⟩ := Option.map_eq_some_iff.mp found
  simpa only [observe_eq, hasTrace_bind_pure_map_iff render_injective] using checked.2 pre stored

theorem explain_mismatch :
    (left.explainMismatch? right = none ↔ left.weakEq? right = true) ∧
    ∀ w, left.explainMismatch? right = some w →
      left.firstMismatch? right = some w.packet ∧
        w.direction.distinguishes (left.observe w.packet.1 w.packet.2)
          (right.observe w.packet.1 w.packet.2) w.trace := by
  cases first : left.firstMismatch? right with
  | none => simp [Program.explainMismatch?, Program.weakEq?, first]
  | some p =>
    have direct := explain_refinement left right p.1 p.2
    have reverse := explain_refinement right left p.1 p.2
    have weakFail := mismatch_some first
    cases lr : left.explainRefinementAt? right p.1 p.2 with
    | some trace =>
      constructor
      · simp [Program.explainMismatch?, Program.weakEq?, first, lr]
      · intro w found
        have equal : ⟨p, .leftToRight, trace⟩ = w := by
          simpa [Program.explainMismatch?, first, lr] using found
        subst w
        exact ⟨rfl, direct.2 trace lr⟩
    | none =>
      cases rl : right.explainRefinementAt? left p.1 p.2 with
      | some trace =>
        constructor
        · simp [Program.explainMismatch?, Program.weakEq?, first, lr, rl]
        · intro w found
          have equal : ⟨p, .rightToLeft, trace⟩ = w := by
            simpa [Program.explainMismatch?, first, lr, rl] using found
          subst w
          exact ⟨rfl, reverse.2 trace rl⟩
      | none =>
        exact (weakFail (by simp [Program.weakEqAt?, direct.1.mp lr, reverse.1.mp rl])).elim

end Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

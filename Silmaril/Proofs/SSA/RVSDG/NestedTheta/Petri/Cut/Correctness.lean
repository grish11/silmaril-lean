module

public import Silmaril.SSA.RVSDG.NestedTheta.Petri.Cut.Defs

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Petri.Cut.Proofs

open RVSDG.Petri (Tokens Vertex read)
open Relation (ReflTransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {args bank outs : Ports (PortType V S)}
variable {past frontSigs wholeSigs tailSigs : List (Ports (PortType V S))}
variable {front : Term Op args past frontSigs bank} {whole : Term Op args past wholeSigs outs}
variable {tail : Term Op args (extend past frontSigs) tailSigs outs}
variable (cut : Cut front whole tail) (m : Model.{u, v, w} Op)

theorem attach_pending :
    cut.attach m (pending m front) (pending m tail) = pending m whole := by
  induction cut with
  | stop => rfl
  | @bind _ _ _ _ _ node children _ whole _ _ ih =>
    exact congrArg (fun rest => ((Vertex.pending, rest) : Marking m (.bind node children whole))) ih

theorem observe_attach (prefixMark : Marking m front) (tailMark : Marking m tail) :
    cut.observe m (cut.attach m prefixMark tailMark) = prefixMark := by
  induction cut with
  | stop => cases prefixMark; rfl
  | bind _ _ _ ih => exact congrArg (Prod.mk prefixMark.1) (ih prefixMark.2 tailMark)

theorem prefix_step (entry : Tuple m.Val args) (tokens : Tokens m.Val past)
    {a b : Marking m front} (step : Fire m front entry tokens a b) (rest : Marking m tail) :
    Fire m whole entry tokens (cut.attach m a rest) (cut.attach m b rest) := by
  induction cut with
  | stop => cases step
  | bind _ _ _ ih =>
    cases step with
    | primitive ready ran => exact .primitive ready ran
    | enter ready guard => exact .enter ready guard
    | advance step => exact .advance step
    | commit ready decision => exact .commit ready decision
    | restart ready decision entered => exact .restart ready decision entered
    | later step => exact .later (ih _ step rest)

theorem tail_step (entry : Tuple m.Val args) (tokens : Tokens m.Val past) (mark : Marking m front)
    {a b : Marking m tail} (step : Fire m tail entry (cut.tokens m tokens mark) a b) :
    Fire m whole entry tokens (cut.attach m mark a) (cut.attach m mark b) := by
  induction cut with
  | stop => exact step
  | bind _ _ _ ih => exact .later (ih _ mark.2 step)

theorem read_after (entry : Tuple m.Val args) (tokens : Tokens m.Val past) (mark : Marking m front)
    (result : Tuple m.Val bank) (done : finished m front entry tokens mark = some result) :
    read cut.wires entry (cut.tokens m tokens mark) = some result := by
  induction cut with
  | stop => exact done
  | bind _ _ _ ih =>
    cases phase : mark.1 with
    | pending => simp [finished, phase] at done
    | waiting => simp [finished, phase] at done
    | done =>
      simp only [Cut.tokens, phase, Vertex.outputs]
      exact ih _ mark.2 (by simpa only [finished, phase] using done)

theorem finished_attach (entry : Tuple m.Val args) (tokens : Tokens m.Val past)
    (prefixMark : Marking m front) (tailMark : Marking m tail) {result : Tuple m.Val bank}
    (done : finished m front entry tokens prefixMark = some result) :
    finished m whole entry tokens (cut.attach m prefixMark tailMark) =
      finished m tail entry (cut.tokens m tokens prefixMark) tailMark := by
  induction cut with
  | stop => rfl
  | bind _ _ _ ih =>
    cases phase : prefixMark.1 with
    | pending | waiting => simp [finished, phase] at done
    | done value =>
      simp only [Cut.attach, Cut.tokens, finished, phase, Vertex.outputs]
      exact ih _ prefixMark.2 tailMark (by simpa only [finished, phase] using done)

end Silmaril.SSA.RVSDG.NestedTheta.Petri.Cut.Proofs

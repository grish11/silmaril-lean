module

public import Silmaril.SSA.RVSDG.NestedTheta.Petri.Cut.Defs
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Petri.Cut.Commutation
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Petri.Cut.Correctness

/-! Publishing additional prefix colours preserves continuation firings. -/

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Petri

open RVSDG.Petri (Tokens)
open Relation (ReflTransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {args bank outs : Ports (PortType V S)}
variable {past frontSigs wholeSigs tailSigs : List (Ports (PortType V S))}
variable {front : Term Op args past frontSigs bank} {whole : Term Op args past wholeSigs outs}
variable {tail : Term Op args (extend past frontSigs) tailSigs outs}

theorem Cut.lift_prefix_step (cut : Cut front whole tail) (m : Model.{u, v, w} Op)
    (entry : Tuple m.Val args) (tokens : Tokens m.Val past) {before after : Marking m front}
    (step : Fire m front entry tokens before after) (rest : Marking m tail) :
    Fire m whole entry tokens (cut.attach m before rest) (cut.attach m after rest) :=
  Cut.Proofs.prefix_step cut m entry tokens step rest

/-- A continuation can replay its exact step with the tokens from a
later prefix marking. Every previously available colour is preserved. -/
theorem Cut.tail_after_prefix (cut : Cut front whole tail) (m : Model.{u, v, w} Op)
    (entry : Tuple m.Val args) (tokens : Tokens m.Val past) {before after : Marking m front}
    (prefixSteps : ReflTransGen (Fire m front entry tokens) before after)
    {a b : Marking m tail} (step : Fire m tail entry (cut.tokens m tokens before) a b) :
    Fire m tail entry (cut.tokens m tokens after) a b :=
  Cut.Commutation.Proofs.tail_after_prefix cut m entry tokens prefixSteps step

end Silmaril.SSA.RVSDG.NestedTheta.Petri

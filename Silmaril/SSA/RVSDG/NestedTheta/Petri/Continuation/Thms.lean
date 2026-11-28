module

public import Silmaril.SSA.RVSDG.NestedTheta.Petri.Cut.Thms
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Petri.Soundness
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Petri.Cut.Correctness

/-! Resume a legal prefix of an actual firing run, preserving its starting marking. -/

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Petri

open Relation (ReflTransGen)
open RVSDG.Petri (Tokens)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {args bank outs : Ports (PortType V S)}
variable {frontSigs wholeSigs tailSigs : List (Ports (PortType V S))}
variable (m : Model.{u, v, w} Op)

/-- If a term has a finite result, any legally reached marking admits a
legal continuation to that result. This is an existence statement about
the continuation. -/
theorem complete_reached (term : Term Op args [] wholeSigs outs)
    (entry : Tuple m.Val args) (output : Tuple m.Val outs) {mark : Marking m term}
    (steps : ReflTransGen (Fire m term entry PUnit.unit) (pending m term) mark)
    (run : term.Returns m entry output) :
    ∃ final, ReflTransGen (Fire m term entry PUnit.unit) mark final ∧
      finished m term entry PUnit.unit final = some output :=
  Proofs.complete_reached m term entry output steps run

/-- Transport a segment between two observations through the existing cut,
keeping the actual continuation marking fixed. -/
theorem Cut.prefix_between
    {past : List (Ports (PortType V S))}
    {front : Term Op args past frontSigs bank} {whole : Term Op args past wholeSigs outs}
    {tail : Term Op args (extend past frontSigs) tailSigs outs}
    (cut : Cut front whole tail) (entry : Tuple m.Val args) (tokens : Tokens m.Val past)
    {before after : Marking m front} (steps : ReflTransGen (Fire m front entry tokens) before after)
    (rest : Marking m tail) :
    ReflTransGen (Fire m whole entry tokens) (cut.attach m before rest) (cut.attach m after rest) :=
  steps.lift (fun mark => cut.attach m mark rest)
    (fun _ _ step => Cut.Proofs.prefix_step cut m entry tokens step rest)

/-- Read completion through a prefix whose colours have all been marked. -/
theorem Cut.finished_attach
    {past : List (Ports (PortType V S))}
    {front : Term Op args past frontSigs bank} {whole : Term Op args past wholeSigs outs}
    {tail : Term Op args (extend past frontSigs) tailSigs outs}
    (cut : Cut front whole tail) (entry : Tuple m.Val args) (tokens : Tokens m.Val past)
    (prefixMark : Marking m front) (tailMark : Marking m tail) {result : Tuple m.Val bank}
    (done : finished m front entry tokens prefixMark = some result) :
    finished m whole entry tokens (cut.attach m prefixMark tailMark) =
      finished m tail entry (cut.tokens m tokens prefixMark) tailMark :=
  Cut.Proofs.finished_attach cut m entry tokens prefixMark tailMark done

end Silmaril.SSA.RVSDG.NestedTheta.Petri

module

public import Silmaril.SSA.SeaOfNodes.GVN.Elimination.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GVN.Elimination.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GVN.Elimination

open Diamond (Dataflow Model Signature Ty Val ValueSort)
open RVSDG (Locals Origin Tuple Wires extend)

universe u v w

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {args : List (Ty Data)} {past sigs target : List (List (Ty Data))} {out : ValueSort Data}
variable {flow : Dataflow Op args past sigs}
/-- Splitting an extended origin reads either its old wire or a port
of the appended result. -/
theorem read_splitOrigin {head : List (Ty Data)} {t : Ty Data}
    (wire : Origin args (past ++ [head]) t) (m : Model.{u,v,w} Op)
    (entry : Tuple (Val m.value) args) (locals : Locals (Val m.value) past)
    (next : Tuple (Val m.value) head) :
    (match splitOrigin head wire with
      | .inl prior => Diamond.read m prior entry locals
      | .inr port => next.get port) = Diamond.read m wire entry (locals.snoc next) :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Elimination.read_splitOrigin m entry wire locals next

/-- Extending both stores with the same result preserves the routing invariant. -/
theorem Routing.push_agrees {route : Routing args past target} {m : Model.{u,v,w} Op}
    {entry : Tuple (Val m.value) args} {old : Locals (Val m.value) past}
    {new : Locals (Val m.value) target} (agree : route.Agrees m entry old new)
    {head : List (Ty Data)} (next : Tuple (Val m.value) head) :
    Routing.Agrees (route.push head) m entry (old.snoc next) (new.snoc next) :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Elimination.push_agrees m entry agree next

/-- Pointwise agreement across two argument banks preserves the whole ordered packet. -/
theorem Routing.wires_read_between {targetArgs ports : List (Ty Data)}
    {route : Routing args past target targetArgs} (m : Model.{u,v,w} Op)
    (entry : Tuple (Val m.value) args) (entry' : Tuple (Val m.value) targetArgs)
    (old : Locals (Val m.value) past) (new : Locals (Val m.value) target)
    (agree : route.AgreesBetween m entry entry' old new) (wires : Wires args past ports) :
    wires.read entry old = (route.wires wires).read entry' new :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Elimination.wires_read m entry agree wires

/-- Redirecting the newest singleton to an equal prefix read preserves all reads. -/
theorem dropNewest_agrees (replacement : Origin args past (.value out))
    (m : Model.{u,v,w} Op) (entry : Tuple (Val m.value) args) (locals : Locals (Val m.value) past)
    (next : Tuple (Val m.value) [.value out])
    (same : next.get .head = Diamond.read m replacement entry locals) :
    Routing.Agrees (dropNewest replacement) m entry (locals.snoc next) locals :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Elimination.drop_agrees m entry replacement locals next same

/-- Routing a suffix preserves every source wire when the incoming
producer stores agree along the supplied routing. -/
theorem routeSuffix_agrees (flow : Dataflow Op args past sigs)
    (route : Routing args past target) (m : Model.{u,v,w} Op) (entry : Tuple (Val m.value) args)
    (old : Locals (Val m.value) past) (new : Locals (Val m.value) target)
    (agree : route.Agrees m entry old new) :
    let result := routeSuffix flow route
    Routing.Agrees result.2 m entry (flow.eval m entry old) (result.1.eval m entry new) :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Elimination.routeSuffix_agrees m entry flow route old new agree

/-- Reading an inlined pure packet agrees with running the closed table on
the values of its supplied boundary wires. -/
theorem plug_read {inner ports : List (Ty Data)} (flow : Dataflow Op inner [] sigs)
    (outputs : Wires inner (extend [] sigs) ports) (inputs : Wires args past inner)
    (m : Model.{u,v,w} Op) (entry : Tuple (Val m.value) args) (locals : Locals (Val m.value) past) :
    let bound := plug flow outputs inputs
    bound.2.read entry (bound.1.eval m entry locals) =
      outputs.read (inputs.read entry locals) (flow.eval m (inputs.read entry locals) PUnit.unit) :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Elimination.plug_read m entry flow outputs inputs locals

/-- Erasure preserves every routed read when the replacement in the
producer's prefix reads the same value as the deleted binding. -/
theorem erase_agrees (candidate : Producer flow out)
    (replacement : Origin args (operandScope candidate) (.value out))
    (m : Model.{u,v,w} Op) (entry : Tuple (Val m.value) args) (locals : Locals (Val m.value) past)
    (equal : Diamond.read m candidate.origin entry (flow.eval m entry locals) =
      Diamond.read m (inFinal candidate replacement) entry (flow.eval m entry locals)) :
    let result := erase candidate replacement
    Routing.Agrees result.route m entry (flow.eval m entry locals) (result.flow.eval m entry locals) :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Elimination.erase_agrees m entry candidate replacement locals equal

/-- Typed erasure removes exactly one binding. -/
theorem erase_size (candidate : Producer flow out)
    (replacement : Origin args (operandScope candidate) (.value out)) :
    (erase candidate replacement).sigs'.length + 1 = sigs.length :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Elimination.erase_size candidate replacement

variable [DecidableEq (ValueSort Data)] [∀ ins out, DecidableEq (Op ins out)]

/-- Every old wire has the same value after applying the returned routing.
This includes reads of the deleted producer and the final result wire. -/
theorem eliminate_sound (candidate representative : Producer flow out)
    (replacement : Origin args (operandScope candidate) (.value out))
    (m : Model.{u,v,w} Op) (entry : Tuple (Val m.value) args)
    (locals : Locals (Val m.value) past) {result : Rewrite Op args past sigs}
    (accepted : eliminate? candidate representative replacement = some result) :
    Routing.Agrees result.route m entry (flow.eval m entry locals) (result.flow.eval m entry locals) :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Elimination.eliminate_sound
    m entry candidate representative replacement locals accepted

/-- A successful rewrite removes exactly one producer. -/
theorem eliminate_size (candidate representative : Producer flow out)
    (replacement : Origin args (operandScope candidate) (.value out)) {result : Rewrite Op args past sigs}
    (accepted : eliminate? candidate representative replacement = some result) :
    result.sigs'.length + 1 = sigs.length :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Elimination.eliminate_size candidate representative replacement accepted

end Silmaril.SSA.SeaOfNodes.GVN.Elimination

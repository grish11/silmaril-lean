module

public import Silmaril.SSA.SeaOfNodes.Pure.Deletion.Defs
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Deletion.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Pure.Deletion.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Pure.Deletion

open Diamond (Dataflow Model Signature Ty Val ValueSort)
open GVN (Producer)
open GVN.Cyclic.Deletion (Route erase?)
open RVSDG (Locals Tuple Wires extend)

universe u v w

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {args ports : List (Ty Data)} {past sigs : List (List (Ty Data))}
variable {out : ValueSort Data} {flow : Dataflow Op args past sigs}
variable {candidate : Producer flow out} {outputs : Wires args (extend past sigs) ports}
variable {result : Result Op args ports past sigs}

/-- Acceptance checks both the surviving table and the complete outgoing packet. -/
theorem delete?_eq_some_iff :
    delete? candidate outputs = some result ↔
      erase? candidate = some result.erasure ∧
        Route.wires? result.erasure.route outputs = some result.outputs :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.Deletion.delete?_eq_some_iff

/-- Every original read admitted by the partial map keeps its value. -/
theorem delete?_agrees (accepted : delete? candidate outputs = some result) (m : Model.{u,v,w} Op)
    (entry : Tuple (Val m.value) args) (locals : Locals (Val m.value) past) :
    Route.Agrees result.erasure.route m entry (flow.eval m entry locals)
      (result.erasure.flow.eval m entry locals) :=
  GVN.Cyclic.Deletion.erase_sound candidate m entry locals (delete?_eq_some_iff.mp accepted).1

/-- The entire outgoing packet agrees for all inputs and earlier locals. -/
theorem delete?_outputs_eq (accepted : delete? candidate outputs = some result) (m : Model.{u,v,w} Op)
    (entry : Tuple (Val m.value) args) (locals : Locals (Val m.value) past) :
    result.outputs.read entry (result.erasure.flow.eval m entry locals) =
      outputs.read entry (flow.eval m entry locals) :=
  (Route.wires_read m entry (delete?_agrees accepted m entry locals) outputs
    (delete?_eq_some_iff.mp accepted).2).symm

/-- Apart from the nominated operation, the exact typed opcodes keep their order. -/
theorem delete?_opcode_order (accepted : delete? candidate outputs = some result) :
    opcodes result.erasure.flow = (opcodes flow).eraseIdx (position candidate) :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.Deletion.erase?_opcode_order (delete?_eq_some_iff.mp accepted).1

end Silmaril.SSA.SeaOfNodes.Pure.Deletion

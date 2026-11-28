module

public import Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay.Defs
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Deletion.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Pure.SuffixReplay.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay

open Diamond (Ty Val ValueSort dataPorts)
open GVN.Cyclic.Deletion (Route)
open GVN.Elimination (Rewrite Routing)
open ConstantFold.RightSpine (WordWire)
open SubZero (model)
open RVSDG (Tuple extend)

variable {inputs : List (ValueSort Unit)} {ports : List (Ty Unit)}
variable {block : Block inputs ports} {after : State inputs ports block.sigs}
variable {requests : List (Request inputs block.sigs)}

theorem Block.program_eval (block : Block inputs ports) (entry : Tuple (Val model.value) (dataPorts inputs)) :
    block.program.eval model entry = (block.packet.read entry (block.flow.eval model entry PUnit.unit)).get .head :=
  Proofs.SSA.SeaOfNodes.Pure.SuffixReplay.program_eval entry block

/-- The two typed routes compose for all mapped reads and every outgoing wire. -/
theorem compose_agrees {first : State inputs ports block.sigs} {next : State inputs ports first.block.sigs}
    (entry : Tuple (Val model.value) (dataPorts inputs))
    (before : Agrees block first entry) (after : Agrees first.block next entry) :
    Agrees block (first.compose next) entry :=
  Proofs.SSA.SeaOfNodes.Pure.SuffixReplay.compose_agrees entry before after

/-- Embed a certified total rewrite as a partial route on the whole packet. -/
theorem fromRewrite_agrees (edit : Rewrite SubZero.Opcode (dataPorts inputs) [] block.sigs)
    (entry : Tuple (Val model.value) (dataPorts inputs))
    (agree : Routing.Agrees edit.route model entry (block.flow.eval model entry PUnit.unit)
      (edit.flow.eval model entry PUnit.unit)) :
    Agrees block (fromRewrite block edit) entry :=
  Proofs.SSA.SeaOfNodes.Pure.SuffixReplay.fromRewrite_agrees entry edit agree

/-- One accepted step preserves reads and the complete outgoing packet. -/
theorem step_agrees {action : Action} {wire : WordWire (dataPorts inputs) (extend [] block.sigs)}
    (accepted : step block action wire = .ok after) (entry : Tuple (Val model.value) (dataPorts inputs)) :
    Agrees block after entry :=
  Proofs.SSA.SeaOfNodes.Pure.SuffixReplay.step_agrees entry accepted

/-- Every successful request list preserves mapped reads and routes the complete packet. -/
theorem run_agrees (accepted : run block requests = .ok after) (entry : Tuple (Val model.value) (dataPorts inputs)) :
    Agrees block after entry :=
  Proofs.SSA.SeaOfNodes.Pure.SuffixReplay.run_agrees entry accepted

/-- Every outgoing value agrees with its original value in packet order. -/
theorem run_packet_eq (accepted : run block requests = .ok after)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    after.block.packet.read entry (after.block.flow.eval model entry PUnit.unit) =
      block.packet.read entry (block.flow.eval model entry PUnit.unit) :=
  let ok := run_agrees accepted entry
  (Route.wires_read model entry ok.1 block.packet ok.2).symm

/-- The packet's first word is the native suffix return. -/
theorem run_eval_eq (accepted : run block requests = .ok after)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    after.block.program.eval model entry = block.program.eval model entry := by
  rw [Block.program_eval, Block.program_eval, run_packet_eq accepted entry]

variable {original : List (List (Ty Unit))}

/-- A successful prefix determines the actual table and routes for the rest of the list. -/
theorem runFrom_append (state : State inputs ports original) (index : Nat)
    (pre post : List (Request inputs original)) :
    runFrom state index (pre ++ post) =
      (runFrom state index pre).bind (fun next => runFrom next (index + pre.length) post) :=
  Proofs.SSA.SeaOfNodes.Pure.SuffixReplay.runFrom_append state index pre post

/-- The first failing request reports its index and returns no prefix table. -/
theorem runFrom_refuses_at {state next : State inputs ports original} {index : Nat}
    {pre post : List (Request inputs original)} {request : Request inputs original} {reason : Reason}
    (prior : runFrom state index pre = .ok next) (failed : advance next request = .error reason) :
    runFrom state index (pre ++ request :: post) = .error ⟨index + pre.length, reason⟩ := by
  rw [runFrom_append, prior]
  simp [Except.bind, runFrom, failed]

end Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay

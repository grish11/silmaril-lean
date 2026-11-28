module

public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.SuffixReplay.Defs
import Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.SuffixReplay

open Silmaril.SSA.SeaOfNodes.Diamond
open AddPhi.Rotate (Program)
open AddPhi.Rotate.Pair.Dispatch.Materialize.SuffixReplay
open Silmaril.SSA.SeaOfNodes.Pure.SubZero (model word)
open Silmaril.SSA.RVSDG (Tuple)

variable {inputs joined : List (ValueSort Unit)} {sigs : List (List (Ty Unit))}
variable {p target : Program inputs sigs joined} {requests : List (Request p)}

private theorem accepted_state (accepted : rewrite p requests = .ok target) :
    ∃ state, Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay.run (blockOf p) requests = .ok state ∧
      target = { p with suffix := state.block.program } := by
  cases checked : Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay.run (blockOf p) requests with
  | error reason => simp [rewrite, checked, Except.map] at accepted
  | ok state =>
    exact ⟨state, rfl, by simpa [rewrite, checked, Except.map, eq_comm] using accepted⟩

theorem rewrite_preserves (accepted : rewrite p requests = .ok target) :
    target.diamond = p.diamond ∧ target.residual = p.residual ∧
      ∀ entry : Tuple (Val model.value) (dataPorts (word :: joined)),
        target.suffix.eval model entry = p.suffix.eval model entry := by
  obtain ⟨_, checked, rfl⟩ := accepted_state accepted
  exact ⟨rfl, rfl, Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay.run_eval_eq checked⟩

end Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.SuffixReplay

module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Prune.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneInfeasibleExit.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.Prune.Proofs

open Diamond.SCCP (TupleCovers)
open SeaOfNodes.MLIR (sourceInputs)
open PruneExit (InputFacts)
open Loop.MLIR.CF (TargetOp evalOp model)
open Loop.MLIR.CF.Bank (Label Values bankEnv lower)
open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Cfg)

private theorem unique_eq_some_iff (edges : Executable) (feedback : Bool) :
    uniqueSuccessor edges = some feedback ↔
      (if feedback then incomingIndex .backedge else exitIndex) ∈ edges ∧
      (if feedback then exitIndex else incomingIndex .backedge) ∉ edges := by
  cases feedback <;>
    by_cases back : incomingIndex .backedge ∈ edges <;>
    by_cases exit : exitIndex ∈ edges <;>
    simp [uniqueSuccessor, back, exit]

private theorem unique_eq_none_iff (edges : Executable) :
    uniqueSuccessor edges = none ↔ (incomingIndex .backedge ∈ edges ↔ exitIndex ∈ edges) := by
  by_cases back : incomingIndex .backedge ∈ edges <;>
    by_cases exit : exitIndex ∈ edges <;>
    simp [uniqueSuccessor, back, exit]

variable {Γ carried : List Width} {result : Width} {entrySigs headerSigs : List (List (Diamond.Ty Width))}
variable {g : Loop.MLIR.CF.Bank.Program Γ carried result entrySigs headerSigs} {facts : InputFacts Γ}
variable {input : Env Γ} {cfg : Cfg TargetOp (Label carried result) Γ [result]}

attribute [local irreducible] solve

theorem rewrite_eq_some_iff :
    rewrite g facts = some cfg ↔
      PruneExit.Bank.rewrite g facts = some cfg ∨ PruneInfeasibleExit.rewrite g facts = some cfg := by
  unfold rewrite
  rw [Option.map_eq_some_iff, PruneExit.Bank.rewrite_eq_some_iff, PruneInfeasibleExit.rewrite_eq_some_iff]
  constructor
  · rintro ⟨feedback, selected, rfl⟩
    have admitted : PruneExit.Bank.OnlySuccessor feedback g facts :=
      (unique_eq_some_iff _ _).mp selected
    cases feedback
    · exact .inl ⟨admitted, rfl⟩
    · exact .inr ⟨admitted, rfl⟩
  · rintro (⟨admitted, rfl⟩ | ⟨admitted, rfl⟩)
    · exact ⟨false, (unique_eq_some_iff _ _).mpr admitted, rfl⟩
    · exact ⟨true, (unique_eq_some_iff _ _).mpr admitted, rfl⟩

theorem rewrite_eq_none_iff :
    rewrite g facts = none ↔
      (incomingIndex .backedge ∈ (solve model g facts).1 ↔ exitIndex ∈ (solve model g facts).1) := by
  unfold rewrite
  rw [Option.map_eq_none_iff]
  exact unique_eq_none_iff _

theorem blocks_eq (rewritten : rewrite g facts = some cfg) :
    cfg.entry = (lower g).entry ∧ cfg.block .exit = (lower g).block .exit := by
  rcases rewrite_eq_some_iff.mp rewritten with exits | feedback
  · obtain ⟨_, rfl⟩ := PruneExit.Bank.rewrite_eq_some_iff.mp exits
    exact ⟨PruneExit.Bank.entry_eq g, PruneExit.Bank.exit_eq g⟩
  · obtain ⟨_, rfl⟩ := PruneInfeasibleExit.rewrite_eq_some_iff.mp feedback
    exact ⟨PruneInfeasibleExit.entry_eq g, PruneInfeasibleExit.exit_eq g⟩

theorem arrives_frame (rewritten : rewrite g facts = some cfg) (covered : TupleCovers facts (sourceInputs input))
    {via : Incoming} {count : Nat} {old : Values carried}
    (arrived : Arrives model g (sourceInputs input) via count old) :
    (cfg.block .header).eval evalOp (fun term env => term.eval env) ((bankEnv old).append input) =
      ((lower g).block .header).eval evalOp (fun term env => term.eval env) ((bankEnv old).append input) := by
  rcases rewrite_eq_some_iff.mp rewritten with exits | feedback
  · obtain ⟨admitted, rfl⟩ := PruneExit.Bank.rewrite_eq_some_iff.mp exits
    exact PruneExit.Bank.arrives_frame admitted covered arrived
  · obtain ⟨admitted, rfl⟩ := PruneInfeasibleExit.rewrite_eq_some_iff.mp feedback
    exact PruneInfeasibleExit.arrives_frame admitted covered arrived

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.Prune.Proofs

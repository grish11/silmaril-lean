module

public import Silmaril.Semantics.Function.Semantic.Defs
public import Silmaril.Semantics.Function.Thms

public section
namespace Silmaril.Semantics.Function.Proofs

theorem consecutive_path {sig : Signature} {machine : Machine sig} {context : sig.Context}
    {analysis : Analysis sig} (covers : CallGraphProblem (machine.actualCalls context) analysis)
    {source dest : Node sig} {pre post : machine.State}
    (run : Consecutive machine context source pre dest post) : CallPath (mayGraph analysis.may) source dest := by
  induction run with
  | single step => exact Relation.TransGen.single ⟨_, covers ⟨_, _, step⟩, trivial, rfl, rfl⟩
  | cons step _ ih => exact Relation.TransGen.head ⟨_, covers ⟨_, _, step⟩, trivial, rfl, rfl⟩ ih

end Silmaril.Semantics.Function.Proofs

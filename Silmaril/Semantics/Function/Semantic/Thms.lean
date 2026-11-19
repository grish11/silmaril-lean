module

public import Silmaril.Semantics.Function.Semantic.Defs
public import Silmaril.Semantics.Function.Thms
import Silmaril.Proofs.Semantics.Function.Interpretation

@[expose] public section
namespace Silmaril.Semantics.Function
variable {sig : Signature} {machine : Machine sig} {context : sig.Context}
variable {boundary : Boundaries machine} {candidates : Decomposition sig} {analysis : Analysis sig}

theorem Correspondence.body_sound (cert : Correspondence boundary context candidates analysis)
    {name : sig.Internal} {row : sig.Body} (candidate : candidates name row) :
    boundary.semanticBodies context name row := ⟨cert.region candidate, cert.exits candidate⟩

theorem Correspondence.may_cover (cert : Correspondence boundary context candidates analysis) :
    CallGraphProblem (machine.actualCalls context) analysis :=
  fun {_} ⟨_, _, step⟩ => cert.coversStep step

theorem consecutive_path (covers : CallGraphProblem (machine.actualCalls context) analysis)
    {source dest : Node sig} {pre post : machine.State}
    (run : Consecutive machine context source pre dest post) :
    CallPath (mayGraph analysis.may) source dest := Proofs.consecutive_path covers run

end Silmaril.Semantics.Function

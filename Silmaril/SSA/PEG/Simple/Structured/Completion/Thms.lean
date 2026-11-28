module

public import Silmaril.SSA.PEG.Simple.Structured.Completion.Defs
public import Silmaril.SSA.PEG.Simple.Structured.Thms
public import Silmaril.SSA.PEG.Simple.While.Thms
import Silmaril.Proofs.SSA.PEG.Simple.Structured.Completion

public section

namespace Silmaril.SSA.PEG.Simple.Structured

open RVSDG (Port Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data} {vars : List (Ty Data)} {t : Ty Data}

/-- Construct the original source trace using the shared compiled first exit.
Only the guard and complete loop-free body computations reached in this
prefix must be defined. The first pass supplies the source branch decisions. -/
theorem translate_while_trace_of_checkedPrefix (guard : Expr P vars .bool)
    (body : Stmt P false vars vars) (ret : Port vars t) (neg : P [.bool] .bool)
    (m : Interpretation.{u,v,w} P) (env : Tuple m.Value vars)
    (negSem : ∀ b : Bool, m.run neg (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (i : Index (program (whileProgram guard body.enableWhile ret) neg).nodes.length)
    {count : Nat}
    (first : readWhilePass guard body.enableWhile ret neg m
      ((translate (whileProgram guard body.enableWhile ret) neg).denote m env
        (translate_demandWellFounded (whileProgram guard body.enableWhile ret) neg)) i = some ⟨count⟩)
    (checked : checkWhilePrefix m guard body count env = true) {value : m.Value t}
    (defined : (translate (whileProgram guard body.enableWhile ret) neg).observe m
      ((translate (whileProgram guard body.enableWhile ret) neg).denote m env
        (translate_demandWellFounded (whileProgram guard body.enableWhile ret) neg)) i =
      .cons (some value) .nil) :
    ∃ final, WhileTrace m guard body.enableWhile count env final ∧ final.get ret = value :=
  Proofs.checkedTrace guard body ret neg m env negSem ((translate _ neg).denote_solves m env _)
    i first checked defined

/-- The checked completion converse of `translate_returns` for a top-level
while with a loop-free body. -/
theorem translate_while_returns_of_checkedPrefix (guard : Expr P vars .bool)
    (body : Stmt P false vars vars) (ret : Port vars t) (neg : P [.bool] .bool)
    (m : Interpretation.{u,v,w} P) (env : Tuple m.Value vars)
    (negSem : ∀ b : Bool, m.run neg (.cons ⟨b⟩ .nil) = some ⟨!b⟩) :
    let source := whileProgram guard body.enableWhile ret
    let graph := translate source neg
    let values := graph.denote m env (translate_demandWellFounded source neg)
    ∀ i {count},
      readWhilePass guard body.enableWhile ret neg m values i = some ⟨count⟩ →
      checkWhilePrefix m guard body count env = true →
      ∀ {value}, graph.observe m values i = .cons (some value) .nil → source.Returns m env value := by
  intro source graph values i count first checked value defined
  obtain ⟨final, trace, result⟩ :=
    translate_while_trace_of_checkedPrefix guard body ret neg m env negSem i first checked defined
  exact ⟨final, trace.exec, result⟩

end Silmaril.SSA.PEG.Simple.Structured

module

public import Silmaril.SSA.PEG.Simple.Structured.Completion.Token.Defs
public import Silmaril.SSA.PEG.Semantics.Thms
import Silmaril.Proofs.SSA.PEG.Simple.Structured.Token.Loop

@[expose] public section

namespace Silmaril.SSA.PEG.Simple.Structured.Token

open RVSDG (Port Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {vars : List (Ty Data)} {t : Ty Data}

theorem Body.source_ofStmt {outs : List (Ty Data)} (stmt : Stmt P false vars outs) :
    (Body.ofStmt stmt).source = stmt :=
  Proofs.sourceOfStmt stmt

variable (guard : Expr P vars .bool) (body : Body P vars vars) (ret : Port vars t)
variable (neg : P [.bool] .bool)

theorem translate_rank :
    (Structured.rank (program guard body ret neg).nodes.length).check
      (translate guard body ret neg) = true :=
  Structured.Proofs.rankChecked (program guard body ret neg).code (program guard body ret neg).refs

theorem translate_demandWellFounded : WellFounded (translate guard body ret neg).Demand :=
  (translate guard body ret neg).demandWellFounded_of_check _ (translate_rank guard body ret neg)

variable (m : Interpretation.{u,v,w} P) (env : Tuple m.Value vars)

noncomputable def observe (i : Index (program guard body ret neg).nodes.length) :
    Tuple (fun t => Option (m.Value t)) [t, .bool] :=
  let g := translate guard body ret neg
  g.observe (model m) (g.denote (model m) env (translate_demandWellFounded guard body ret neg)) i

/-- A successful run of the original source defines both ordered roots. -/
theorem observe_of_returns
    (negSem : ∀ b : Bool, m.run neg (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (i : Index (program guard body ret neg).nodes.length)
    {value : m.Value t} (ran : (source guard body ret).Returns m env value) :
    observe guard body ret neg m env i = .cons (some value) (.cons (some ⟨true⟩) .nil) :=
  (Proofs.correspondence guard body ret neg m env negSem
    ((translate guard body ret neg).denote_solves (model m) env _) i).1 ran

/-- The completion root alone suffices to reconstruct a successful source
run, which also defines the original data result. -/
theorem returns_of_completion
    (negSem : ∀ b : Bool, m.run neg (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (i : Index (program guard body ret neg).nodes.length)
    (done : ((observe guard body ret neg m env i).get (.tail .head)).isSome) :
    ∃ value, (source guard body ret).Returns m env value ∧
      observe guard body ret neg m env i = .cons (some value) (.cons (some ⟨true⟩) .nil) :=
  (Proofs.correspondence guard body ret neg m env negSem
    ((translate guard body ret neg).denote_solves (model m) env _) i).2 done

end Silmaril.SSA.PEG.Simple.Structured.Token

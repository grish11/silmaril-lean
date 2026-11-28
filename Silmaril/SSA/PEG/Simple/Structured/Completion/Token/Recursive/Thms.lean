module

public import Silmaril.SSA.PEG.Simple.Structured.Completion.Token.Recursive.Defs
public import Silmaril.SSA.PEG.Semantics.Thms
import Silmaril.Proofs.SSA.PEG.Simple.Structured.Token.Recursive.Correctness

@[expose] public section

namespace Silmaril.SSA.PEG.Simple.Structured.Token.Recursive

open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params : List (Ty Data)} {t : Ty Data}
variable (p : Program P true params t) (neg : P [.bool] .bool)

theorem translate_rank :
    (Structured.rank (program p neg).nodes.length).check (translate p neg) = true :=
  Structured.Proofs.rankChecked (program p neg).code (program p neg).refs

theorem translate_demandWellFounded : WellFounded (translate p neg).Demand :=
  (translate p neg).demandWellFounded_of_check _ (translate_rank p neg)

variable (m : Interpretation.{u,v,w} P) (env : Tuple m.Value params)

noncomputable def observe (i : Index (program p neg).nodes.length) :
    Tuple (fun t => Option (m.Value t)) [t, .bool] :=
  let g := translate p neg
  g.observe (model m) (g.denote (model m) env (translate_demandWellFounded p neg)) i

/-- Success defines both ordered roots of the recursive compilation. -/
theorem observe_of_returns
    (negSem : ∀ b : Bool, m.run neg (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (i : Index (program p neg).nodes.length)
    {value : m.Value t} (ran : p.Returns m env value) :
    observe p neg m env i = .cons (some value) (.cons (some ⟨true⟩) .nil) :=
  (Proofs.correspondence p neg m env negSem ((translate p neg).denote_solves (model m) env _) i).1 ran

/-- The emitted marker alone reconstructs a successful execution of the
original program and defines the matching data return. -/
theorem returns_of_completion
    (negSem : ∀ b : Bool, m.run neg (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (i : Index (program p neg).nodes.length)
    (done : ((observe p neg m env i).get (.tail .head)).isSome) :
    ∃ value, p.Returns m env value ∧
      observe p neg m env i = .cons (some value) (.cons (some ⟨true⟩) .nil) :=
  (Proofs.correspondence p neg m env negSem ((translate p neg).denote_solves (model m) env _) i).2 done

end Silmaril.SSA.PEG.Simple.Structured.Token.Recursive

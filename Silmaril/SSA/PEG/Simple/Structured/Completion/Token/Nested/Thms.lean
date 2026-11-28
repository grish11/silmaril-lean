module

public import Silmaril.SSA.PEG.Simple.Structured.Completion.Token.Nested.Defs
public import Silmaril.SSA.PEG.Simple.While.Thms
import Silmaril.Proofs.SSA.PEG.Simple.Structured.Token.Nested

@[expose] public section

namespace Silmaril.SSA.PEG.Simple.Structured.Token.Nested

open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {outer child : List (Ty Data)} {t : Ty Data}
variable (f : Form P outer child t) (neg : P [.bool] .bool)

theorem Form.translate_rank :
    (Structured.rank (f.program neg).nodes.length).check (f.translate neg) = true :=
  Structured.Proofs.rankChecked (f.program neg).code (f.program neg).refs

theorem Form.translate_demandWellFounded : WellFounded (f.translate neg).Demand :=
  (f.translate neg).demandWellFounded_of_check _ (f.translate_rank neg)

variable (m : Interpretation.{u,v,w} P) (env : Tuple m.Value outer)

noncomputable def Form.values : (f.translate neg).Valuation (model m) :=
  (f.translate neg).denote (model m) env (f.translate_demandWellFounded neg)

noncomputable def Form.observe (i : Index (f.program neg).nodes.length) :
    Tuple (fun t => Option (m.Value t)) [t, .bool] :=
  (f.translate neg).observe (model m) (f.values neg m env) i

theorem Form.observe_of_returns
    (negSem : ∀ b : Bool, m.run neg (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (i : Index (f.program neg).nodes.length)
    {value : m.Value t} (ran : f.source.Returns m env value) :
    f.observe neg m env i = .cons (some value) (.cons (some ⟨true⟩) .nil) :=
  (Proofs.correspondence f neg m env negSem ((f.translate neg).denote_solves (model m) env _) i).1 ran

/-- Decode the emitted completion root into the original outer source
trace. Every continuing step has its own defined child pass and token.
Zero trips require no child observation. -/
theorem Form.trace_of_completion
    (negSem : ∀ b : Bool, m.run neg (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (i : Index (f.program neg).nodes.length) (done : ((f.observe neg m env i).get (.tail .head)).isSome) :
    ∃ count final, WhileTrace m f.guard f.step count env final ∧
      f.observe neg m env i = .cons (some (final.get f.result)) (.cons (some ⟨true⟩) .nil) ∧
      (f.outerPass neg).read m.carrier (f.values neg m env ((f.outerPass neg).id, i)) = some ⟨count⟩ ∧
      ∀ j < count, ∃ trips, f.childExit neg m (f.values neg m env) (i.set (f.outerPass neg).id j) trips :=
  (Proofs.correspondence f neg m env negSem ((f.translate neg).denote_solves (model m) env _) i).2 done

theorem Form.returns_of_completion
    (negSem : ∀ b : Bool, m.run neg (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (i : Index (f.program neg).nodes.length) (done : ((f.observe neg m env i).get (.tail .head)).isSome) :
    ∃ value, f.source.Returns m env value ∧
      f.observe neg m env i = .cons (some value) (.cons (some ⟨true⟩) .nil) := by
  obtain ⟨_, final, trace, observed, _⟩ := f.trace_of_completion neg m env negSem i done
  exact ⟨final.get f.result, ⟨final, trace.exec, rfl⟩, observed⟩

end Silmaril.SSA.PEG.Simple.Structured.Token.Nested

module

public import Silmaril.Proofs.Logic.Reachability.AllPath

@[expose] public section
namespace Silmaril.Logic.Reachability

variable {S : Type} {cfg : S} {A : Signature cfg}

/-- A local circular invariant proves an actual all-path reachability sentence
in the existing institution, uniformly for every captured object assignment. -/
theorem Sentence.allPath_of_invariant (M : Model cfg A) (p : Sentence cfg A)
    (mode : p.mode = .allPath)
    (I : ((i : Fin p.variableCount) → M.carrier (p.context i)) → M.carrier cfg → Prop)
    (pre : ∀ v w, w ∈ M.denote v p.pre → I v w)
    (progress : ∀ v, AllPathInvariant (step cfg M) (fun w => w ∈ M.denote v p.post) (I v)) :
    p.Satisfies cfg M := by
  intro v w hw
  rw [mode]
  exact (progress v).sound w (pre v w hw)

/-- The existing all-path institution's truth condition has an exact local
progress characterization; neither the model objects nor their arrows change. -/
theorem Sentence.allPath_iff_invariant (M : Model cfg A) (p : Sentence cfg A)
    (mode : p.mode = .allPath) :
    p.Satisfies cfg M ↔
      ∀ v : (i : Fin p.variableCount) → M.carrier (p.context i),
        ∃ I : M.carrier cfg → Prop,
          (∀ w, w ∈ M.denote v p.pre → I w) ∧
          AllPathInvariant (step cfg M) (fun w => w ∈ M.denote v p.post) I := by
  constructor
  · intro h v
    refine ⟨AllPartial (step cfg M) (fun w => w ∈ M.denote v p.post), ?_,
      allPartial_invariant _ _⟩
    intro w hw
    have holds := h v w hw
    rw [mode] at holds
    exact holds
  · intro h v w hw
    obtain ⟨I, hpre, hI⟩ := h v
    rw [mode]
    exact hI.sound w (hpre w hw)

end Silmaril.Logic.Reachability

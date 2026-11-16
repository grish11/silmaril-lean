module

public import Silmaril.Containers.Behaviour.Defs
import Silmaril.Proofs.Containers.Behaviour.Basic

/-!
# Behaviours: theorems

PROVED (standard axioms). Proofs longer than a few lines are in
`Silmaril.Proofs.Containers.Behaviour` and only pointed at from here.

**Specifications.**

* `Model.Sat.mono`, `Model.Sat.and`: satisfaction is monotone and conjunctive;
* `Spec.totalCorrect_partialCorrect`: total correctness implies partial correctness;
* `Model.sat_partialCorrect_of_noExit`: a model none of whose runs exits (it crashes, spins,
  blocks or is killed) satisfies **every** partial-correctness specification: partial
  correctness alone says nothing about crashes or divergence.

**Refinement.**

* `Model.Refines.sat`: behaviour inclusion preserves every specification;
* `Model.Refines.traceRefines`: it implies trace inclusion;
* `Model.TraceRefines.safe`: trace inclusion preserves safety;
* `traceRefines_not_total`: but not total correctness: a silently diverging process
  trace-refines one that exits at once.

**Noninterference.**

* `noninterference_not_trace_property`: no specification of single runs is equivalent to
  noninterference;
* `trace_property_not_noninterference`: a trace property (memory safety, no arbitrary code
  execution, confinement to a profile) that holds of two runs which each send one octet and exit
  does not imply noninterference, even though each run alone is harmless.
-/

public section

namespace Silmaril.Containers

variable {E : Type}

theorem Model.Sat.mono {M : Model E} {φ ψ : Spec E} (h : M.Sat φ) (hφ : ∀ b, φ b → ψ b) :
    M.Sat ψ := fun b hb => hφ b (h b hb)

theorem Model.Sat.and {M : Model E} {φ ψ : Spec E} (h₁ : M.Sat φ) (h₂ : M.Sat ψ) :
    M.Sat fun b => φ b ∧ ψ b := fun b hb => ⟨h₁ b hb, h₂ b hb⟩

theorem Spec.totalCorrect_partialCorrect {post : List E → UInt8 → Prop} {b : Beh E}
    (h : Spec.totalCorrect post b) : Spec.partialCorrect post b := by
  rcases b with ⟨t, s⟩ | _ | _ | _ <;> try exact h.elim
  cases s <;> first | exact h | exact h.elim

theorem Model.sat_partialCorrect_of_noExit {M : Model E}
    (h : ∀ t c, ¬ M (.done t (.exited c))) (post : List E → UInt8 → Prop) :
    M.Sat (Spec.partialCorrect post) := by
  intro b hb
  rcases b with ⟨t, s⟩ | _ | _ | _ <;> try trivial
  cases s with
  | exited c => exact (h t c hb).elim
  | _ => trivial

theorem Model.Refines.sat {M N : Model E} (h : M.Refines N) {φ : Spec E} (hN : N.Sat φ) :
    M.Sat φ := fun b hb => hN b (h b hb)

theorem Model.Refines.traceRefines {M N : Model E} (h : M.Refines N) : M.TraceRefines N :=
  fun _ ⟨b, hb, ht⟩ => ⟨b, h b hb, ht⟩

theorem Model.TraceRefines.safe {M N : Model E} (h : M.TraceRefines N) {S : List E → Prop}
    (hN : N.Sat (Spec.safe S)) : M.Sat (Spec.safe S) :=
  fun b hb t ht => let ⟨b', hb', ht'⟩ := h t ⟨b, hb, ht⟩; hN b' hb' t ht'

/-- A silently diverging process trace-refines one that exits at once, but only the latter is
totally correct. -/
theorem traceRefines_not_total :
    let M : Model Unit := (· = .spins [])
    let N : Model Unit := (· = .done [] (.exited 0))
    M.TraceRefines N ∧ N.Sat (Spec.totalCorrect fun _ _ => True) ∧
      ¬ M.Sat (Spec.totalCorrect fun _ _ => True) :=
  Silmaril.Proofs.Containers.Behaviour.traceRefines_not_total

/-- No property of single runs is equivalent to noninterference. -/
theorem noninterference_not_trace_property :
    ¬ ∃ φ : Spec Bool, ∀ M : Model Bool,
      Model.Noninterference (fun _ => ()) id M ↔ M.Sat φ :=
  Silmaril.Proofs.Containers.Behaviour.noninterference_not_trace_property

/-- A trace property that allows each of two runs (one sends `true` and exits, the other sends
`false` and exits) does not imply noninterference. -/
theorem trace_property_not_noninterference (φ : Spec Bool)
    (h₁ : φ (.done [true] (.exited 0))) (h₂ : φ (.done [false] (.exited 0))) :
    ¬ ∀ M : Model Bool, M.Sat φ → Model.Noninterference (fun _ => ()) id M :=
  Silmaril.Proofs.Containers.Behaviour.trace_property_not_noninterference φ h₁ h₂

end Silmaril.Containers

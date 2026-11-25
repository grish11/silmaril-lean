module

public import Silmaril.Semantics.Calco2019.Examples.Printing.Defs

public section

namespace Silmaril.Calco2019.Examples.Printing.Proofs

variable {A : Type*}

theorem writer_no_fixpoint (a : A) :
    ¬ ∃ g, writerStep (writerForever a) g = g := by
  rintro ⟨g, hg⟩
  have h := congrArg (fun q => (q ()).1.length) hg
  simp [writerStep, writerForever] at h

theorem writerForever_guarded (a : A) : WriterGuarded (writerForever a) := by
  intro x z _
  simp [writerForever]

theorem writerForever_divergence (a : A) :
    writerWithDivergenceStep (writerForever a) (fun _ => none) = fun _ => none := by
  rfl

theorem traceLoop_guarded (a : A) : TraceGuarded (traceLoop a) := by
  intro x z word h
  simp [traceLoop] at h
  simp [h]

private theorem trace_step_iff (a : A) (g : Unit → Set (Trace A Unit)) (x : Unit) (t : Trace A Unit) :
    t ∈ traceStep (traceLoop a) g x ↔
      t = .inl ([], ()) ∨ ∃ tail ∈ g (), t = prepend [a] tail := by
  change (_ ∨ _ ∨ _) ↔ _
  simp [traceLoop, Subsingleton.elim (α := Unit) _ ()]

private theorem prefix_const (a : A) :
    prepend [a] (Sum.inr (fun _ => a) : Trace A Unit) = Sum.inr (fun _ => a) := by
  apply congrArg Sum.inr
  funext n
  cases n <;> rfl

theorem finite_fixpoint (a : A) : traceStep (traceLoop a) (finiteSolution a) = finiteSolution a := by
  funext x
  ext t
  rw [trace_step_iff]
  constructor
  · rintro (h | ⟨tail, ⟨n, rfl⟩, h⟩)
    · exact ⟨0, h⟩
    · exact ⟨n + 1, h⟩
  · rintro ⟨n, rfl⟩
    cases n with
    | zero => exact Or.inl rfl
    | succ n => exact Or.inr ⟨_, ⟨n, rfl⟩, rfl⟩

theorem productive_fixpoint (a : A) :
    traceStep (traceLoop a) (productiveSolution a) = productiveSolution a := by
  funext x
  ext t
  rw [trace_step_iff]
  constructor
  · rintro (h | ⟨tail, htail, h⟩)
    · exact Or.inr ⟨0, h⟩
    · rcases htail with rfl | ⟨n, rfl⟩
      · exact Or.inl (h.trans (prefix_const a))
      · exact Or.inr ⟨n + 1, h⟩
  · rintro (rfl | ⟨n, rfl⟩)
    · exact Or.inr ⟨_, Or.inl rfl, (prefix_const a).symm⟩
    · cases n with
      | zero => exact Or.inl rfl
      | succ n => exact Or.inr ⟨_, Or.inr ⟨n, rfl⟩, rfl⟩

theorem solutions_distinct (a : A) : finiteSolution a ≠ productiveSolution a := by
  intro h
  have hs : (Sum.inr fun _ => a) ∈ productiveSolution a () := Or.inl rfl
  rw [← h] at hs
  obtain ⟨_, heq⟩ := hs
  cases heq

theorem silent_loop_unguarded (A : Type*) :
    ¬ TraceGuarded (fun _ : Unit => ({Sum.inl ([], Sum.inr ())} : Set (Trace A (Unit ⊕ Unit)))) := by
  intro h
  exact h () () [] (by simp) rfl

end Silmaril.Calco2019.Examples.Printing.Proofs

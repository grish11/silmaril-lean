module

public import Silmaril.Semantics.Calco2019.Examples.Printing.Defs
import Silmaril.Proofs.Semantics.Calco2019.Examples.Printing

/-! # Fixpoints of the CALCO writer and trace loops -/

public section

namespace Silmaril.Calco2019.Examples.Printing

variable {A : Type*}

theorem writerForever_guarded (a : A) : WriterGuarded (writerForever a) :=
  Proofs.writerForever_guarded a

/-- Example 20(4)'s guarded writer loop would require a finite word equal to its own
extension by one letter. -/
theorem writer_no_fixpoint (a : A) : ¬ ∃ g, writerStep (writerForever a) g = g :=
  Proofs.writer_no_fixpoint a

theorem writerForever_divergence (a : A) :
    writerWithDivergenceStep (writerForever a) (fun _ => none) = fun _ => none :=
  Proofs.writerForever_divergence a

theorem traceLoop_guarded (a : A) : TraceGuarded (traceLoop a) :=
  Proofs.traceLoop_guarded a

theorem finite_fixpoint (a : A) :
    traceStep (traceLoop a) (finiteSolution a) = finiteSolution a :=
  Proofs.finite_fixpoint a

theorem productive_fixpoint (a : A) :
    traceStep (traceLoop a) (productiveSolution a) = productiveSolution a :=
  Proofs.productive_fixpoint a

theorem solutions_distinct (a : A) : finiteSolution a ≠ productiveSolution a :=
  Proofs.solutions_distinct a

theorem finite_subset_productive (a : A) (x : Unit) :
    finiteSolution a x ⊆ productiveSolution a x := fun _ h => Or.inr h

theorem solutions_nonempty (a : A) (x : Unit) :
    (finiteSolution a x).Nonempty ∧ (productiveSolution a x).Nonempty :=
  ⟨⟨_, ⟨0, rfl⟩⟩, ⟨_, Or.inl rfl⟩⟩

theorem silent_loop_unguarded (A : Type*) :
    ¬ TraceGuarded (fun _ : Unit => ({Sum.inl ([], Sum.inr ())} : Set (Trace A (Unit ⊕ Unit)))) :=
  Proofs.silent_loop_unguarded A

end Silmaril.Calco2019.Examples.Printing

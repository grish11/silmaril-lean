module

public import Silmaril.SSA.Isotope.Calco2019.Resumption.Defs

public section

universe u v w

namespace Silmaril.Isotope.Calco2019.Resumption.Machine.Proofs

open Isotope.LambdaSSA.Semantics Isotope.LambdaSSA.Resumption

variable {α : Type u} {Φ : Type v} {σ : Type w}
  {instr : Φ → Value α → σ → Value α → σ → Prop}

theorem Boundary.deterministic (det : InstrDeterministic instr)
    {s : Configuration α Φ σ} {o p : Answer α σ ⊕ Configuration α Φ σ}
    (first : Boundary instr s o) (second : Boundary instr s p) : o = p := by
  induction first generalizing p with
  | term => cases second with | term => rfl | admin h _ => cases h
  | region => cases second with | region => rfl | admin h _ => cases h
  | instruction h =>
    cases second with
    | instruction h' =>
      obtain ⟨rfl, rfl⟩ := det _ _ _ _ _ _ _ h h'
      rfl
    | admin h' _ => cases h'
  | admin h _ ih =>
    cases second with
    | term => cases h
    | region => cases h
    | instruction => cases h
    | admin h' tail =>
      cases h.deterministic h'
      exact ih tail

theorem observe_eq_iff (det : InstrDeterministic instr)
    {s : Configuration α Φ σ} {o : Answer α σ ⊕ Configuration α Φ σ} :
    observe instr s = some o ↔ Boundary instr s o := by
  classical
  unfold observe
  split
  · rename_i existsBoundary
    exact ⟨fun e => (Option.some.inj e) ▸ existsBoundary.choose_spec,
      fun h => congrArg some (Boundary.deterministic det existsBoundary.choose_spec h)⟩
  · rename_i noBoundary
    constructor
    · intro h
      cases h
    · exact fun h => (noBoundary ⟨_, h⟩).elim

private def destination : Answer α σ ⊕ Configuration α Φ σ → Configuration α Φ σ
  | .inl (r, s) => (r.control, s)
  | .inr c => c

private theorem Boundary.run {c : Configuration α Φ σ} {o : Answer α σ ⊕ Configuration α Φ σ}
    (h : Boundary instr c o) :
    Run instr c.1 c.2 (destination o).1 (destination o).2 := by
  induction h with
  | term | region => exact .refl
  | instruction h => exact .single (.instruction h)
  | admin h _ ih => exact .head (.admin h) ih

private theorem finite_return_run (det : InstrDeterministic instr)
    {source : Configuration α Φ σ} {answer : Answer α σ}
    (h : FiniteReturn (observe instr) source answer) :
    Run instr source.1 source.2 answer.1.control answer.2 := by
  induction h with
  | done h => exact Boundary.run ((observe_eq_iff det).mp h)
  | next h _ ih => exact (Boundary.run ((observe_eq_iff det).mp h)).trans ih

theorem finite_return_iff_run (det : InstrDeterministic instr) {c : Control α Φ}
    {s t : σ} {r : Result α} :
    FiniteReturn (observe instr) (c, s) (r, t) ↔ Run instr c s r.control t := by
  constructor
  · exact finite_return_run det
  · intro h
    generalize e : r.control = last at h
    induction h with
    | refl =>
      cases e
      exact .done ((observe_eq_iff det).mpr (by cases r with
        | term => exact .term
        | region => exact .region))
    | head h _ ih =>
      have tail := ih e
      cases h with
      | admin h =>
        cases tail with
        | done h' => exact .done ((observe_eq_iff det).mpr (.admin h ((observe_eq_iff det).mp h')))
        | next h' finish =>
          exact .next ((observe_eq_iff det).mpr (.admin h ((observe_eq_iff det).mp h'))) finish
      | instruction h =>
        exact .next ((observe_eq_iff det).mpr (.instruction h)) tail

end Silmaril.Isotope.Calco2019.Resumption.Machine.Proofs

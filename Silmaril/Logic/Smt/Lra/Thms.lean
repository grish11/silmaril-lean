module

public import Silmaril.Logic.Smt.Lra.Defs

@[expose] public section
namespace Silmaril.Logic.Smt.Lra

theorem Problem.entails_iff_unsat_not (P : Problem) (p : Formula) :
    P.Entails p ↔ Problem.Unsat (Formula.not p :: P) := by
  classical
  constructor
  · intro h
    rintro ⟨M, hM⟩
    exact hM (.not p) (by simp) (h M (fun q hq => hM q (by simp [hq])))
  · intro h M hM
    by_contra hn
    apply h
    refine ⟨M, ?_⟩
    intro q hq
    rcases List.mem_cons.mp hq with hq | hq
    · subst q
      exact hn
    · exact hM q hq
end Silmaril.Logic.Smt.Lra

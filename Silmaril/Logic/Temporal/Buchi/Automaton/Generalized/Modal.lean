module

public import Silmaril.Logic.Temporal.Buchi.Automaton.Generalized.Thms
public import Silmaril.Logic.Temporal.Buchi.Automaton.Base.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Temporal.Buchi.Automaton.Generalized
open ModalMu CategoryTheory

/-- Actual closed scalar syntax on the original model, via the round-robin and
ordinary base-model compilers. -/
def Symbolic.formula {S : Signature} {n k : Nat} (A : Symbolic S.Atom n k)
    (a : S.Action) : Formula S 0 := Base.formula A.compile a

theorem formula_correct {S : Signature} {n k : Nat} (A : Symbolic S.Atom n k)
    (a : S.Action) (M : Model S) (ρ : Env M.World 0) (w : M.World) :
    w ∈ (A.formula a).denote M ρ ↔ A.AcceptsPath (M.step a) (modelLabel M) w :=
  (Base.formula_correct A.compile a M ρ w).trans
    (acceptsPath_compile A (M.step a) (modelLabel M) w)

theorem formula_map {S T : Signature} {n k : Nat} (A : Symbolic S.Atom n k)
    (f : S ⟶ T) (a : S.Action) :
    (A.formula a).map f = (A.map f.atom).formula (f.action a) := by
  unfold Symbolic.formula
  rw [Base.formula_map, compile_map]

end Silmaril.Logic.Temporal.Buchi.Automaton.Generalized

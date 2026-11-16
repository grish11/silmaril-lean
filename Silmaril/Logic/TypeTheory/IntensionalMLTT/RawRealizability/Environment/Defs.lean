module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability.Algebra.Thms

@[expose] public section

namespace Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability

/-- Assign each source variable an actual quotient value in the target scope. -/
abbrev Environment (n m : ℕ) := Fin n → Value m

/-- Interpret full source syntax by capture-avoiding substitution of representatives. -/
noncomputable def eval {n m : ℕ} (t : Term n) (ρ : Environment n m) : Value m :=
  ofTerm (t.subst (fun i => rep (ρ i)))

/-- Simultaneous substitution on actual quotient values. Representative independence is proved. -/
noncomputable def qsubst {n m : ℕ} (q : Value n) (ρ : Environment n m) : Value m :=
  eval (rep q) ρ

noncomputable def qrename {n m : ℕ} (q : Value n) (r : Fin n → Fin m) : Value m :=
  ofTerm ((rep q).rename r)

def variableEnv (n : ℕ) : Environment n n := fun i => ofTerm (.var i)

noncomputable def liftEnv {n m : ℕ} (ρ : Environment n m) : Environment (n + 1) (m + 1) :=
  Fin.cons (ofTerm (.var 0)) (fun i => qrename (ρ i) Fin.succ)

end Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability

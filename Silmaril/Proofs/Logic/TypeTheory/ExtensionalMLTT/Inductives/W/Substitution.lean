module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Defs

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Tm

@[simp]
theorem liftSub_id (n : ℕ) : liftSub (fun i : Fin n => Tm.bv i) = fun i => .bv i := by
  funext i
  cases i using Fin.cases <;> simp [liftSub, wk0, wkn]

/-- Substituting each bound variable by itself preserves all terms, including W binders. -/
@[simp]
theorem bsubst_id {k : ℕ} (t : Tm k) : t.bsubst (fun i => .bv i) = t := by
  induction t <;> simp_all [bsubst]

/-- Removing an unused outermost variable reverses extension of the scope. -/
theorem open_castLE {n m : ℕ} (t : Tm n) (h : n ≤ m) (x : String) :
    (t.castLE (Nat.le_succ_of_le h)).open x = t.castLE h := by
  induction t generalizing m with
  | bv i =>
    simp only [castLE, Tm.open]
    change Fin.lastCases (.fv x) Tm.bv (i.castLE h).castSucc = Tm.bv (i.castLE h)
    exact Fin.lastCases_castSucc _
  | _ => simp_all [castLE, Tm.open]

/-- Substitution traverses the position-family binder of W formation. -/
theorem bsubst_wtype {n m : ℕ} (σ : Fin n → Tm m) (A : Tm n) (B : Tm (n + 1)) :
    (Tm.wtype A B).bsubst σ = .wtype (A.bsubst σ) (B.bsubst (liftSub σ)) := rfl

/-- Substitution traverses both the label family and the dependent motive. -/
theorem bsubst_wrec {n m : ℕ} (σ : Fin n → Tm m) (A : Tm n)
    (B C : Tm (n + 1)) (s t : Tm n) :
    (Tm.wrec A B C s t).bsubst σ = .wrec (A.bsubst σ) (B.bsubst (liftSub σ))
      (C.bsubst (liftSub σ)) (s.bsubst σ) (t.bsubst σ) := rfl

/-- A variable-dependent family and motive expose all de Bruijn indices of the telescope. -/
theorem wStepType_named (A B C : String) :
    wStepType (.fv A) (.app (.fv B) (.bv 0)) (.app (.fv C) (.bv 0)) =
      .pi (.fv A)
        (.pi (.pi (.app (.fv B) (.bv 0)) (.wtype (.fv A) (.app (.fv B) (.bv 0))))
          (.pi (.pi (.app (.fv B) (.bv 1)) (.app (.fv C) (.app (.bv 1) (.bv 0))))
            (.app (.fv C) (.sup (.fv A) (.app (.fv B) (.bv 0)) (.bv 2) (.bv 1))))) := rfl

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Tm

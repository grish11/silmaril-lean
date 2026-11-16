module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.BinderSemantics
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Finite.Structural

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

universe u

noncomputable section

/-- Substituting in a one-variable term evaluates its argument in that variable. -/
theorem Tm.denoteIn_lst0 (U : ℕ → ZFSet.{u}) (ρ : String → ZFSet.{u})
    (t : Tm 1) (a : Tm 0) :
    (t.lst a).denoteIn U ρ Fin.elim0 = t.denoteIn U ρ (Fin.cons (a.denoteIn U ρ Fin.elim0) Fin.elim0) := by
  rw [Tm.denoteIn_lst, snoc_empty]

/-- Nondependent arrows are constant-fibre dependent products. -/
theorem Tm.denoteIn_arr (U : ℕ → ZFSet.{u}) (ρ : String → ZFSet.{u})
    (A B : Tm 0) :
    (Tm.arr A B).denoteIn U ρ Fin.elim0 =
      SetSem.pi (A.denoteIn U ρ Fin.elim0) (fun _ => B.denoteIn U ρ Fin.elim0) := by
  simp only [Tm.arr, Tm.denoteIn]
  congr 1
  funext z
  exact Tm.denoteIn_wk0 U ρ Fin.elim0 B z


private theorem one_env (z : ZFSet.{u}) :
    (fun _ : Fin 1 => z) = Fin.cons z Fin.elim0 := by
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  cases hi
  rfl

private theorem cons_two (a b c : ZFSet.{u}) :
    (Fin.cons a (Fin.cons b (Fin.cons c Fin.elim0)) : Fin 3 → ZFSet.{u}) 2 = c := rfl

private theorem one_castLE_env {m : ℕ} (β : Fin (m + 1) → ZFSet.{u}) (h : 1 ≤ m + 1) :
    (fun i : Fin 1 => β (i.castLE h)) = Fin.cons (β 0) Fin.elim0 := by
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  cases hi
  rfl

/-- The object step telescope interprets as the precise graph-model W step type. -/
theorem Tm.denoteIn_wStepType (U : ℕ → ZFSet.{u}) (ρ : String → ZFSet.{u})
    (A : Tm 0) (B C : Tm 1) :
    (Tm.wStepType A B C).denoteIn U ρ Fin.elim0 =
      WSet.stepType (A.denoteIn U ρ Fin.elim0)
        (fun a => B.denoteIn U ρ (Fin.cons a Fin.elim0))
        (fun t => C.denoteIn U ρ (Fin.cons t Fin.elim0)) := by
  simp only [Tm.wStepType, Tm.denoteIn, Tm.denoteIn_bsubst, Tm.denoteIn_castLE_closed,
    Tm.denoteIn_castLE, Fin.cons_zero, Fin.cons_one, cons_two, one_env, one_castLE_env, WSet.stepType]

private theorem denoteIn_wkn1 (U : ℕ → ZFSet.{u}) (ρ : String → ZFSet.{u})
    (t : Tm 1) (a b : ZFSet.{u}) :
    (t.wkn 1).denoteIn U ρ (Fin.cons a (Fin.cons b Fin.elim0)) =
      t.denoteIn U ρ (Fin.cons a Fin.elim0) := by
  rw [Tm.denoteIn_wkn]
  apply congrArg (fun β => t.denoteIn U ρ β)
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  cases hi
  rfl

/-- The object iota lambda denotes the graph of recursive calls on the child graph. -/
theorem Tm.denoteIn_recChildren (U : ℕ → ZFSet.{u}) (ρ : String → ZFSet.{u})
    (A : Tm 0) (B C : Tm 1) (s a f : Tm 0) :
    (Tm.recChildren A B C s a f).denoteIn U ρ Fin.elim0 =
      SetSem.lam (B.denoteIn U ρ (Fin.cons (a.denoteIn U ρ Fin.elim0) Fin.elim0))
        (fun b => WSet.wrec (A.denoteIn U ρ Fin.elim0)
          (fun a => B.denoteIn U ρ (Fin.cons a Fin.elim0)) (s.denoteIn U ρ Fin.elim0)
          (SetSem.app (f.denoteIn U ρ Fin.elim0) b)) := by
  simp only [Tm.recChildren, Tm.denoteIn, Tm.denoteIn_lst0, Tm.denoteIn_wk0,
    Fin.cons_zero, denoteIn_wkn1]

end
end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

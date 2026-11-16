module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Structural

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

universe u

noncomputable section

/-- The one-entry bound environment can be built from either end. -/
theorem snoc_empty (z : ZFSet.{u}) :
    (Fin.snoc (Fin.elim0 : Fin 0 → ZFSet.{u}) z : Fin 1 → ZFSet.{u}) =
      (Fin.cons z Fin.elim0 : Fin 1 → ZFSet.{u}) := by
  funext i
  have hi : i = 0 := by
    apply Fin.ext
    have hi : i.val < 1 := i.isLt
    omega
  subst i
  rfl

/-- Substituting in a one-variable term evaluates its argument in that variable. -/
theorem Tm.denote_lst0 (T : SetHierarchy.{u}) (ρ : String → ZFSet.{u})
    (t : Tm 1) (a : Tm 0) :
    (t.lst a).denote T ρ Fin.elim0 = t.denote T ρ (Fin.cons (a.denote T ρ Fin.elim0) Fin.elim0) := by
  rw [Tm.denote_lst, snoc_empty]

/-- Nondependent arrows are constant-fibre dependent products. -/
theorem Tm.denote_arr (T : SetHierarchy.{u}) (ρ : String → ZFSet.{u})
    (A B : Tm 0) :
    (Tm.arr A B).denote T ρ Fin.elim0 =
      SetSem.pi (A.denote T ρ Fin.elim0) (fun _ => B.denote T ρ Fin.elim0) := by
  simp only [Tm.arr, Tm.denote]
  congr 1
  funext z
  exact Tm.denote_wk0 T ρ Fin.elim0 B z


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
theorem Tm.denote_wStepType (T : SetHierarchy.{u}) (ρ : String → ZFSet.{u})
    (A : Tm 0) (B C : Tm 1) :
    (Tm.wStepType A B C).denote T ρ Fin.elim0 =
      WSet.stepType (A.denote T ρ Fin.elim0)
        (fun a => B.denote T ρ (Fin.cons a Fin.elim0))
        (fun t => C.denote T ρ (Fin.cons t Fin.elim0)) := by
  simp only [Tm.wStepType, Tm.denote, Tm.denote_bsubst, Tm.denote_castLE_closed,
    Tm.denote_castLE, Fin.cons_zero, Fin.cons_one, cons_two, one_env, one_castLE_env, WSet.stepType]

private theorem denote_wkn1 (T : SetHierarchy.{u}) (ρ : String → ZFSet.{u})
    (t : Tm 1) (a b : ZFSet.{u}) :
    (t.wkn 1).denote T ρ (Fin.cons a (Fin.cons b Fin.elim0)) =
      t.denote T ρ (Fin.cons a Fin.elim0) := by
  rw [Tm.denote_wkn]
  apply congrArg (fun β => t.denote T ρ β)
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  cases hi
  rfl

/-- The object iota lambda denotes the graph of recursive calls on the child graph. -/
theorem Tm.denote_recChildren (T : SetHierarchy.{u}) (ρ : String → ZFSet.{u})
    (A : Tm 0) (B C : Tm 1) (s a f : Tm 0) :
    (Tm.recChildren A B C s a f).denote T ρ Fin.elim0 =
      SetSem.lam (B.denote T ρ (Fin.cons (a.denote T ρ Fin.elim0) Fin.elim0))
        (fun b => WSet.wrec (A.denote T ρ Fin.elim0)
          (fun a => B.denote T ρ (Fin.cons a Fin.elim0)) (s.denote T ρ Fin.elim0)
          (SetSem.app (f.denote T ρ Fin.elim0) b)) := by
  simp only [Tm.recChildren, Tm.denote, Tm.denote_lst0, Tm.denote_wk0,
    Fin.cons_zero, denote_wkn1]

end
end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

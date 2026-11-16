module

public import Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.ContextConversion.Thms

public section
namespace Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityLambdaCongruence
open Silmaril.Logic.TypeTheory.IntensionalMLTT
open Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality

/-- Weakening beneath a retained binder and then applying its fresh variable is identity. -/
theorem instantiate_fresh {n : ℕ} (t : Term (n + 1)) :
    (t.rename (Term.upRen Fin.succ)).instantiate (.var 0) = t := by
  change (t.rename (Term.upRen Fin.succ)).subst (Fin.cons (.var 0) Term.var) = t
  rw [Term.subst_rename]
  have he : (Fin.cons (.var 0) Term.var) ∘ Term.upRen Fin.succ =
      (Term.var : Fin (n + 1) → Term (n + 1)) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [he, Term.subst_var]

/-- Source beta and eta derive lambda congruence across convertible annotations. -/
theorem lambda_congr {k n : ℕ} {S : Context k} {Γ : Context n}
    {A A' : Term n} {B b b' : Term (n + 1)} {s : LFSort}
    (hAA' : Equality S Γ A A' (.univ 0))
    (hB : Equality S (Γ.snoc A) B B (.univ s.val))
    (hb : Equality S (Γ.snoc A) b b' B) :
    Equality S Γ (.lam A b) (.lam A' b') (.pi A B) := by
  have hA : Equality S Γ A A (.univ 0) := .trans hAA' (.symm hAA')
  have hA' : Equality S Γ A' A' (.univ 0) := .trans (.symm hAA') hAA'
  have hB' : Equality S (Γ.snoc A') B B (.univ s.val) := hB.convertLast hAA'
  have hb' : Equality S (Γ.snoc A') b' b' B :=
    (Equality.trans (Equality.symm hb) hb).convertLast hAA'
  have hPi : Equality S Γ (.pi A B) (.pi A' B) (.univ s.val) := .pi hAA' hB
  have hg : Equality S Γ (.lam A' b') (.lam A' b') (.pi A B) :=
    .conv (.lam hA' hB' hb') (.symm hPi)
  have hA'w : Equality S (Γ.snoc A) A'.weaken A'.weaken (.univ 0) := hA'.weaken hA
  have hΔ : ContextFormed S ((Γ.snoc A).snoc A'.weaken) :=
    .snoc (.snoc hA.context hA) hA'w
  have hBw : Equality S ((Γ.snoc A).snoc A'.weaken)
      (B.rename (Term.upRen Fin.succ)) (B.rename (Term.upRen Fin.succ)) (.univ s.val) :=
    hB'.rename hΔ (Term.upRen Fin.succ) (Renaming.lift (Renaming.weaken Γ A) A')
  have hbw : Equality S ((Γ.snoc A).snoc A'.weaken)
      (b'.rename (Term.upRen Fin.succ)) (b'.rename (Term.upRen Fin.succ))
      (B.rename (Term.upRen Fin.succ)) :=
    hb'.rename hΔ (Term.upRen Fin.succ) (Renaming.lift (Renaming.weaken Γ A) A')
  have hv : Equality S (Γ.snoc A) (.var 0) (.var 0) A'.weaken :=
    .conv (s := 0) (.var (.snoc hA.context hA) .here) (hAA'.weaken hA)
  have hbeta : Equality S (Γ.snoc A)
      (.app (Term.lam A' b').weaken (.var 0)) b' B := by
    simpa only [Term.weaken, Term.rename, instantiate_fresh] using
      Equality.beta hA'w hBw hbw hv
  have heta : Equality S Γ (.lam A (.app (Term.lam A' b').weaken (.var 0)))
      (.lam A' b') (.pi A B) := .eta hA hB hg
  exact .trans (.lam hA hB (.trans hb (.symm hbeta))) heta

end Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityLambdaCongruence

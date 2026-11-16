module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Terms.Defs

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms
open Silmaril.Logic.TypeTheory.ExtensionalMLTT

universe u

theorem bound_castLE {n m : ℕ} (h : n ≤ m) (t : Tm n) :
    (t.castLE h).universeBound = t.universeBound := by
  induction t generalizing m <;> simp_all [Tm.castLE, Tm.universeBound]

theorem bound_wkn {k : ℕ} (j : ℕ) (t : Tm k) :
    (t.wkn j).universeBound = t.universeBound := by
  induction t generalizing j <;> simp_all [Tm.wkn, Tm.universeBound]
  split <;> rfl

theorem liftSub_zero {n m : ℕ} {σ : Fin n → Tm m}
    (hσ : ∀ i, (σ i).universeBound = 0) :
    ∀ i, (Tm.liftSub σ i).universeBound = 0 := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · exact (bound_wkn 0 _).trans (hσ j)

theorem bound_bsubst_zero {n m : ℕ} (t : Tm n) (σ : Fin n → Tm m)
    (hσ : ∀ i, (σ i).universeBound = 0) :
    (t.bsubst σ).universeBound = t.universeBound := by
  induction t generalizing m <;>
    simp_all [Tm.bsubst, Tm.universeBound, liftSub_zero hσ]

theorem bound_bsubst_bv {n m : ℕ} (t : Tm n) (σ : Fin n → Fin m) :
    (t.bsubst (fun i => .bv (σ i))).universeBound = t.universeBound :=
  bound_bsubst_zero t _ (fun _ => rfl)

theorem positions_bound (S : Description) :
    S.positions.universeBound = S.position.universeBound := by
  apply bound_bsubst_zero
  intro i
  refine Fin.cases ?_ (fun _ => ?_) i <;> rfl

theorem next_bound (S : Description) :
    (S.next.bsubst (Fin.cases (.bv (0 : Fin 4))
      (Fin.cases (.snd (.bv 3)) (fun _ => .fst (.bv 3))))).universeBound =
      S.next.universeBound := by
  apply bound_bsubst_zero
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun _ => ?_) j <;> rfl

theorem raw_bound (S : Description) : S.raw.universeBound ≤ S.universeBound := by
  simp only [Description.raw, Description.totalShape, Tm.universeBound, positions_bound,
    Description.universeBound]
  omega

theorem rootStep_bound (S : Description) : S.rootStep.universeBound ≤ S.universeBound := by
  simp only [Description.rootStep, Description.childrenType, Tm.universeBound,
    bound_castLE, bound_bsubst_bv, positions_bound, Description.raw,
    Description.totalShape, Description.universeBound]
  omega

theorem root_bound {k : ℕ} (S : Description) (t : Tm k) :
    (S.root t).universeBound ≤ max S.universeBound t.universeBound := by
  have hs := rootStep_bound S
  have hr := raw_bound S
  simp only [Description.root, Tm.universeBound, bound_castLE,
    Description.totalShape, positions_bound]
  simp only [Description.raw, Description.totalShape, Tm.universeBound,
    positions_bound] at hr
  omega

theorem coherenceBody_bound (S : Description) :
    S.coherenceBody.universeBound ≤ S.universeBound := by
  have hr := root_bound S (.app (.bv (2 : Fin 4)) (.bv 0))
  simp only [Description.coherenceBody, Description.childIndexAt, Tm.universeBound, bound_bsubst_bv,
    bound_castLE, next_bound, positions_bound]
  simp only [Tm.universeBound, max_self, max_zero] at hr
  unfold Description.universeBound at *
  omega

theorem coherenceStep_bound (S : Description) (n : ℕ) :
    (S.coherenceStep n).universeBound ≤ max S.universeBound (n + 1) := by
  have hb := coherenceBody_bound S
  have hr := raw_bound S
  simp only [Description.coherenceStep, Description.childrenType, Description.totalShape,
    Tm.universeBound, bound_castLE, bound_bsubst_bv, positions_bound]
  unfold Description.universeBound at *
  omega

theorem coherence_bound {k : ℕ} (S : Description) (n : ℕ) (t : Tm k) :
    (S.coherence n t).universeBound ≤ max (max S.universeBound (n + 1)) t.universeBound := by
  have hs := coherenceStep_bound S n
  simp only [Description.coherence, Tm.universeBound, bound_castLE,
    Description.totalShape, positions_bound]
  unfold Description.universeBound at *
  omega

theorem fibre_bound (S : Description) (n : ℕ) (i : Tm 0) :
    (S.fibre n i).universeBound ≤ max (max S.universeBound (n + 1)) i.universeBound := by
  have hr := raw_bound S
  have hroot := root_bound S (.bv (0 : Fin 1))
  have hc := coherence_bound S n (.bv (1 : Fin 2))
  simp only [Description.fibre, Tm.universeBound, Tm.wk0, bound_wkn]
  simp only [Tm.universeBound, max_zero] at hroot hc
  unfold Description.universeBound at *
  omega

theorem positions_denoteIn (S : Description) (U : ℕ → ZFSet.{u})
    (ρ : String → ZFSet.{u}) (a : ZFSet.{u}) :
    S.positions.denoteIn U ρ (Fin.cons a Fin.elim0) =
      S.position.denoteIn U ρ
        (Fin.cons (SetSem.snd a) (Fin.cons (SetSem.fst a) Fin.elim0)) := by
  rw [Description.positions, Tm.denoteIn_bsubst]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · have hj : j = 0 := Subsingleton.elim _ _
    subst j
    rfl

theorem childIndexAt_denoteIn {k : ℕ} (S : Description) (U : ℕ → ZFSet.{u})
    (ρ : String → ZFSet.{u}) (β : Fin k → ZFSet.{u}) (label p : Tm k) :
    (S.childIndexAt label p).denoteIn U ρ β =
      S.next.denoteIn U ρ (Fin.cons (p.denoteIn U ρ β)
        (Fin.cons (SetSem.snd (label.denoteIn U ρ β))
          (Fin.cons (SetSem.fst (label.denoteIn U ρ β)) Fin.elim0))) := by
  rw [Description.childIndexAt, Tm.denoteIn_bsubst]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun k => ?_) j
    · rfl
    · have hk : k = 0 := Subsingleton.elim _ _
      subst k
      rfl

theorem positions_castLE_denoteIn {k : ℕ} (S : Description) (U : ℕ → ZFSet.{u})
    (ρ : String → ZFSet.{u}) (β : Fin k → ZFSet.{u}) (a : ZFSet.{u}) :
    (S.positions.castLE (Nat.succ_le_succ (Nat.zero_le k))).denoteIn U ρ (Fin.cons a β) =
      S.positions.denoteIn U ρ (Fin.cons a Fin.elim0) := by
  rw [Tm.denoteIn_castLE]
  congr 1
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rfl

theorem root_denoteIn {k : ℕ} (S : Description) (U : ℕ → ZFSet.{u})
    (ρ : String → ZFSet.{u}) (β : Fin k → ZFSet.{u}) (t : Tm k) :
    (S.root t).denoteIn U ρ β =
      WSet.wrec (S.totalShape.denoteIn U ρ Fin.elim0)
        (fun a => S.positions.denoteIn U ρ (Fin.cons a Fin.elim0))
        (S.rootStep.denoteIn U ρ Fin.elim0) (t.denoteIn U ρ β) := by
  simp only [Description.root, Tm.denoteIn, Tm.denoteIn_castLE_closed,
    positions_castLE_denoteIn]

theorem coherence_denoteIn {k : ℕ} (S : Description) (n : ℕ) (U : ℕ → ZFSet.{u})
    (ρ : String → ZFSet.{u}) (β : Fin k → ZFSet.{u}) (t : Tm k) :
    (S.coherence n t).denoteIn U ρ β =
      WSet.wrec (S.totalShape.denoteIn U ρ Fin.elim0)
        (fun a => S.positions.denoteIn U ρ (Fin.cons a Fin.elim0))
        ((S.coherenceStep n).denoteIn U ρ Fin.elim0) (t.denoteIn U ρ β) := by
  simp only [Description.coherence, Tm.denoteIn, Tm.denoteIn_castLE_closed,
    positions_castLE_denoteIn]

theorem fibre_denoteIn (S : Description) (n : ℕ) (U : ℕ → ZFSet.{u})
    (ρ : String → ZFSet.{u}) (i : Tm 0) :
    let labels := S.totalShape.denoteIn U ρ Fin.elim0
    let positions := fun a => S.positions.denoteIn U ρ (Fin.cons a Fin.elim0)
    let root := WSet.wrec labels positions (S.rootStep.denoteIn U ρ Fin.elim0)
    let coherent := WSet.wrec labels positions ((S.coherenceStep n).denoteIn U ρ Fin.elim0)
    (S.fibre n i).denoteIn U ρ Fin.elim0 =
      SetSem.sigma (S.raw.denoteIn U ρ Fin.elim0) (fun t =>
        SetSem.sigma (SetSem.truth (root t = i.denoteIn U ρ Fin.elim0))
          (fun _ => coherent t)) := by
  simp only [Description.fibre, Tm.denoteIn, root_denoteIn, coherence_denoteIn,
    Tm.denoteIn_wk0, Fin.cons_zero]
  rfl

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

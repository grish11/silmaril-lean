module

public import Silmaril.SSA.Isotope.Institution.Thms

public section

namespace Silmaril.Isotope.LetSeq.StraightLine.Binders

open LocallyNameless (Tm)

universe u v

variable {ν : Type u} {Φ : Type v}

theorem instantiate_bsubst_up_proof {n m : Nat} (σ : Fin n → Tm ν Φ m) (k : Tm ν Φ (n + 1)) (v : Tm ν Φ m) :
    Tm.instantiate (k.bsubst (Tm.upSub σ)) v = k.bsubst (Fin.cases v σ) := by
  rw [Tm.instantiate, Tm.bsubst_comp]
  apply Tm.bsubst_congr
  intro i
  refine Fin.cases rfl (fun j => ?_) i
  simp only [Fin.cases_succ, Tm.upSub_succ, Tm.lift, Tm.bsubst_rename]
  exact Tm.bsubst_id _

theorem instantiate_renamed_proof {n m : Nat} (k : Tm ν Φ (n + 1)) (v : Tm ν Φ m)
    (ρ : Fin n → Fin m) :
    Tm.instantiate (k.rename (Tm.up ρ)) v = k.bsubst (Fin.cases v (fun i => .bv (ρ i))) := by
  rw [Tm.instantiate, Tm.bsubst_rename]
  exact Tm.bsubst_congr (Fin.cases rfl (fun _ => rfl)) k

theorem open_left_pair_proof {n m : Nat} (b : Tm ν Φ n) (v : Tm ν Φ m) (ρ : Fin n → Fin m) :
    Tm.instantiate ((Tm.let₁ b.lift (.pair (.bv 1) (.bv 0))).rename (Tm.up ρ)) v =
      .let₁ (b.rename ρ) (.pair v.lift (.bv 0)) := by
  rw [instantiate_renamed_proof]
  simp only [Tm.bsubst, Tm.lift, Tm.bsubst_rename]
  rw [← Tm.bsubst_bv_eq_rename]
  rfl

theorem open_right_pair_proof {n m : Nat} (a : Tm ν Φ n) (v : Tm ν Φ m) (ρ : Fin n → Fin m) :
    Tm.instantiate ((Tm.pair a.lift (.bv 0)).rename (Tm.up ρ)) v = .pair (a.rename ρ) v := by
  rw [instantiate_renamed_proof]
  simp only [Tm.bsubst, Tm.lift, Tm.bsubst_rename]
  rw [← Tm.bsubst_bv_eq_rename]
  rfl

theorem rename_open_substitution_proof {n m k : Nat} (σ : Fin n → Tm ν Φ m) (ρ : Fin m → Fin k)
    (body : Tm ν Φ (n + 1)) :
    (body.bsubst (Tm.upSub σ)).rename (Tm.up ρ) =
      body.bsubst (Tm.upSub (fun i => (σ i).rename ρ)) := by
  rw [Tm.rename_bsubst]
  apply Tm.bsubst_congr
  exact Fin.cases rfl (fun j => Tm.rename_lift ρ (σ j))

theorem open_pack_continuation_proof {n m : Nat} (body : Tm ν Φ (n + 2)) (v : Tm ν Φ m)
    (ρ : Fin n → Fin m) :
    Tm.instantiate ((Tm.let₂ (.bv 0) body.underTwoBinders).rename (Tm.up ρ)) v =
      .let₂ v (body.rename (Tm.up (Tm.up ρ))) := by
  rw [instantiate_renamed_proof]
  simp only [Tm.bsubst, Fin.cases_zero, Tm.underTwoBinders, Tm.bsubst_rename]
  congr 1
  rw [← Tm.bsubst_bv_eq_rename]
  exact Tm.bsubst_congr (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))) body

end Silmaril.Isotope.LetSeq.StraightLine.Binders

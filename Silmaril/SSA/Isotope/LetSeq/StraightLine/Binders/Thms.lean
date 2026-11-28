module

public import Silmaril.SSA.Isotope.Institution.Thms
import Silmaril.Proofs.SSA.Isotope.LetSeq.StraightLine.Binders.Core

/-! # Native LetSeq binder transport for straight-line normalization -/

public section

namespace Silmaril.Isotope.LetSeq.StraightLine.Binders

open LocallyNameless (Tm)

universe u v

variable {ν : Type u} {Φ : Type v}

theorem instantiate_bsubst_up {n m : Nat} (σ : Fin n → Tm ν Φ m) (k : Tm ν Φ (n + 1)) (v : Tm ν Φ m) :
    Tm.instantiate (k.bsubst (Tm.upSub σ)) v = k.bsubst (Fin.cases v σ) :=
  Binders.instantiate_bsubst_up_proof σ k v

theorem instantiate_renamed {n m : Nat} (k : Tm ν Φ (n + 1)) (v : Tm ν Φ m)
    (ρ : Fin n → Fin m) :
    Tm.instantiate (k.rename (Tm.up ρ)) v = k.bsubst (Fin.cases v (fun i => .bv (ρ i))) :=
  Binders.instantiate_renamed_proof k v ρ

theorem open_left_pair {n m : Nat} (b : Tm ν Φ n) (v : Tm ν Φ m) (ρ : Fin n → Fin m) :
    Tm.instantiate ((Tm.let₁ b.lift (.pair (.bv 1) (.bv 0))).rename (Tm.up ρ)) v =
      .let₁ (b.rename ρ) (.pair v.lift (.bv 0)) :=
  Binders.open_left_pair_proof b v ρ

theorem open_right_pair {n m : Nat} (a : Tm ν Φ n) (v : Tm ν Φ m) (ρ : Fin n → Fin m) :
    Tm.instantiate ((Tm.pair a.lift (.bv 0)).rename (Tm.up ρ)) v = .pair (a.rename ρ) v :=
  Binders.open_right_pair_proof a v ρ

theorem rename_open_substitution {n m k : Nat} (σ : Fin n → Tm ν Φ m) (ρ : Fin m → Fin k)
    (body : Tm ν Φ (n + 1)) :
    (body.bsubst (Tm.upSub σ)).rename (Tm.up ρ) =
      body.bsubst (Tm.upSub (fun i => (σ i).rename ρ)) :=
  Binders.rename_open_substitution_proof σ ρ body

theorem open_pack_continuation {n m : Nat} (body : Tm ν Φ (n + 2)) (v : Tm ν Φ m)
    (ρ : Fin n → Fin m) :
    Tm.instantiate ((Tm.let₂ (.bv 0) body.underTwoBinders).rename (Tm.up ρ)) v =
      .let₂ v (body.rename (Tm.up (Tm.up ρ))) :=
  Binders.open_pack_continuation_proof body v ρ

end Silmaril.Isotope.LetSeq.StraightLine.Binders

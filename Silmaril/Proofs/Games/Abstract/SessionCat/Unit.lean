module

public import Silmaril.Proofs.Games.Abstract.SessionCat.Det
public import Silmaril.Proofs.Games.Abstract.SessionCat.Id
public import Silmaril.Games.DivComp.Thms

/-!
# Session-level category laws: unit laws (proofs)

`idS` has deterministic returns and no plain traps, so linking with it is composition with its
session (`comp_threadS`), which is copycat (`threadS_idS`), a unit of composition
(`DStrategy.id_comp`, `DStrategy.comp_id`).
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.SessionCat

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratThread Silmaril.Games.Abstract.StratSession
  Silmaril.Games.Abstract.SessionLink Silmaril.Games.Abstract.SessionCat

universe u

variable {E : Sig.{u}} {S A B A' B' : Type u}

theorem retDet_idS : RetDet (idS (A := A) (B := B)) := by
  rintro s a c c' b b' s₁ s₁' ⟨y, hy⟩ ⟨y', hy'⟩
  simp only [Prod.mk.injEq, End.ret.injEq] at hy hy'
  obtain ⟨rfl, rfl, -⟩ := hy
  obtain ⟨rfl, rfl, -⟩ := hy'
  exact ⟨rfl, fun h => by cases h; rfl⟩

theorem noPlainTrap_idS : NoPlainTrap (idS (A := A) (B := B)) := by
  rintro s a c ⟨y, hy⟩
  cases (Prod.ext_iff.1 hy).2

theorem threadS_linkS_idS {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})} (hnt : NoPlainTrap t)
    (ht : RetDet t) (s : S) : threadS (linkS t idS) (s, PUnit.unit) = threadS t s := by
  rw [← comp_threadS hnt (storeDet_of_retDet ht) (storeDet_of_retDet (retDet_linkS ht retDet_idS)),
    threadS_idS, DStrategy.comp_id]

theorem threadS_idS_linkS {u : ObsTriple (sig1 A B) S A' (B' ⊕ PUnit.{u + 1})} (hu : RetDet u)
    (s : S) : threadS (linkS idS u) (PUnit.unit, s) = threadS u s := by
  rw [← comp_threadS noPlainTrap_idS (storeDet_of_retDet retDet_idS)
      (storeDet_of_retDet (retDet_linkS retDet_idS hu)), threadS_idS, DStrategy.id_comp]

theorem obsEq_linkS_idS {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})} (hnt : NoPlainTrap t)
    (ht : RetDet t) (s : S) : ObsEq (linkS t idS) t (s, PUnit.unit) s :=
  (threadS_eq_iff (storeDet_of_retDet (retDet_linkS ht retDet_idS)) (storeDet_of_retDet ht)
    (noPlainTrap_linkS noPlainTrap_idS) hnt).1 (threadS_linkS_idS hnt ht s)

theorem obsEq_idS_linkS {u : ObsTriple (sig1 A B) S A' (B' ⊕ PUnit.{u + 1})}
    (hnu : NoPlainTrap u) (hu : RetDet u) (s : S) : ObsEq (linkS idS u) u (PUnit.unit, s) s :=
  (threadS_eq_iff (storeDet_of_retDet (retDet_linkS retDet_idS hu)) (storeDet_of_retDet hu)
    (noPlainTrap_linkS hnu) hnu).1 (threadS_idS_linkS hu s)

end Silmaril.Proofs.Games.Abstract.SessionCat

module

public import Silmaril.Proofs.Games.Abstract.StratOps.Game
import Silmaril.Games.Abstract.FullFun.Thms

/-!
# Copairing and the fixpoint law for triples and play objects (proofs)

* `iterT_unfold`: `iterT t = seqT t (caseT pureT (iterT t))`. The full part is
  `FullFun.iter_unfold`; a pending call after a finite continuing chain is a pending call of the
  first iteration (empty chain) or one after a first continuing iteration and a shorter chain;
* `sat_caseT`, `admissible_caseT`: saturation is computed argument by argument, so it commutes
  with copairing;
* `seqD_caseD`, `iterD_unfold`: the triple laws on the image of `toDStrat`, with no hypothesis,
  because every operation involved preserves admissibility and `toDStrat (sat t) = toDStrat t`.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.StratOps

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratOps

universe u

variable {E : Sig.{u}} {S A B C D : Type u}

/-- **The fixpoint law for triples**, pending calls. -/
theorem iterT_unfold_pending (t : ObsTriple E S A (B ⊕ A)) :
    (iterT t).2.1 = (seqT t (caseT pureT (iterT t))).2.1 := by
  funext s a
  ext ⟨c, m⟩
  constructor
  · rintro ⟨c₀, s', a', c', m', hc, hp, he⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    cases hc with
    | refl => exact .inl hp
    | step hm hc =>
      exact .inr ⟨_, .inr _, _, _ ++ c', m, hm, ⟨_, _, _, c', m, hc, hp, rfl⟩,
        by rw [List.append_assoc]⟩
  · rintro (hp | ⟨c₁, b | a₁, s₁, c₂, m', hm, hp, he⟩)
    · exact ⟨[], s, a, c, m, .refl, hp, rfl⟩
    · exact hp.elim
    · obtain ⟨c₀, s', a', c', m'', hc, hp', he'⟩ := hp
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he'
      exact ⟨c₁ ++ c₀, s', a', c', m, .step hm hc, hp', by rw [List.append_assoc]⟩

/-- **The fixpoint law for triples.** -/
theorem iterT_unfold (t : ObsTriple E S A (B ⊕ A)) :
    iterT t = seqT t (caseT pureT (iterT t)) :=
  ext_full (FullFun.iter_unfold (full t)) (iterT_unfold_pending t)

/-- Saturation commutes with copairing. -/
theorem sat_caseT (t : ObsTriple E S A C) (u : ObsTriple E S B C) :
    sat (caseT t u) = caseT (sat t) (sat u) :=
  ext_full rfl (funext fun _ => funext fun x => by cases x <;> rfl)

theorem admissible_caseT {t : ObsTriple E S A C} {u : ObsTriple E S B C} (ht : Admissible t)
    (hu : Admissible u) : Admissible (caseT t u) :=
  (sat_caseT t u).trans (by rw [show sat t = t from ht, show sat u = u from hu])

theorem caseD_adm {t : ObsTriple E S A C} {u : ObsTriple E S B C} (ht : Admissible t)
    (hu : Admissible u) : caseD (toDStrat t) (toDStrat u) = toDStrat (caseT t u) := by
  rw [caseD, readback_toDStrat_adm ht, readback_toDStrat_adm hu]

/-- Sequencing of play objects distributes over copairing on the left. -/
theorem seqD_caseD (t : ObsTriple E S A C) (u : ObsTriple E S B C) (v : ObsTriple E S C D) :
    seqD (caseD (toDStrat t) (toDStrat u)) (toDStrat v) =
      caseD (seqD (toDStrat t) (toDStrat v)) (seqD (toDStrat u) (toDStrat v)) := by
  have ht := admissible_sat (t := t)
  have hu := admissible_sat (t := u)
  have hv := admissible_sat (t := v)
  rw [← toDStrat_sat (t := t), ← toDStrat_sat (t := u), ← toDStrat_sat (t := v),
    caseD_adm ht hu, seqD_adm (admissible_caseT ht hu) hv, seqD_adm ht hv, seqD_adm hu hv,
    caseD_adm (saturated_seqT ht hv) (saturated_seqT hu hv)]
  congr 1
  exact ext_full (FullFun.seq_case _ _ _) (funext fun _ => funext fun x => by cases x <;> rfl)

/-- **The fixpoint law for play objects.** -/
theorem iterD_unfold (t : ObsTriple E S A (B ⊕ A)) :
    iterD (toDStrat t) = seqD (toDStrat t) (caseD pureD (iterD (toDStrat t))) := by
  have ht := admissible_sat (t := t)
  rw [← toDStrat_sat (t := t), iterD, readback_toDStrat_adm ht, pureD,
    caseD_adm saturated_pureT (saturated_iterT ht),
    seqD_adm ht (admissible_caseT saturated_pureT (saturated_iterT ht)), ← iterT_unfold]

end Silmaril.Proofs.Games.Abstract.StratOps

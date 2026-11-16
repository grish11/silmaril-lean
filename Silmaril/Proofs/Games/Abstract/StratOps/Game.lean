module

public import Silmaril.Proofs.Games.Abstract.StratOps.Iter

/-!
# Game-level operations through readback (proofs)

`readback_toDStrat`: reading back a play object gives the saturation of its triple, from the
readback lemmas `StratObs.mem_ret`, `mem_trap`, `mem_div`, `mem_pending` and `mem_inf`. The
game-level laws then follow from the triple laws, because every operation preserves
admissibility and `toDStrat` is injective on admissible triples.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.StratOps

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratOps

universe u

variable {E : Sig.{u}} {S A B C D : Type u}

theorem readback_toDStrat (t : ObsTriple E S A B) : readback (toDStrat t) = sat t := by
  refine Prod.ext (funext fun s => funext fun a => ?_)
    (Prod.ext (funext fun s => funext fun a => ?_) (funext fun s => funext fun a => ?_))
  · ext ⟨c, e⟩
    cases e with
    | ret b s' => exact mem_ret s a c b s'
    | trap => exact mem_trap s a c
    | div => exact mem_div (s, a) c
  · ext ⟨c, m⟩
    exact mem_pending (s, a) c m
  · ext ω
    exact mem_inf (s, a) ω

/-- On admissible triples, readback inverts `toDStrat`. -/
theorem readback_toDStrat_adm {t : ObsTriple E S A B} (ht : Admissible t) :
    readback (toDStrat t) = t :=
  (readback_toDStrat t).trans ht

/-! ## Admissibility of the operations -/

theorem admissible_mapT {t : ObsTriple E S A B} (ht : Admissible t) (h : B → C) :
    Admissible (mapT t h) :=
  (sat_mapT t h).trans (congrArg (mapT · h) ht)

theorem admissible_comapT {A' : Type u} {t : ObsTriple E S A B} (ht : Admissible t)
    (k : A' → A) : Admissible (comapT t k) :=
  (sat_comapT t k).trans (congrArg (comapT · k) ht)

theorem admissible_whiskerRightT {t : ObsTriple E S A B} (ht : Admissible t) (C : Type u) :
    Admissible (whiskerRightT t C) :=
  (sat_whiskerRightT t C).trans (congrArg (whiskerRightT · C) ht)

theorem admissible_whiskerLeftT {t : ObsTriple E S A B} (ht : Admissible t) (C : Type u) :
    Admissible (whiskerLeftT C t) :=
  (sat_whiskerLeftT C t).trans (congrArg (whiskerLeftT C ·) ht)

/-! ## The game-level operations on admissible triples -/

section Adm

variable {t : ObsTriple E S A B} {u : ObsTriple E S B C}

theorem seqD_adm (ht : Admissible t) (hu : Admissible u) :
    seqD (toDStrat t) (toDStrat u) = toDStrat (seqT t u) := by
  rw [seqD, readback_toDStrat_adm ht, readback_toDStrat_adm hu]

theorem mapD_adm (ht : Admissible t) (h : B → C) : mapD (toDStrat t) h = toDStrat (mapT t h) := by
  rw [mapD, readback_toDStrat_adm ht]

theorem comapD_adm {A' : Type u} (ht : Admissible t) (k : A' → A) :
    comapD (toDStrat t) k = toDStrat (comapT t k) := by
  rw [comapD, readback_toDStrat_adm ht]

theorem whiskerRightD_adm (ht : Admissible t) (C : Type u) :
    whiskerRightD (toDStrat t) C = toDStrat (whiskerRightT t C) := by
  rw [whiskerRightD, readback_toDStrat_adm ht]

theorem whiskerLeftD_adm (ht : Admissible t) (C : Type u) :
    whiskerLeftD C (toDStrat t) = toDStrat (whiskerLeftT C t) := by
  rw [whiskerLeftD, readback_toDStrat_adm ht]

end Adm

/-! ## Laws on the image of `toDStrat` -/

section Laws

variable (t : ObsTriple E S A B)

theorem seqD_assoc (u : ObsTriple E S B C) (v : ObsTriple E S C D) :
    seqD (seqD (toDStrat t) (toDStrat u)) (toDStrat v) =
      seqD (toDStrat t) (seqD (toDStrat u) (toDStrat v)) := by
  have ht := admissible_sat (t := t)
  have hu := admissible_sat (t := u)
  have hv := admissible_sat (t := v)
  rw [← toDStrat_sat (t := t), ← toDStrat_sat (t := u), ← toDStrat_sat (t := v), seqD_adm ht hu,
    seqD_adm (saturated_seqT ht hu) hv, seqD_adm hu hv, seqD_adm ht (saturated_seqT hu hv),
    seqT_assoc]

theorem seqD_pureD : seqD (toDStrat t) pureD = toDStrat t := by
  rw [← toDStrat_sat (t := t), pureD, seqD_adm admissible_sat saturated_pureT, seqT_pureT]

theorem pureD_seqD : seqD pureD (toDStrat t) = toDStrat t := by
  rw [← toDStrat_sat (t := t), pureD, seqD_adm saturated_pureT admissible_sat, pureT_seqT]

theorem mapD_id : mapD (toDStrat t) id = toDStrat t := by
  rw [← toDStrat_sat (t := t), mapD_adm admissible_sat, mapT_id]

theorem mapD_mapD (h : B → C) (h' : C → D) :
    mapD (mapD (toDStrat t) h) h' = mapD (toDStrat t) (h' ∘ h) := by
  rw [← toDStrat_sat (t := t), mapD_adm admissible_sat,
    mapD_adm (admissible_mapT admissible_sat h), mapD_adm admissible_sat, mapT_mapT]

theorem comapD_id : comapD (toDStrat t) id = toDStrat t := by
  rw [← toDStrat_sat (t := t), comapD_adm admissible_sat]
  rfl

theorem comapD_comapD {A' A'' : Type u} (k : A' → A) (k' : A'' → A') :
    comapD (comapD (toDStrat t) k) k' = comapD (toDStrat t) (k ∘ k') := by
  rw [← toDStrat_sat (t := t), comapD_adm admissible_sat,
    comapD_adm (admissible_comapT admissible_sat k), comapD_adm admissible_sat]
  rfl

theorem mapD_comapD {A' : Type u} (k : A' → A) (h : B → C) :
    mapD (comapD (toDStrat t) k) h = comapD (mapD (toDStrat t) h) k := by
  rw [← toDStrat_sat (t := t), comapD_adm admissible_sat,
    mapD_adm (admissible_comapT admissible_sat k), mapD_adm admissible_sat,
    comapD_adm (admissible_mapT admissible_sat h)]
  rfl

theorem seqD_pureD_mapD (h : B → C) :
    seqD (toDStrat t) (mapD pureD h) = mapD (toDStrat t) h := by
  rw [← toDStrat_sat (t := t), pureD, mapD_adm saturated_pureT,
    seqD_adm admissible_sat (admissible_mapT saturated_pureT h), seqT_pureT_mapT,
    mapD_adm admissible_sat]

theorem pureD_mapD_seqD (h : A → B) (u : ObsTriple E S B C) :
    seqD (mapD pureD h) (toDStrat u) = comapD (toDStrat u) h := by
  rw [← toDStrat_sat (t := u), pureD, mapD_adm saturated_pureT,
    seqD_adm (admissible_mapT saturated_pureT h) admissible_sat, pureT_mapT_seqT,
    comapD_adm admissible_sat]

theorem seqD_mapD (h : B → C) (u : ObsTriple E S C D) :
    seqD (mapD (toDStrat t) h) (toDStrat u) = seqD (toDStrat t) (comapD (toDStrat u) h) := by
  rw [← toDStrat_sat (t := t), ← toDStrat_sat (t := u), mapD_adm admissible_sat,
    seqD_adm (admissible_mapT admissible_sat h) admissible_sat, comapD_adm admissible_sat,
    seqD_adm admissible_sat (admissible_comapT admissible_sat h), seqT_mapT]

theorem mapD_seqD (u : ObsTriple E S B C) (h : C → D) :
    mapD (seqD (toDStrat t) (toDStrat u)) h = seqD (toDStrat t) (mapD (toDStrat u) h) := by
  rw [← toDStrat_sat (t := t), ← toDStrat_sat (t := u), seqD_adm admissible_sat admissible_sat,
    mapD_adm (saturated_seqT admissible_sat admissible_sat), mapD_adm admissible_sat,
    seqD_adm admissible_sat (admissible_mapT admissible_sat h), mapT_seqT]

theorem comapD_seqD {A' : Type u} (u : ObsTriple E S B C) (k : A' → A) :
    comapD (seqD (toDStrat t) (toDStrat u)) k = seqD (comapD (toDStrat t) k) (toDStrat u) := by
  rw [← toDStrat_sat (t := t), ← toDStrat_sat (t := u), seqD_adm admissible_sat admissible_sat,
    comapD_adm (saturated_seqT admissible_sat admissible_sat), comapD_adm admissible_sat,
    seqD_adm (admissible_comapT admissible_sat k) admissible_sat]
  rfl

theorem whiskerRightD_pureD : whiskerRightD (pureD : DStrategy E (funSig S A A)) C = pureD := by
  rw [pureD, whiskerRightD_adm saturated_pureT, whiskerRightT_pureT]; rfl

theorem whiskerLeftD_pureD : whiskerLeftD C (pureD : DStrategy E (funSig S A A)) = pureD := by
  rw [pureD, whiskerLeftD_adm saturated_pureT, whiskerLeftT_pureT]; rfl

theorem whiskerRightD_seqD (u : ObsTriple E S B D) (C : Type u) :
    whiskerRightD (seqD (toDStrat t) (toDStrat u)) C =
      seqD (whiskerRightD (toDStrat t) C) (whiskerRightD (toDStrat u) C) := by
  rw [← toDStrat_sat (t := t), ← toDStrat_sat (t := u), seqD_adm admissible_sat admissible_sat,
    whiskerRightD_adm (saturated_seqT admissible_sat admissible_sat),
    whiskerRightD_adm admissible_sat, whiskerRightD_adm admissible_sat,
    seqD_adm (admissible_whiskerRightT admissible_sat C)
      (admissible_whiskerRightT admissible_sat C), whiskerRightT_seqT]

theorem whiskerLeftD_seqD (u : ObsTriple E S B D) (C : Type u) :
    whiskerLeftD C (seqD (toDStrat t) (toDStrat u)) =
      seqD (whiskerLeftD C (toDStrat t)) (whiskerLeftD C (toDStrat u)) := by
  rw [← toDStrat_sat (t := t), ← toDStrat_sat (t := u), seqD_adm admissible_sat admissible_sat,
    whiskerLeftD_adm (saturated_seqT admissible_sat admissible_sat),
    whiskerLeftD_adm admissible_sat, whiskerLeftD_adm admissible_sat,
    seqD_adm (admissible_whiskerLeftT admissible_sat C)
      (admissible_whiskerLeftT admissible_sat C), whiskerLeftT_seqT]

end Laws

theorem not_interchangeD :
    ∃ (E : Sig.{0}) (t u : ObsTriple E PUnit PUnit PUnit),
      seqD (whiskerRightD (toDStrat t) PUnit) (whiskerLeftD PUnit (toDStrat u)) ≠
        seqD (whiskerLeftD PUnit (toDStrat u)) (whiskerRightD (toDStrat t) PUnit) := by
  obtain ⟨E, f, g, hne⟩ := FullFun.not_interchange
  refine ⟨E, ofFull f fun _ _ => ∅, ofFull g fun _ _ => ∅, fun he => hne ?_⟩
  rw [← toDStrat_sat (t := ofFull f _), ← toDStrat_sat (t := ofFull g _),
    whiskerRightD_adm admissible_sat, whiskerLeftD_adm admissible_sat,
    seqD_adm (admissible_whiskerRightT admissible_sat _) (admissible_whiskerLeftT admissible_sat _),
    seqD_adm (admissible_whiskerLeftT admissible_sat _) (admissible_whiskerRightT admissible_sat _)]
    at he
  exact congrArg full (toDStrat_injective
    (saturated_seqT (admissible_whiskerRightT admissible_sat _)
      (admissible_whiskerLeftT admissible_sat _))
    (saturated_seqT (admissible_whiskerLeftT admissible_sat _)
      (admissible_whiskerRightT admissible_sat _)) he)

end Silmaril.Proofs.Games.Abstract.StratOps

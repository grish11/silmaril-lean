module

public import Silmaril.Games.Abstract.StratOps.Defs
public import Silmaril.Games.Abstract.FullFun.Thms
public import Silmaril.Games.Abstract.StratObs.Thms
import Silmaril.Proofs.Games.Abstract.StratOps.Game
import Silmaril.Proofs.Games.Abstract.StratOps.Unfold
import Silmaril.Proofs.Games.Abstract.StratOps.Natural

/-!
# Premonoidal operations on observation triples: theorems

**The full parts are the `FullFun` operations** (`full_seqT`, `full_pureT`, `full_mapT`,
`full_comapT`, `full_whiskerRightT`, `full_whiskerLeftT`, `full_iterT`), by `rfl`. A triple is
determined by its full part and its pending calls (`ext_full`).

**Laws** (proofs in `Silmaril.Proofs.Games.Abstract.StratOps.Laws`; the full parts are the
`FullFun` laws, the proofs handle the pending calls):

* `seqT_assoc`, `seqT_pureT`, `pureT_seqT`: a category (associativity and units);
* `mapT_id`, `mapT_mapT`, `comapT_id`, `comapT_comapT`, `mapT_comapT`: functoriality of pure
  post- and pre-composition;
* `seqT_pureT_mapT`, `pureT_mapT_seqT`, `seqT_mapT`, `mapT_seqT`, `comapT_seqT`: pure maps and
  sequencing;
* `whiskerRightT_pureT`, `whiskerRightT_seqT`, `whiskerLeftT_pureT`, `whiskerLeftT_seqT`:
  whiskering is functorial;
* `not_interchangeT`: **the interchange law fails**, so triples are premonoidal and not
  monoidal (transported from `FullFun.not_interchange`).

**Copairing and the fixpoint law** (`Silmaril.Proofs.Games.Abstract.StratOps.Unfold`):

* `full_caseT`, `comapT_inl_caseT`, `comapT_inr_caseT`, `pureT_mapT_inl_seqT_caseT`,
  `pureT_mapT_inr_seqT_caseT`, `caseT_pureT_mapT`, `seqT_caseT`: copairing after an injection
  is the corresponding component, the copairing of the injections is the identity, and
  sequencing distributes over copairing on the left;
* `iterT_unfold` (**the fixpoint law**): `iterT t = seqT t (caseT pureT (iterT t))`, with no
  hypothesis on `t`. The full part is `FullFun.iter_unfold`; the pending calls after a finite
  continuing chain are those of the first iteration or those after a first continuing
  iteration and a shorter chain.

**Naturality and uniformity of iteration** (`Silmaril.Proofs.Games.Abstract.StratOps.Natural`;
the full parts are `FullFun.iter_map` and `FullFun.iter_uniform_comap`):

* `iterT_mapT` (**naturality in the output**): `iterT (mapT t (Sum.map h id)) = mapT (iterT t) h`;
* `caseT_pureT_mapT_mapT`: the copairing of pure maps is a pure map;
* `iterT_uniform_comap`, `iterT_uniform` (**uniformity** for a pure map `h`): if
  `h ; F = G ; [inl, inr ∘ h]` then `h ; iterT F = iterT G`. No hypothesis on `F`, `G` beyond
  this equation: divergence, infinite silent chains, productive runs and pending calls are
  all included.

**Saturation** (`Silmaril.Proofs.Games.Abstract.StratOps.Sat`, `….Iter`):

* `sat_mapT`, `sat_comapT`, `sat_whiskerRightT`, `sat_whiskerLeftT`: pure maps and whiskering
  commute with saturation, with no hypothesis;
* `sat_seqT_sat_right`: saturating the second argument of a sequence changes nothing;
* `sat_seqT` (`u` total) and `sat_seqT_of_adm` (`t` admissible):
  `sat (seqT (sat t) (sat u)) = sat (seqT t u)`. **It fails in general** (`not_sat_seqT`): a
  call prefix of a return of `t` is a call of `sat t`, but `seqT t u` loses it when `u` has no
  observation after that return;
* `sat_iterT_of_adm`: the same for iteration of an admissible body (immediate). For a
  non-admissible body the same loss as for sequencing can occur (a continuing iteration into a
  state with no observation); no totality version is proved for iteration;
* `sat_caseT`: copairing commutes with saturation, with no hypothesis;
* `admissible_pureT`, `admissible_seqT`, `admissible_mapT`, `admissible_comapT`,
  `admissible_whiskerRightT`, `admissible_whiskerLeftT`, `admissible_caseT`,
  `admissible_iterT`: **every operation preserves admissibility**, with no further
  hypothesis.

**Readback and the game-level operations** (`Silmaril.Proofs.Games.Abstract.StratOps.Game`):

* `readback_toDStrat : readback (toDStrat t) = sat t`, from the `StratObs` readback lemmas;
* `seqD_toDStrat` and the other `…D_toDStrat`: on play objects, a game-level operation is the
  triple operation on the saturations;
* preservation `toDStrat (seqT t u) = seqD (toDStrat t) (toDStrat u)` under the hypotheses of
  `sat_seqT` (`toDStrat_seqT`, `toDStrat_seqT_of_adm`), failing in general
  (`not_toDStrat_seqT`); for `pureT`, `mapT`, `comapT` and whiskering with no hypothesis; for
  `iterT` for an admissible body (`toDStrat_iterT_of_adm`); for `caseT` with no hypothesis
  (`toDStrat_caseT`);
* the laws on the image of `toDStrat`, with no hypothesis (every operation preserves
  admissibility): `seqD_assoc`, `seqD_pureD`, `pureD_seqD`, the map laws, the whiskering laws,
  `seqD_caseD`, **the fixpoint law** `iterD_unfold`
  (`iterD σ = seqD σ (caseD pureD (iterD σ))` for `σ = toDStrat t`, any `t`), and
  `not_interchangeD` (premonoidal, not monoidal).

The game-level operations are defined through readback, not by a direct interaction
construction on strategies; none is claimed.
-/

public section

namespace Silmaril.Games.Abstract.StratOps

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs

universe u

variable {E : Sig.{u}} {S A B C D : Type u}

/-! ## Components -/

/-- A triple is its full part with its pending calls. -/
theorem ofFull_full (t : ObsTriple E S A B) : ofFull (full t) t.2.1 = t := rfl

/-- Triples with the same full part and pending calls are equal. -/
theorem ext_full {t t' : ObsTriple E S A B} (hf : full t = full t') (hp : t.2.1 = t'.2.1) :
    t = t' :=
  (ofFull_full t).symm.trans (hf ▸ hp ▸ ofFull_full t')

theorem full_seqT (t : ObsTriple E S A B) (u : ObsTriple E S B C) :
    full (seqT t u) = FullFun.seq (full t) (full u) := rfl

theorem full_pureT : full (pureT : ObsTriple E S A A) = FullFun.pure := rfl

theorem full_mapT (t : ObsTriple E S A B) (h : B → C) : full (mapT t h) = (full t).map h := rfl

theorem full_comapT {A' : Type u} (t : ObsTriple E S A B) (k : A' → A) :
    full (comapT t k) = (full t).comap k := rfl

theorem full_whiskerRightT (t : ObsTriple E S A B) (C : Type u) :
    full (whiskerRightT t C) = (full t).whiskerRight C := rfl

theorem full_whiskerLeftT (C : Type u) (t : ObsTriple E S A B) :
    full (whiskerLeftT C t) = (full t).whiskerLeft C := rfl

theorem full_iterT (t : ObsTriple E S A (B ⊕ A)) : full (iterT t) = FullFun.iter (full t) := rfl

/-! ## Laws -/

/-- **Associativity of sequencing.** -/
theorem seqT_assoc (t : ObsTriple E S A B) (u : ObsTriple E S B C) (v : ObsTriple E S C D) :
    seqT (seqT t u) v = seqT t (seqT u v) :=
  Silmaril.Proofs.Games.Abstract.StratOps.seqT_assoc t u v

/-- The identity is a right unit. -/
theorem seqT_pureT (t : ObsTriple E S A B) : seqT t pureT = t :=
  Silmaril.Proofs.Games.Abstract.StratOps.seqT_pureT t

/-- The identity is a left unit. -/
theorem pureT_seqT (u : ObsTriple E S A B) : seqT pureT u = u :=
  Silmaril.Proofs.Games.Abstract.StratOps.pureT_seqT u

theorem mapT_id (t : ObsTriple E S A B) : mapT t id = t :=
  Silmaril.Proofs.Games.Abstract.StratOps.mapT_id t

theorem mapT_mapT (t : ObsTriple E S A B) (h : B → C) (h' : C → D) :
    mapT (mapT t h) h' = mapT t (h' ∘ h) :=
  Silmaril.Proofs.Games.Abstract.StratOps.mapT_mapT t h h'

theorem comapT_id (t : ObsTriple E S A B) : comapT t id = t := rfl

theorem comapT_comapT {A' A'' : Type u} (t : ObsTriple E S A B) (k : A' → A) (k' : A'' → A') :
    comapT (comapT t k) k' = comapT t (k ∘ k') := rfl

theorem mapT_comapT {A' : Type u} (t : ObsTriple E S A B) (k : A' → A) (h : B → C) :
    mapT (comapT t k) h = comapT (mapT t h) k := rfl

/-- Sequencing with a pure map is that map. -/
theorem seqT_pureT_mapT (t : ObsTriple E S A B) (h : B → C) :
    seqT t (mapT pureT h) = mapT t h :=
  Silmaril.Proofs.Games.Abstract.StratOps.seqT_pureT_mapT t h

/-- Sequencing after a pure map is pre-composition. -/
theorem pureT_mapT_seqT (h : A → B) (u : ObsTriple E S B C) :
    seqT (mapT pureT h) u = comapT u h :=
  Silmaril.Proofs.Games.Abstract.StratOps.pureT_mapT_seqT h u

/-- A pure map can be moved across sequencing. -/
theorem seqT_mapT (t : ObsTriple E S A B) (h : B → C) (u : ObsTriple E S C D) :
    seqT (mapT t h) u = seqT t (comapT u h) :=
  Silmaril.Proofs.Games.Abstract.StratOps.seqT_mapT t h u

/-- A pure map after a sequence is a pure map after its second part. -/
theorem mapT_seqT (t : ObsTriple E S A B) (u : ObsTriple E S B C) (h : C → D) :
    mapT (seqT t u) h = seqT t (mapT u h) :=
  Silmaril.Proofs.Games.Abstract.StratOps.mapT_seqT t u h

/-- Pre-composition of a sequence is pre-composition of its first part. -/
theorem comapT_seqT {A' : Type u} (t : ObsTriple E S A B) (u : ObsTriple E S B C) (k : A' → A) :
    comapT (seqT t u) k = seqT (comapT t k) u := rfl

theorem whiskerRightT_pureT : whiskerRightT (pureT : ObsTriple E S A A) C = pureT :=
  Silmaril.Proofs.Games.Abstract.StratOps.whiskerRightT_pureT

theorem whiskerLeftT_pureT : whiskerLeftT C (pureT : ObsTriple E S A A) = pureT :=
  Silmaril.Proofs.Games.Abstract.StratOps.whiskerLeftT_pureT

/-- **Right whiskering preserves sequencing.** -/
theorem whiskerRightT_seqT (t : ObsTriple E S A B) (u : ObsTriple E S B D) (C : Type u) :
    whiskerRightT (seqT t u) C = seqT (whiskerRightT t C) (whiskerRightT u C) :=
  Silmaril.Proofs.Games.Abstract.StratOps.whiskerRightT_seqT t u C

/-- **Left whiskering preserves sequencing.** -/
theorem whiskerLeftT_seqT (t : ObsTriple E S A B) (u : ObsTriple E S B D) (C : Type u) :
    whiskerLeftT C (seqT t u) = seqT (whiskerLeftT C t) (whiskerLeftT C u) :=
  Silmaril.Proofs.Games.Abstract.StratOps.whiskerLeftT_seqT t u C

/-- **The interchange law fails for triples**: premonoidal, not monoidal. -/
theorem not_interchangeT :
    ∃ (E : Sig.{0}) (t u : ObsTriple E PUnit PUnit PUnit),
      seqT (whiskerRightT t PUnit) (whiskerLeftT PUnit u) ≠
        seqT (whiskerLeftT PUnit u) (whiskerRightT t PUnit) :=
  Silmaril.Proofs.Games.Abstract.StratOps.not_interchangeT

/-! ## Copairing and the fixpoint law -/

theorem full_caseT (t : ObsTriple E S A C) (u : ObsTriple E S B C) :
    full (caseT t u) = FullFun.case (full t) (full u) := rfl

theorem comapT_inl_caseT (t : ObsTriple E S A C) (u : ObsTriple E S B C) :
    comapT (caseT t u) Sum.inl = t := rfl

theorem comapT_inr_caseT (t : ObsTriple E S A C) (u : ObsTriple E S B C) :
    comapT (caseT t u) Sum.inr = u := rfl

/-- Copairing after the left injection is the left component. -/
theorem pureT_mapT_inl_seqT_caseT (t : ObsTriple E S A C) (u : ObsTriple E S B C) :
    seqT (mapT pureT Sum.inl) (caseT t u) = t :=
  pureT_mapT_seqT Sum.inl _

/-- Copairing after the right injection is the right component. -/
theorem pureT_mapT_inr_seqT_caseT (t : ObsTriple E S A C) (u : ObsTriple E S B C) :
    seqT (mapT pureT Sum.inr) (caseT t u) = u :=
  pureT_mapT_seqT Sum.inr _

/-- The copairing of the injections is the identity. -/
theorem caseT_pureT_mapT :
    caseT (mapT pureT Sum.inl) (mapT pureT Sum.inr) = (pureT : ObsTriple E S (A ⊕ B) (A ⊕ B)) :=
  ext_full FullFun.case_pure_map (funext fun _ => funext fun x => by cases x <;> rfl)

/-- Sequencing distributes over copairing on the left. -/
theorem seqT_caseT (t : ObsTriple E S A C) (u : ObsTriple E S B C) (v : ObsTriple E S C D) :
    seqT (caseT t u) v = caseT (seqT t v) (seqT u v) :=
  ext_full (FullFun.seq_case _ _ _) (funext fun _ => funext fun x => by cases x <;> rfl)

/-- **The fixpoint law**: one iteration, then exit (`inl`) or iterate again (`inr`); finished
behaviours, productive runs and pending calls. -/
theorem iterT_unfold (t : ObsTriple E S A (B ⊕ A)) : iterT t = seqT t (caseT pureT (iterT t)) :=
  Silmaril.Proofs.Games.Abstract.StratOps.iterT_unfold t

/-- **Naturality of iteration in the output.** -/
theorem iterT_mapT (t : ObsTriple E S A (B ⊕ A)) (h : B → C) :
    iterT (mapT t (Sum.map h id)) = mapT (iterT t) h :=
  Silmaril.Proofs.Games.Abstract.StratOps.iterT_mapT t h

/-- The copairing of pure maps is a pure map. -/
theorem caseT_pureT_mapT_mapT {X : Type u} (h₁ : A → X) (h₂ : B → X) :
    caseT (mapT (pureT : ObsTriple E S A A) h₁) (mapT pureT h₂) = mapT pureT (Sum.elim h₁ h₂) :=
  Silmaril.Proofs.Games.Abstract.StratOps.caseT_pureT_mapT_mapT h₁ h₂

/-- **Uniformity of iteration** with respect to a pure map `k`, pre-composition form. -/
theorem iterT_uniform_comap {A' : Type u} {F : ObsTriple E S A (B ⊕ A)}
    {G : ObsTriple E S A' (B ⊕ A')} {k : A' → A} (hFG : comapT F k = mapT G (Sum.map id k)) :
    comapT (iterT F) k = iterT G :=
  Silmaril.Proofs.Games.Abstract.StratOps.iterT_uniform_comap hFG

/-- **Uniformity of iteration** (Elgot form) for a pure map `h`: if `h ; F = G ; [inl, inr ∘ h]`
then `h ; iterT F = iterT G`. -/
theorem iterT_uniform {A' : Type u} {F : ObsTriple E S A (B ⊕ A)}
    {G : ObsTriple E S A' (B ⊕ A')} (h : A' → A)
    (hFG : seqT (mapT pureT h) F =
      seqT G (caseT (mapT pureT Sum.inl) (mapT pureT (Sum.inr ∘ h)))) :
    seqT (mapT pureT h) (iterT F) = iterT G :=
  Silmaril.Proofs.Games.Abstract.StratOps.iterT_uniform h hFG

/-! ## Saturation and admissibility -/

section Sat

variable {t : ObsTriple E S A B} {u : ObsTriple E S B C}

/-- Saturation keeps a triple total. -/
theorem total_sat (hu : Total u) : Total (sat u) :=
  Silmaril.Proofs.Games.Abstract.StratOps.total_sat hu

/-- Saturating the second argument of a sequence does not change its saturation. -/
theorem sat_seqT_sat_right : sat (seqT t (sat u)) = sat (seqT t u) :=
  Silmaril.Proofs.Games.Abstract.StratOps.sat_eq rfl
    Silmaril.Proofs.Games.Abstract.StratOps.satP_seqT_sat_right rfl

/-- **Sequencing commutes with saturation** when the second argument is total. -/
theorem sat_seqT (hu : Total u) : sat (seqT (sat t) (sat u)) = sat (seqT t u) :=
  Silmaril.Proofs.Games.Abstract.StratOps.sat_seqT hu

/-- **Sequencing commutes with saturation** when the first argument is admissible. -/
theorem sat_seqT_of_adm (ht : Admissible t) : sat (seqT (sat t) (sat u)) = sat (seqT t u) :=
  Silmaril.Proofs.Games.Abstract.StratOps.sat_seqT_of_adm ht

/-- **Without a hypothesis the equation fails**: a call prefix of a return of `t` is a pending
call of `sat t`, but if `u` has no observation after that return, `seqT t u` loses it. -/
theorem not_sat_seqT :
    ∃ (E : Sig.{0}) (t u : ObsTriple E PUnit PUnit PUnit),
      sat (seqT (sat t) (sat u)) ≠ sat (seqT t u) :=
  Silmaril.Proofs.Games.Abstract.StratOps.not_sat_seqT

theorem sat_mapT (t : ObsTriple E S A B) (h : B → C) : sat (mapT t h) = mapT (sat t) h :=
  Silmaril.Proofs.Games.Abstract.StratOps.sat_mapT t h

theorem sat_comapT {A' : Type u} (t : ObsTriple E S A B) (k : A' → A) :
    sat (comapT t k) = comapT (sat t) k := rfl

theorem sat_whiskerRightT (t : ObsTriple E S A B) (C : Type u) :
    sat (whiskerRightT t C) = whiskerRightT (sat t) C :=
  Silmaril.Proofs.Games.Abstract.StratOps.sat_whiskerRightT t C

theorem sat_whiskerLeftT (C : Type u) (t : ObsTriple E S A B) :
    sat (whiskerLeftT C t) = whiskerLeftT C (sat t) :=
  Silmaril.Proofs.Games.Abstract.StratOps.sat_whiskerLeftT C t

/-- Iteration commutes with saturation when the body is admissible. -/
theorem sat_iterT_of_adm {t : ObsTriple E S A (B ⊕ A)} (ht : Admissible t) :
    sat (iterT (sat t)) = sat (iterT t) := by
  rw [show sat t = t from ht]

/-- Copairing commutes with saturation. -/
theorem sat_caseT (t : ObsTriple E S A C) (u : ObsTriple E S B C) :
    sat (caseT t u) = caseT (sat t) (sat u) :=
  Silmaril.Proofs.Games.Abstract.StratOps.sat_caseT t u

theorem admissible_caseT {t : ObsTriple E S A C} {u : ObsTriple E S B C} (ht : Admissible t)
    (hu : Admissible u) : Admissible (caseT t u) :=
  Silmaril.Proofs.Games.Abstract.StratOps.admissible_caseT ht hu

theorem admissible_pureT : Admissible (pureT : ObsTriple E S A A) :=
  Silmaril.Proofs.Games.Abstract.StratOps.saturated_pureT

/-- **Sequencing preserves admissibility.** -/
theorem admissible_seqT (ht : Admissible t) (hu : Admissible u) : Admissible (seqT t u) :=
  Silmaril.Proofs.Games.Abstract.StratOps.saturated_seqT ht hu

theorem admissible_mapT (ht : Admissible t) (h : B → C) : Admissible (mapT t h) :=
  Silmaril.Proofs.Games.Abstract.StratOps.admissible_mapT ht h

theorem admissible_comapT {A' : Type u} (ht : Admissible t) (k : A' → A) :
    Admissible (comapT t k) :=
  Silmaril.Proofs.Games.Abstract.StratOps.admissible_comapT ht k

theorem admissible_whiskerRightT (ht : Admissible t) (C : Type u) :
    Admissible (whiskerRightT t C) :=
  Silmaril.Proofs.Games.Abstract.StratOps.admissible_whiskerRightT ht C

theorem admissible_whiskerLeftT (ht : Admissible t) (C : Type u) :
    Admissible (whiskerLeftT C t) :=
  Silmaril.Proofs.Games.Abstract.StratOps.admissible_whiskerLeftT ht C

/-- **Iteration preserves admissibility.** -/
theorem admissible_iterT {t : ObsTriple E S A (B ⊕ A)} (ht : Admissible t) :
    Admissible (iterT t) :=
  Silmaril.Proofs.Games.Abstract.StratOps.saturated_iterT ht

end Sat

/-! ## Readback -/

/-- **Reading back a play object gives the saturation of its triple.** -/
theorem readback_toDStrat (t : ObsTriple E S A B) : readback (toDStrat t) = sat t :=
  Silmaril.Proofs.Games.Abstract.StratOps.readback_toDStrat t

/-- On admissible triples, readback inverts `toDStrat`. -/
theorem readback_toDStrat_adm {t : ObsTriple E S A B} (ht : Admissible t) :
    readback (toDStrat t) = t :=
  (readback_toDStrat t).trans ht

/-! ## The game-level operations on the image of `toDStrat`

The operations are defined through readback (`seqD` and the others); on play objects they are
the triple operations on saturations. -/

section Game

variable {t : ObsTriple E S A B} {u : ObsTriple E S B C}

theorem seqD_toDStrat : seqD (toDStrat t) (toDStrat u) = toDStrat (seqT (sat t) (sat u)) := by
  rw [seqD, readback_toDStrat, readback_toDStrat]

theorem pureD_eq : (pureD : DStrategy E (funSig S A A)) = toDStrat pureT := rfl

theorem mapD_toDStrat (h : B → C) : mapD (toDStrat t) h = toDStrat (mapT (sat t) h) := by
  rw [mapD, readback_toDStrat]

theorem comapD_toDStrat {A' : Type u} (k : A' → A) :
    comapD (toDStrat t) k = toDStrat (comapT (sat t) k) := by
  rw [comapD, readback_toDStrat]

theorem whiskerRightD_toDStrat (C : Type u) :
    whiskerRightD (toDStrat t) C = toDStrat (whiskerRightT (sat t) C) := by
  rw [whiskerRightD, readback_toDStrat]

theorem whiskerLeftD_toDStrat (C : Type u) :
    whiskerLeftD C (toDStrat t) = toDStrat (whiskerLeftT C (sat t)) := by
  rw [whiskerLeftD, readback_toDStrat]

theorem iterD_toDStrat {t : ObsTriple E S A (B ⊕ A)} :
    iterD (toDStrat t) = toDStrat (iterT (sat t)) := by
  rw [iterD, readback_toDStrat]

theorem caseD_toDStrat {t : ObsTriple E S A C} {u : ObsTriple E S B C} :
    caseD (toDStrat t) (toDStrat u) = toDStrat (caseT (sat t) (sat u)) := by
  rw [caseD, readback_toDStrat, readback_toDStrat]

/-! ### Preservation -/

/-- **`toDStrat` preserves sequencing** when the second argument is total. -/
theorem toDStrat_seqT (hu : Total u) : toDStrat (seqT t u) = seqD (toDStrat t) (toDStrat u) := by
  rw [seqD_toDStrat]; exact toDStrat_eq_iff.2 (sat_seqT hu).symm

/-- **`toDStrat` preserves sequencing** when the first argument is admissible. -/
theorem toDStrat_seqT_of_adm (ht : Admissible t) :
    toDStrat (seqT t u) = seqD (toDStrat t) (toDStrat u) := by
  rw [seqD_toDStrat]; exact toDStrat_eq_iff.2 (sat_seqT_of_adm ht).symm

/-- **Preservation of sequencing fails in general.** -/
theorem not_toDStrat_seqT :
    ∃ (E : Sig.{0}) (t u : ObsTriple E PUnit PUnit PUnit),
      toDStrat (seqT t u) ≠ seqD (toDStrat t) (toDStrat u) := by
  obtain ⟨E, t, u, h⟩ := not_sat_seqT
  exact ⟨E, t, u, fun he => h (toDStrat_eq_iff.1 (he.trans seqD_toDStrat).symm)⟩

theorem toDStrat_pureT : toDStrat (pureT : ObsTriple E S A A) = pureD := rfl

theorem toDStrat_mapT (h : B → C) : toDStrat (mapT t h) = mapD (toDStrat t) h := by
  rw [mapD_toDStrat]; exact toDStrat_eq_iff.2 (by rw [sat_mapT, sat_mapT, sat_idem])

theorem toDStrat_comapT {A' : Type u} (k : A' → A) :
    toDStrat (comapT t k) = comapD (toDStrat t) k := by
  rw [comapD_toDStrat]; exact toDStrat_eq_iff.2 (by rw [sat_comapT, sat_comapT, sat_idem])

theorem toDStrat_whiskerRightT (C : Type u) :
    toDStrat (whiskerRightT t C) = whiskerRightD (toDStrat t) C := by
  rw [whiskerRightD_toDStrat]
  exact toDStrat_eq_iff.2 (by rw [sat_whiskerRightT, sat_whiskerRightT, sat_idem])

theorem toDStrat_whiskerLeftT (C : Type u) :
    toDStrat (whiskerLeftT C t) = whiskerLeftD C (toDStrat t) := by
  rw [whiskerLeftD_toDStrat]
  exact toDStrat_eq_iff.2 (by rw [sat_whiskerLeftT, sat_whiskerLeftT, sat_idem])

/-- `toDStrat` preserves copairing. -/
theorem toDStrat_caseT {t : ObsTriple E S A C} {u : ObsTriple E S B C} :
    toDStrat (caseT t u) = caseD (toDStrat t) (toDStrat u) := by
  rw [caseD_toDStrat, ← sat_caseT, toDStrat_sat]

/-- `toDStrat` preserves iteration when the body is admissible. -/
theorem toDStrat_iterT_of_adm {t : ObsTriple E S A (B ⊕ A)} (ht : Admissible t) :
    toDStrat (iterT t) = iterD (toDStrat t) := by
  rw [iterD, readback_toDStrat_adm ht]

end Game

/-! ### Laws on the image of `toDStrat` -/

section GameLaws

variable (t : ObsTriple E S A B)

/-- **Associativity of game-level sequencing** on play objects. -/
theorem seqD_assoc (u : ObsTriple E S B C) (v : ObsTriple E S C D) :
    seqD (seqD (toDStrat t) (toDStrat u)) (toDStrat v) =
      seqD (toDStrat t) (seqD (toDStrat u) (toDStrat v)) :=
  Silmaril.Proofs.Games.Abstract.StratOps.seqD_assoc t u v

theorem seqD_pureD : seqD (toDStrat t) pureD = toDStrat t :=
  Silmaril.Proofs.Games.Abstract.StratOps.seqD_pureD t

theorem pureD_seqD : seqD pureD (toDStrat t) = toDStrat t :=
  Silmaril.Proofs.Games.Abstract.StratOps.pureD_seqD t

theorem mapD_id : mapD (toDStrat t) id = toDStrat t :=
  Silmaril.Proofs.Games.Abstract.StratOps.mapD_id t

theorem mapD_mapD (h : B → C) (h' : C → D) :
    mapD (mapD (toDStrat t) h) h' = mapD (toDStrat t) (h' ∘ h) :=
  Silmaril.Proofs.Games.Abstract.StratOps.mapD_mapD t h h'

theorem comapD_id : comapD (toDStrat t) id = toDStrat t :=
  Silmaril.Proofs.Games.Abstract.StratOps.comapD_id t

theorem comapD_comapD {A' A'' : Type u} (k : A' → A) (k' : A'' → A') :
    comapD (comapD (toDStrat t) k) k' = comapD (toDStrat t) (k ∘ k') :=
  Silmaril.Proofs.Games.Abstract.StratOps.comapD_comapD t k k'

theorem mapD_comapD {A' : Type u} (k : A' → A) (h : B → C) :
    mapD (comapD (toDStrat t) k) h = comapD (mapD (toDStrat t) h) k :=
  Silmaril.Proofs.Games.Abstract.StratOps.mapD_comapD t k h

theorem seqD_pureD_mapD (h : B → C) :
    seqD (toDStrat t) (mapD pureD h) = mapD (toDStrat t) h :=
  Silmaril.Proofs.Games.Abstract.StratOps.seqD_pureD_mapD t h

theorem pureD_mapD_seqD (h : A → B) (u : ObsTriple E S B C) :
    seqD (mapD pureD h) (toDStrat u) = comapD (toDStrat u) h :=
  Silmaril.Proofs.Games.Abstract.StratOps.pureD_mapD_seqD h u

theorem seqD_mapD (h : B → C) (u : ObsTriple E S C D) :
    seqD (mapD (toDStrat t) h) (toDStrat u) = seqD (toDStrat t) (comapD (toDStrat u) h) :=
  Silmaril.Proofs.Games.Abstract.StratOps.seqD_mapD t h u

theorem mapD_seqD (u : ObsTriple E S B C) (h : C → D) :
    mapD (seqD (toDStrat t) (toDStrat u)) h = seqD (toDStrat t) (mapD (toDStrat u) h) :=
  Silmaril.Proofs.Games.Abstract.StratOps.mapD_seqD t u h

theorem comapD_seqD {A' : Type u} (u : ObsTriple E S B C) (k : A' → A) :
    comapD (seqD (toDStrat t) (toDStrat u)) k = seqD (comapD (toDStrat t) k) (toDStrat u) :=
  Silmaril.Proofs.Games.Abstract.StratOps.comapD_seqD t u k

theorem whiskerRightD_pureD : whiskerRightD (pureD : DStrategy E (funSig S A A)) C = pureD :=
  Silmaril.Proofs.Games.Abstract.StratOps.whiskerRightD_pureD

theorem whiskerLeftD_pureD : whiskerLeftD C (pureD : DStrategy E (funSig S A A)) = pureD :=
  Silmaril.Proofs.Games.Abstract.StratOps.whiskerLeftD_pureD

/-- **Right whiskering preserves game-level sequencing** on play objects. -/
theorem whiskerRightD_seqD (u : ObsTriple E S B D) (C : Type u) :
    whiskerRightD (seqD (toDStrat t) (toDStrat u)) C =
      seqD (whiskerRightD (toDStrat t) C) (whiskerRightD (toDStrat u) C) :=
  Silmaril.Proofs.Games.Abstract.StratOps.whiskerRightD_seqD t u C

/-- **Left whiskering preserves game-level sequencing** on play objects. -/
theorem whiskerLeftD_seqD (u : ObsTriple E S B D) (C : Type u) :
    whiskerLeftD C (seqD (toDStrat t) (toDStrat u)) =
      seqD (whiskerLeftD C (toDStrat t)) (whiskerLeftD C (toDStrat u)) :=
  Silmaril.Proofs.Games.Abstract.StratOps.whiskerLeftD_seqD t u C

/-- Game-level sequencing distributes over copairing on the left, on play objects. -/
theorem seqD_caseD {C' : Type u} (u : ObsTriple E S C' B) (v : ObsTriple E S B D) :
    seqD (caseD (toDStrat t) (toDStrat u)) (toDStrat v) =
      caseD (seqD (toDStrat t) (toDStrat v)) (seqD (toDStrat u) (toDStrat v)) :=
  Silmaril.Proofs.Games.Abstract.StratOps.seqD_caseD t u v

end GameLaws

/-- **The fixpoint law for play objects**: on the image of `toDStrat`, with no hypothesis. -/
theorem iterD_unfold (t : ObsTriple E S A (B ⊕ A)) :
    iterD (toDStrat t) = seqD (toDStrat t) (caseD pureD (iterD (toDStrat t))) :=
  Silmaril.Proofs.Games.Abstract.StratOps.iterD_unfold t


/-- **The interchange law fails for play objects**: the game-level structure is premonoidal,
not monoidal. -/
theorem not_interchangeD :
    ∃ (E : Sig.{0}) (t u : ObsTriple E PUnit PUnit PUnit),
      seqD (whiskerRightD (toDStrat t) PUnit) (whiskerLeftD PUnit (toDStrat u)) ≠
        seqD (whiskerLeftD PUnit (toDStrat u)) (whiskerRightD (toDStrat t) PUnit) :=
  Silmaril.Proofs.Games.Abstract.StratOps.not_interchangeD

end Silmaril.Games.Abstract.StratOps

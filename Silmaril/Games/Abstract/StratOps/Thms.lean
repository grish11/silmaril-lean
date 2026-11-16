module

public import Silmaril.Games.Abstract.StratOps.Defs
public import Silmaril.Games.Abstract.FullFun.Thms
import Silmaril.Proofs.Games.Abstract.StratOps.Laws

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

`AFun.iter` and `FullFun.iter` have no Elgot fixpoint or unfolding law in the library, so none
is stated for `iterT`.
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

end Silmaril.Games.Abstract.StratOps
